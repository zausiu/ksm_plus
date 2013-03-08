/*
 * Memory merging support.
 *
 * This code enables dynamic sharing of identical pages found in different
 * memory areas, even if they are not shared by fork()
 *
 * Copyright (C) 2008-2009 Red Hat, Inc.
 * Authors:
 *	Izik Eidus
 *	Andrea Arcangeli
 *	Chris Wright
 *	Hugh Dickins
 *
 * Copyright (C) 2013 Sun Yat-sen Unv.
 * Author:
 *      zhouxiao / cryincold@qq.com
 *
 * This work is licensed under the terms of the GNU GPL, version 2.
 */

#include <linux/errno.h>
#include <linux/mm.h>
#include <linux/fs.h>
#include <linux/mman.h>
#include <linux/sched.h>
#include <linux/rwsem.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include <linux/spinlock.h>
#include <linux/jhash.h>
#include <linux/delay.h>
#include <linux/kthread.h>
#include <linux/wait.h>
#include <linux/slab.h>
#include <linux/rbtree.h>
#include <linux/memory.h>
#include <linux/mmu_notifier.h>
#include <linux/swap.h>
#include <linux/ksm.h>
#include <linux/hash.h>
#include <linux/freezer.h>
#include <linux/oom.h>
#include <linux/random.h>
#include <crypto/hash.h>
#include <asm/tlbflush.h>
//#include "mm/internal.h"

#define output(msg, args...) do {                   \
	printk(KERN_DEBUG"sksm [%s]"msg, __func__, ##args); \
}while(0)

// pre-declarations.
struct rmap_item;
struct vma_node;
static int task_ksm_enter(struct task_struct *task);
static void vma_node_do_sampling(struct vma_node *vma_node);
static int print_page_content(struct page *page);

/**
 * @sample_coefficient this value specifies how to take sample from the
 *	vm_area, 0 denotes no actions will be taken. n denote a page has
 *	the odd of n/256 to be sampled.
 * @samples link to the samples. The highest significant 16 bits of a sample
 * 	address is used as the checksum. The lowest significant 16 bits is
 *      used as the page index.
 */
struct vma_node {
	struct rb_node node;
	struct vm_area_struct *vma;
	unsigned long start;
	unsigned long end;
	struct rmap_item *rmap_list;
	struct rmap_item *rmap_current;
	//u32 *samples;
	//unsigned int sample_len;
//	u8 sample_coefficient;    
	u8 coefficient;
};


/**
 * struct mm_slot - ksm information per mm that is being scanned
 * @link: link to the mm_slots hash list
 * @mm_list: link into the mm_slots list, rooted in sksm_mm_head
 * @rmap_list: head for this mm_slot's singly-linked list of rmap_items
 * @mm: the mm that this information is valid for
 */
//struct mm_slot {
//	struct hlist_node link;
//	struct list_head mm_list;
//	struct rmap_item *rmap_list;
//	struct mm_struct *mm;
//};
/**
 * Compared with the original version of mm_slot.rmap_list's been removed which
 * is replaced by a link to the a struct encapsulating the info of the vm_area_struct.
 */
struct mm_slot {
	struct hlist_node link;
	struct list_head mm_list;
	struct mm_struct *mm;
	union {
		struct {
			struct rb_root vma_root;  // the new-added field.
			struct vma_node *curr;
		};
		struct {
			struct rmap_item *rmap_list;
			unsigned long address;
		};
	};
};

/**
 * struct sksm_scan - cursor for scanning
 * @mm_slot: the current mm_slot we are scanning
 * @address: the next address inside that to be scanned
 * @rmap_list: link to the next rmap to be scanned in the rmap_list
 * @seqnr: count of completed full scans (needed when removing unstable node)
 *
 * There is only the one sksm_scan instance of this cursor structure.
 */
struct sksm_scan {
	struct mm_slot *mm_slot;
	//struct vma_node *vma_node;
	//struct rmap_item **rmap_list;
	unsigned long seqnr;
};

/**
 * struct stable_node - node of the stable rbtree
 * @node: rb node of this ksm page in the stable tree
 * @hlist: hlist head of rmap_items using this ksm page
 * @kpfn: page frame number of this ksm page
 * @md5sum: md5 hash code of the page frame.
 */
struct stable_node {
	struct rb_node node;
	struct hlist_head hlist;
	unsigned long kpfn;
	//u8 md5sum[16];
};

/* i think it doesn't worth creating a unstable node. */
/*
struct unstable_node {
	struct rb_node node;
	struct rmap_item *rmap_item;
	u8 md5sum[16];
}*/

/**
 * struct rmap_item - reverse mapping item for virtual addresses
 * @rmap_list: next rmap_item in vma_node's singly-linked rmap_list
 * @anon_vma: pointer to anon_vma for this mm,address, when in stable tree
 * @mm: the memory structure this rmap_item is pointing into
 * @address: the virtual address this rmap_item tracks (+ flags in low bits)
 * @node: rb node of this rmap_item in the unstable tree
 * @head: pointer to stable_node heading this list in the stable tree
 * @hlist: link into hlist of rmap_items hanging off that stable_node
 */
struct rmap_item {
	struct rmap_item *rmap_list;
	struct mm_struct *mm;
	unsigned long address;		/* + low bits used for flags below */
	union {
		struct {
			u16 oldchecksum;
			struct rb_node node;  /* when node of unstable tree */
		};
		struct {		/* when listed from stable tree */
			struct stable_node *head;
			struct hlist_node hlist;
			struct anon_vma *anon_vma;	/* when stable */
		};
	};
};

#define SEQNR_MASK	0x07f	/* low bits of unstable tree seqnr */
#define UNSTABLE_FLAG	0x100	/* is a node of the unstable tree */
#define STABLE_FLAG	0x200	/* is listed from the stable tree */
#define INVALID_FLAG    0x080   /* is an invalid address */

/* The stable and unstable tree heads */
static struct rb_root root_stable_tree = RB_ROOT;
static struct rb_root root_unstable_tree = RB_ROOT;

#define MM_SLOTS_HASH_SHIFT 10
#define MM_SLOTS_HASH_HEADS (1 << MM_SLOTS_HASH_SHIFT)
static struct hlist_head mm_slots_hash[MM_SLOTS_HASH_HEADS];

// data structures for processes_to_scan.
static DEFINE_SPINLOCK(processes_to_scan_lock);
LIST_HEAD(processes_to_scan_head);
struct process_to_scan
{
	char* comm;
	struct list_head list;
};

//////////////////////////////////////////////
// The following code implements a simple stack.
////////////////////////////////////////////////////////
struct stack_brick
{
	void *data;
	struct stack_brick *prev;
};

struct tiny_stack
{
	struct stack_brick *top; 
	int size;
};

static inline void init_tiny_stack(struct tiny_stack *stack)
{
	stack->top = NULL;
	stack->size = 0;
}

static void push_tiny_stack(struct tiny_stack *stack, void *ptr)
{
	struct stack_brick *brick = kmalloc(sizeof(struct tiny_stack), GFP_KERNEL);
	brick->data = ptr;
	brick->prev = stack->top;
	stack->top = brick;
	stack->size++;
}

static void *pop_tiny_stack(struct tiny_stack *stack)
{
	void *ptr = stack->top->data;
	struct stack_brick *trash = stack->top;
	BUG_ON(0 == stack->size);
	stack->top = stack->top->prev;
	stack->size--;
	kfree(trash);
	return ptr;
}

static inline int tiny_stack_size(struct tiny_stack *stack)
{
	return stack->size;
}
// end of the implementation of the tiny_stack.
//////////////////////////////////////////////////////////////////////////////


static struct mm_slot sksm_mm_head = {
	.mm_list = LIST_HEAD_INIT(sksm_mm_head.mm_list),
};
static struct sksm_scan sksm_scan = {
	.mm_slot = &sksm_mm_head,
};

static struct kmem_cache *rmap_item_cache;
static struct kmem_cache *stable_node_cache;
static struct kmem_cache *mm_slot_cache;
static struct kmem_cache *vma_node_cache;
static struct kmem_cache *processes_to_scan_cache;

/* The number of nodes in the stable tree */
static unsigned long ksm_pages_shared;

/* The number of page slots additionally sharing those nodes */
static unsigned long ksm_pages_sharing;

/* The number of nodes in the unstable tree */
static unsigned long ksm_pages_unshared;

/* The number of rmap_items in use: to calculate pages_volatile */
static unsigned long ksm_rmap_items;

/* Number of pages ksmd should scan in one batch */
static unsigned int ksm_thread_pages_to_scan = 200;

/* number of processes ksmd should scan to recruit new vm_area_structs. */
static unsigned int ksm_thread_processes_to_recruit = 4;

/* Milliseconds ksmd should sleep between batches */
static unsigned int sksm_thread_sleep_millisecs = 1500;

#define SKSM_RUN_STOP	        0
#define SKSM_RUN_MERGE	        1
#define SKSM_RUN_UNMERGE	2
#define SKSM_RUN_F0PAGES_ONLY    3
//static unsigned int sksm_run = SKSM_RUN_STOP;
//static unsigned int sksm_run = SKSM_RUN_MERGE;
static unsigned int sksm_run = SKSM_RUN_F0PAGES_ONLY;

static DECLARE_WAIT_QUEUE_HEAD(sksm_thread_wait);
static DEFINE_MUTEX(sksm_thread_mutex);
static DEFINE_SPINLOCK(sksm_mmlist_lock);

#define SKSM_KMEM_CACHE(__struct, __flags) kmem_cache_create("sksm_"#__struct,\
		sizeof(struct __struct), __alignof__(struct __struct),\
		(__flags), NULL)

static int __init sksm_slab_init(void)
{
	rmap_item_cache = SKSM_KMEM_CACHE(rmap_item, 0);
	if (!rmap_item_cache)
		goto out;

	stable_node_cache = SKSM_KMEM_CACHE(stable_node, 0);
	if (!stable_node_cache)
		goto out_free1;

	mm_slot_cache = SKSM_KMEM_CACHE(mm_slot, 0);
	if (!mm_slot_cache)
		goto out_free2;
	
	vma_node_cache = SKSM_KMEM_CACHE(vma_node, 0);
	if (!vma_node_cache)
		goto out_free3;

	processes_to_scan_cache = SKSM_KMEM_CACHE(process_to_scan, 0);
	if (!processes_to_scan_cache)
		goto out_free4;

	return 0;

out_free4:
	kmem_cache_destroy(vma_node_cache);
out_free3:
	kmem_cache_destroy(mm_slot_cache);
out_free2:
	kmem_cache_destroy(stable_node_cache);
out_free1:
	kmem_cache_destroy(rmap_item_cache);
out:
	return -ENOMEM;
}

static void sksm_slab_free(void)
{
	if (vma_node_cache)
		 kmem_cache_destroy(vma_node_cache);

	if (mm_slot_cache)
		kmem_cache_destroy(mm_slot_cache);

	if (stable_node_cache)
		kmem_cache_destroy(stable_node_cache);

	if (rmap_item_cache)
		kmem_cache_destroy(rmap_item_cache);

	if (processes_to_scan_cache)
		kmem_cache_destroy(processes_to_scan_cache);
}

static inline struct rmap_item *alloc_rmap_item(void)
{
	struct rmap_item *rmap_item;

	rmap_item = kmem_cache_zalloc(rmap_item_cache, GFP_KERNEL);
	if (rmap_item)
		ksm_rmap_items++;
	return rmap_item;
}

static inline void free_rmap_item(struct rmap_item *rmap_item)
{
	ksm_rmap_items--;
	rmap_item->mm = NULL;	/* debug safety */
	rmap_item->address = 0xdddddd; /*my poison, for debug.*/
	kmem_cache_free(rmap_item_cache, rmap_item);
}

static inline struct stable_node *alloc_stable_node(void)
{
	return kmem_cache_zalloc(stable_node_cache, GFP_KERNEL);
}

static inline void free_stable_node(struct stable_node *stable_node)
{
	kmem_cache_free(stable_node_cache, stable_node);
}

static inline struct vma_node *alloc_vma_node(void)
{
	return kmem_cache_zalloc(vma_node_cache, GFP_KERNEL);
}

static inline void free_vma_node(struct vma_node *vma_node)
{
	kmem_cache_free(vma_node_cache, vma_node);
}

static inline struct mm_slot *alloc_mm_slot(void)
{
	return kmem_cache_zalloc(mm_slot_cache, GFP_KERNEL);
}

static inline void free_mm_slot(struct mm_slot *mm_slot)
{
	kmem_cache_free(mm_slot_cache, mm_slot);
}

static inline struct process_to_scan *alloc_process_to_scan(void)
{
	return kmem_cache_zalloc(processes_to_scan_cache, GFP_KERNEL);
}

static inline void free_process_to_scan(struct process_to_scan *pts)
{
	kmem_cache_free(processes_to_scan_cache, pts);
}

static int process2scan_exist(const char* comm)
{
	struct process_to_scan *pts;
	list_for_each_entry(pts, &processes_to_scan_head, list)
	{
		if (0 == strcmp(comm, pts->comm)) 
			return 1;
	}
	return 0;
}
static void destroy_processes_to_scan(void)
{
	struct process_to_scan *pts, *pts2;
	
	spin_lock(&processes_to_scan_lock);
	list_for_each_entry_safe(pts, pts2, &processes_to_scan_head, list)
	{
		kfree(pts->comm);
		list_del(&pts->list);
		free_process_to_scan(pts);
	}
	spin_unlock(&processes_to_scan_lock);

}
/* deprecated.
static struct mm_slot *get_mm_slot(struct mm_struct *mm)
{
	struct mm_slot *mm_slot;
	struct hlist_head *bucket;
	struct hlist_node *node;

	bucket = &mm_slots_hash[hash_ptr(mm, MM_SLOTS_HASH_SHIFT)];
	hlist_for_each_entry(mm_slot, node, bucket, link) {
		if (mm == mm_slot->mm)
			return mm_slot;
	}
	return NULL;
}*/

static void insert_to_mm_slots_hash(struct mm_struct *mm,
				    struct mm_slot *mm_slot)
{
	struct hlist_head *bucket;

	bucket = &mm_slots_hash[hash_ptr(mm, MM_SLOTS_HASH_SHIFT)];
	mm_slot->mm = mm;
	hlist_add_head(&mm_slot->link, bucket);
}

static inline int in_stable_tree(struct rmap_item *rmap_item)
{
	return rmap_item->address & STABLE_FLAG;
}

/*
 * ksmd, and unmerge_and_remove_all_rmap_items(), must not touch an mm's
 * page tables after it has passed through ksm_exit() - which, if necessary,
 * takes mmap_sem briefly to serialize against them.  ksm_exit() does not set
 * a special flag: they can just back out as soon as mm_users goes to zero.
 * ksm_test_exit() is used throughout to make this test for exit: in some
 * places for correctness, in some places just to avoid unnecessary work.
 */
static inline bool ksm_test_exit(struct mm_struct *mm)
{
	return atomic_read(&mm->mm_users) == 0;
}

/*
 * We use break_ksm to break COW on a ksm page: it's a stripped down
 *
 *	if (get_user_pages(current, mm, addr, 1, 1, 1, &page, NULL) == 1)
 *		put_page(page);
 *
 * but taking great care only to touch a ksm page, in a VM_MERGEABLE vma,
 * in case the application has unmapped and remapped mm,addr meanwhile.
 * Could a ksm page appear anywhere else?  Actually yes, in a VM_PFNMAP
 * mmap of /dev/mem or /dev/kmem, where we would not want to touch it.
 */
static int break_ksm(struct vm_area_struct *vma, unsigned long addr)
{
	struct page *page;
	int ret = 0;

	//output("calling break_ksm.\n");
	do {
		cond_resched();
		page = follow_page(vma, addr, FOLL_GET);
		if (IS_ERR_OR_NULL(page))
			break;
		if (PageKsm(page))
			ret = handle_mm_fault(vma->vm_mm, vma, addr,
							FAULT_FLAG_WRITE);
		else
			ret = VM_FAULT_WRITE;
		put_page(page);
	} while (!(ret & (VM_FAULT_WRITE | VM_FAULT_SIGBUS | VM_FAULT_OOM)));
	/*
	 * We must loop because handle_mm_fault() may back out if there's
	 * any difficulty e.g. if pte accessed bit gets updated concurrently.
	 *
	 * VM_FAULT_WRITE is what we have been hoping for: it indicates that
	 * COW has been broken, even if the vma does not permit VM_WRITE;
	 * but note that a concurrent fault might break PageKsm for us.
	 *
	 * VM_FAULT_SIGBUS could occur if we race with truncation of the
	 * backing file, which also invalidates anonymous pages: that's
	 * okay, that truncation will have unmapped the PageKsm for us.
	 *
	 * VM_FAULT_OOM: at the time of writing (late July 2009), setting
	 * aside mem_cgroup limits, VM_FAULT_OOM would only be set if the
	 * current task has TIF_MEMDIE set, and will be OOM killed on return
	 * to user; and ksmd, having no mm, would never be chosen for that.
	 *
	 * But if the mm is in a limited mem_cgroup, then the fault may fail
	 * with VM_FAULT_OOM even if the current task is not TIF_MEMDIE; and
	 * even ksmd can fail in this way - though it's usually breaking ksm
	 * just to undo a merge it made a moment before, so unlikely to oom.
	 *
	 * That's a pity: we might therefore have more kernel pages allocated
	 * than we're counting as nodes in the stable tree; but ksm_do_scan
	 * will retry to break_cow on each pass, so should recover the page
	 * in due course.  The important thing is to not let VM_MERGEABLE
	 * be cleared while any such pages might remain in the area.
	 */
	return (ret & VM_FAULT_OOM) ? -ENOMEM : 0;
}

static void break_cow(struct rmap_item *rmap_item)
{
	struct mm_struct *mm = rmap_item->mm;
	unsigned long addr = rmap_item->address;
	struct vm_area_struct *vma;

	/*
	 * It is not an accident that whenever we want to break COW
	 * to undo, we also need to drop a reference to the anon_vma.
	 */
	put_anon_vma(rmap_item->anon_vma);

	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, addr);
	if (!vma || vma->vm_start > addr)
		goto out;
	if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)
		goto out;
	break_ksm(vma, addr);
out:
	up_read(&mm->mmap_sem);
}

static struct page *page_trans_compound_anon(struct page *page)
{
	if (PageTransCompound(page)) {
		struct page *head = compound_trans_head(page);
		/*
		 * head may actually be splitted and freed from under
		 * us but it's ok here.
		 */
		if (PageAnon(head))
			return head;
	}
	return NULL;
}

static struct page *get_mergeable_page(struct rmap_item *rmap_item)
{
	struct mm_struct *mm = rmap_item->mm;
	unsigned long addr = rmap_item->address;
	struct vm_area_struct *vma;
	struct page *page;

	output("down_read. mm:%lx\n", (unsigned long)mm);
	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, addr);
	if (!vma || vma->vm_start > addr)
		goto out;
	if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma) {
		output("(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)\n");
		goto out;
	}

	page = follow_page(vma, addr, FOLL_GET);
	if (IS_ERR_OR_NULL(page)) {
		output("ERR_OR_NULL page.\n");
		goto out;
	}
	if (PageAnon(page) || page_trans_compound_anon(page)) {
		flush_anon_page(vma, page, addr);
		flush_dcache_page(page);
	} else {
		put_page(page);
out:		page = NULL;
	}
	up_read(&mm->mmap_sem);
	return page;
}

static void remove_node_from_stable_tree(struct stable_node *stable_node)
{
	struct rmap_item *rmap_item;
	struct hlist_node *hlist;

	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		if (rmap_item->hlist.next)
			ksm_pages_sharing--;
		else
			ksm_pages_shared--;
		put_anon_vma(rmap_item->anon_vma);
		rmap_item->address &= PAGE_MASK;
		cond_resched();
	}

	rb_erase(&stable_node->node, &root_stable_tree);
	free_stable_node(stable_node);
}

/*
 * get_ksm_page: checks if the page indicated by the stable node
 * is still its ksm page, despite having held no reference to it.
 * In which case we can trust the content of the page, and it
 * returns the gotten page; but if the page has now been zapped,
 * remove the stale node from the stable tree and return NULL.
 *
 * You would expect the stable_node to hold a reference to the ksm page.
 * But if it increments the page's count, swapping out has to wait for
 * ksmd to come around again before it can free the page, which may take
 * seconds or even minutes: much too unresponsive.  So instead we use a
 * "keyhole reference": access to the ksm page from the stable node peeps
 * out through its keyhole to see if that page still holds the right key,
 * pointing back to this stable node.  This relies on freeing a PageAnon
 * page to reset its page->mapping to NULL, and relies on no other use of
 * a page to put something that might look like our key in page->mapping.
 *
 * include/linux/pagemap.h page_cache_get_speculative() is a good reference,
 * but this is different - made simpler by sksm_thread_mutex being held, but
 * interesting for assuming that no other use of the struct page could ever
 * put our expected_mapping into page->mapping (or a field of the union which
 * coincides with page->mapping).  The RCU calls are not for KSM at all, but
 * to keep the page_count protocol described with page_cache_get_speculative.
 *
 * Note: it is possible that get_ksm_page() will return NULL one moment,
 * then page the next, if the page is in between page_freeze_refs() and
 * page_unfreeze_refs(): this shouldn't be a problem anywhere, the page
 * is on its way to being freed; but it is an anomaly to bear in mind.
 */
static struct page *get_ksm_page(struct stable_node *stable_node)
{
	struct page *page;
	void *expected_mapping;

	page = pfn_to_page(stable_node->kpfn);
	expected_mapping = (void *)stable_node +
				(PAGE_MAPPING_ANON | PAGE_MAPPING_KSM);
	rcu_read_lock();
	if (page->mapping != expected_mapping)
		goto stale;
	if (!get_page_unless_zero(page))
		goto stale;
	if (page->mapping != expected_mapping) {
		put_page(page);
		goto stale;
	}
	rcu_read_unlock();
	return page;
stale:
	rcu_read_unlock();
	remove_node_from_stable_tree(stable_node);
	return NULL;
}

/*
 * Removing rmap_item from stable or unstable tree.
 * This function will clean the information from the stable/unstable tree.
 */
static void remove_rmap_item_from_tree(struct rmap_item *rmap_item)
{
	if (rmap_item->address & STABLE_FLAG) {
		struct stable_node *stable_node;
		struct page *page;
		
		output("Try to remove rmap_item %lx from stable tree.\n", (unsigned long)rmap_item);
		stable_node = rmap_item->head;
		page = get_ksm_page(stable_node);
		if (!page)
			goto out;

		lock_page(page);
		hlist_del(&rmap_item->hlist);
		unlock_page(page);
		put_page(page);

		if (stable_node->hlist.first)
			ksm_pages_sharing--;
		else
			ksm_pages_shared--;

		put_anon_vma(rmap_item->anon_vma);
		rmap_item->address &= PAGE_MASK;

	} else if (rmap_item->address & UNSTABLE_FLAG) {
		unsigned char age;
		/*
		 * Usually ksmd can and must skip the rb_erase, because
		 * root_unstable_tree was already reset to RB_ROOT.
		 * But be careful when an mm is exiting: do the rb_erase
		 * if this rmap_item was inserted by this scan, rather
		 * than left over from before.
		 */
		output("Try to remove rmap_item %lx from unstable tree.\n", (unsigned long)rmap_item);
		age = (unsigned char)(sksm_scan.seqnr - rmap_item->address);
		// BUG_ON(age > 1);
		if (!age) {
			rb_erase(&rmap_item->node, &root_unstable_tree);
			output("remove okay.\n");
		} else {
			output("obsolete unstable node.\n");
		}

		ksm_pages_unshared--;
		rmap_item->address &= PAGE_MASK;
	}
out:
	cond_resched();		/* we're called from many long loops */
}

static void remove_trailing_rmap_items(struct rmap_item **rmap_list)
{
	while (*rmap_list) {
		struct rmap_item *rmap_item = *rmap_list;
		*rmap_list = rmap_item->rmap_list;
		remove_rmap_item_from_tree(rmap_item);
		free_rmap_item(rmap_item);
	}
}

static void reset_mm_slot_address(struct mm_slot *slot)
{
	struct rmap_item *rmap_item;
	struct rmap_item **rmap_list;
	rmap_list = &slot->rmap_list;

	while (*rmap_list) {
		rmap_item = *rmap_list;
		if ((rmap_item->address & PAGE_MASK) < slot->address)
			rmap_list = &rmap_item->rmap_list;
		else
			break;
	}
	remove_trailing_rmap_items(rmap_list);
	slot->address = 0;
}

// if address field in rmap_item has the INVALID_FLAG set, this rmap_item is considered to be invalid.
static void clear_invalid_rmap_items(struct vma_node *vma_node)
{
	struct rmap_item **curr;
	
	curr = &vma_node->rmap_list;
	while ( *curr )
	{
		if (!((*curr)->address & INVALID_FLAG))
		{
			curr = &(*curr)->rmap_list;
		}
		else
		{
			struct rmap_item *next = (*curr)->rmap_list;
			struct rmap_item *obsolete = *curr;
			remove_rmap_item_from_tree(obsolete);
			free_rmap_item(obsolete);
			*curr = next;
		}
	}
}

/*
// this function walk through the rmap_list hanging off the vma_node and remove the specified rmap_item.
static void remove_item_from_vma_node(struct vma_node *vma_node, struct rmap_item *trash)
{
	struct rmap_item **item;
	BUG_ON(NULL == vma_node || NULL == trash);
	item = &vma_node->rmap_list;
	if ( vma_node->rmap_list != trash ) {  // it doesn't remove the first one.
		while ( (*item)->rmap_list != trash )		
			item = &(*item)->rmap_list;
		*item = trash->rmap_list;
	} else {  // remove the first one.
		*item = (*item)->rmap_list;
	}
	remove_rmap_item_from_tree(trash);
	free_rmap_item(trash);
}*/
// don't use this function to del vma_node->rmap_list. 
// use vma_node_replace_bellwether instead. 
/*static void remove_rmap_item(struct rmap_item **prev, struct rmap_item *trash)
{
	BUG_ON(NULL == prev || NULL == trash);
	*prev->rmap_list = trash->rmap_list;
	remove_rmap_item_from_tree(trash);
	free_rmap_item(trash);
}*/
/*
static void vma_node_replace_bellwether(struct vma_node *vma_node)
{
	struct rmap_item *item = vma_node->rmap_list;
	BUG_ON( NULL == vma_node || NULL == vma_node->rmap_list);
	vma_node->rmap_list = vma_node->rmap_list->rmap_list;
	remove_rmap_item_from_tree(item);
	free_rmap_item(item);
}*/

/*
 * Though it's very tempting to unmerge in_stable_tree(rmap_item)s rather
 * than check every pte of a given vma, the locking doesn't quite work for
 * that - an rmap_item is assigned to the stable tree after inserting ksm
 * page and upping mmap_sem.  Nor does it fit with the way we skip dup'ing
 * rmap_items from parent to child at fork time (so as not to waste time
 * if exit comes before the next scan reaches it).
 *
 * Similarly, although we'd like to remove rmap_items (so updating counts
 * and freeing memory) when unmerging an area, it's easier to leave that
 * to the next pass of ksmd - consider, for example, how ksmd might be
 * in cmp_and_merge_page on one of the rmap_items we would be removing.
 */
static int unmerge_ksm_pages(struct vm_area_struct *vma,
			     unsigned long start, unsigned long end)
{
	unsigned long addr;
	int err = 0;

	for (addr = start; addr < end && !err; addr += PAGE_SIZE) {
		if (ksm_test_exit(vma->vm_mm))
			break;
		if (signal_pending(current))
			err = -ERESTARTSYS;
		else
			err = break_ksm(vma, addr);
	}
	return err;
}

/*
static int unmerge_rmap_item(struct rmap_item *item)
{
	if ( item->anon_vma ) {
		unsigned long address = item->address & PAGE_MASK;
		// un-finished. I'm really not sure we should unmerge the ksm page 
		// if the correspoing rmap_item is about to be removed.
	}
}*/

static int is_mergeable_vma(struct vm_area_struct *vma)
{
	unsigned long flags = vma->vm_flags;
	int pages_count;
	if (flags & ( VM_SHARED  | VM_MAYSHARE   |
				VM_PFNMAP    | VM_IO      | VM_DONTEXPAND |
				VM_RESERVED  | VM_HUGETLB | VM_INSERTPAGE |
				VM_NONLINEAR | VM_MIXEDMAP | VM_SAO))
		return 0;
#ifdef VM_SAO	
	if (flags & VM_SAO)
		return 0;
#endif

	if (vma->vm_file)
		return 0;

	if (NULL == vma->anon_vma)
		return 0;

	// only user space is eligible. 
	if ( vma->vm_end > 0x00007fffffffffff )
		return 0;

	pages_count = (((u64)vma->vm_end - (u64)vma->vm_start)>>12);
	if (pages_count < 8 ) // || pages_count > 0xffff)
	{
		//printk(KERN_EMERG"a huge anonymous vm_area encountered. MM address: %lX\n", vma->vm_mm);
		return 0;
	}

	return 1;
}

static void nuke_vma_node(struct mm_slot *mm_slot, struct vma_node *vma_node)
{
	// the caller has to make sure the items of ram_list has already been cleared.
	BUG_ON(vma_node->rmap_list);
	//if (vma_node->samples)
		//kfree(vma_node->samples);
	rb_erase(&vma_node->node, &mm_slot->vma_root);
	
	free_vma_node(vma_node);
}

static void nuke_vma_node_from_stack(struct mm_slot *mm_slot, struct tiny_stack *stack)
{
	int size = tiny_stack_size(stack);
	struct vma_node *vma_node;
	while (size--) {
		vma_node = (struct vma_node*)pop_tiny_stack(stack);	
		remove_trailing_rmap_items(&vma_node->rmap_list);
		BUG_ON(vma_node->rmap_list);
		nuke_vma_node(mm_slot, vma_node);
	}
}

/**
 * must hold mm_sem of mm_struct first.
 * 'cos mm_slot has a union, the parameter nuke_vma is used to indicate
 * if the "rb_root vma_root" field is available.
 */
static int nuke_mm_slot(struct mm_slot *mm_slot, int nuke_vma)
{
	struct rb_node *rb_node;
	struct vma_node *vma_node;

	clear_bit(MMF_VM_MERGEABLE, &mm_slot->mm->flags);
	//output("%d\n", nuke_vma);

	if (nuke_vma)
	{
		rb_node =  mm_slot->vma_root.rb_node;
		while (rb_node)
		{
			vma_node = rb_entry(rb_node, struct vma_node, node);	
			remove_trailing_rmap_items(&vma_node->rmap_list);	
			BUG_ON(vma_node->rmap_list);
			nuke_vma_node(mm_slot, vma_node);
			rb_node = mm_slot->vma_root.rb_node;
		}
	} 
	else 
	{
		remove_trailing_rmap_items(&mm_slot->rmap_list);
		BUG_ON(mm_slot->rmap_list);
	}

	// remove the mm_slot from hash_table and the global list.
	spin_lock(&sksm_mmlist_lock);
	hlist_del(&mm_slot->link);
	list_del(&mm_slot->mm_list);
	spin_unlock(&sksm_mmlist_lock);
	free_mm_slot(mm_slot);
	
	return 0;
}

static int is_valid_vma_node_pointer(struct mm_slot *slot, struct vma_node *vma_node)
{
	struct rb_node *rb_node;
	
	if(!vma_node)
		return 0;

	for (rb_node = rb_first(&slot->vma_root) ; rb_node; rb_node = rb_next(rb_node))
	{
		struct vma_node *curr = rb_entry(rb_node, struct vma_node, node);
		if ( curr == vma_node )
			return 1;
	}
	
	return 0;
}

static int is_valid_rmap_item_pointer(struct vma_node *vma_node, struct rmap_item *item)
{
	struct rmap_item *list = vma_node->rmap_list;

	if (!item)
		return 0;

	while (list)
	{
		if (list == item) {
			return 1;
		}
		list = list->rmap_list;
	}	
	return 0;
}

// return 0 on success, otherwise error code will be returned.
static int insert_vma_node(struct mm_slot *slot, struct vm_area_struct *vma)
{
	struct rb_node **new = &slot->vma_root.rb_node;
	struct rb_node *parent = NULL;
	struct vma_node *babe;

	while (*new) {
		struct vma_node *vma_node;
		parent = *new;
		vma_node = rb_entry(*new, struct vma_node, node);

		if (vma_node->vma == vma) // this vma already exists.
			return -1;

		if (vma_node->vma < vma) {
			new = &parent->rb_left;
		} else {
			new = &parent->rb_right;
		}
	}
	babe = alloc_vma_node();
	if (NULL == babe)
		return 1;
	babe->vma = vma;
	babe->start = vma->vm_start;
	babe->end = vma->vm_end;
	//babe->sample_coefficient = 255;
	babe->coefficient = 100;

	rb_link_node(&babe->node, parent, new);
	rb_insert_color(&babe->node, &slot->vma_root);
	
	vma->vm_flags |= VM_MERGEABLE;

	output("get a new mergeable vma. mm:%lx start:%lx end:%lx\n",
		(unsigned long)slot->mm, (unsigned long)vma->vm_start, (unsigned long)vma->vm_end);

	return 0;
}

#ifdef CONFIG_SYSFS
/*
 * Only called through the sysfs control interface:
 */
static int unmerge_and_remove_all_rmap_items(int nuke_vma)
{
        struct mm_slot *mm_slot;
        struct mm_struct *mm;
        struct vm_area_struct *vma;
        int err = 0;

	// output("%d\n", nuke_vma);

        spin_lock(&sksm_mmlist_lock);
        mm_slot = list_entry(sksm_mm_head.mm_list.next, struct mm_slot, mm_list);
        spin_unlock(&sksm_mmlist_lock);
        while (mm_slot != &sksm_mm_head)
	{
                mm = mm_slot->mm;
                down_read(&mm->mmap_sem);
		if (ksm_test_exit(mm)) {
			up_read(&mm->mmap_sem);
			goto _next;
		}
                for (vma = mm->mmap; vma; vma = vma->vm_next) {
                        if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)
                                continue;
                        err = unmerge_ksm_pages(vma, vma->vm_start, vma->vm_end);
                        if (err) {
				up_read(&mm->mmap_sem);
                                goto _out;
			}
                }
		up_read(&mm->mmap_sem);

_next:
		spin_lock(&sksm_mmlist_lock);
		mm_slot = list_entry(mm_slot->mm_list.next, struct mm_slot, mm_list);
		spin_unlock(&sksm_mmlist_lock);
	} // end of while (mm_slot != ... 
	
	spin_lock(&sksm_mmlist_lock);
        mm_slot = list_entry(sksm_mm_head.mm_list.next, struct mm_slot, mm_list);
        spin_unlock(&sksm_mmlist_lock);
	while (mm_slot != &sksm_mm_head)
	{
                mm = mm_slot->mm;
		down_read(&mm->mmap_sem);	
		clear_bit(MMF_VM_MERGEABLE, &mm->flags);
		nuke_mm_slot(mm_slot, nuke_vma);
		up_read(&mm->mmap_sem);
		mmdrop(mm);

		spin_lock(&sksm_mmlist_lock);
		mm_slot = list_entry(sksm_mm_head.mm_list.next, struct mm_slot, mm_list);
		spin_unlock(&sksm_mmlist_lock);
	} // end of for (mm_slot = ... 
		
	sksm_scan.seqnr = 0;

_out:
        spin_lock(&sksm_mmlist_lock);
        sksm_scan.mm_slot = &sksm_mm_head;
        spin_unlock(&sksm_mmlist_lock);
	output("exit.\n");
        return err;
}
#endif /* CONFIG_SYSFS */

static void quicksort(u32 a[], int l, int h)
{
	int i, j, key;

	if (l>=h)
		return;

	i = l;
	j = h;
	key = a[i];

	while (i < j)
	{
		while(i<j && a[j]>key)
			j--;

		if (i < j) 
			a[i++]=a[j];

		while (i<j && a[i]<key)
			i++;

		if (i < j)	
			 a[j--]=a[i];
	}

	a[i]=key;
	if (l < i-1)
		quicksort(a,l,i-1);

	if (i+1 < h)
		quicksort(a,i+1,h);
 
}
/**
 * The crc16 function.
 */
static u16 crc16_checksum(u8 *buf, u32 len)
{
	u16 crc = 0;
	u16 mask, flag;

	for (; len; --len, ++buf) {
		for (mask = 0x80; mask; mask >>= 1) {
		 	flag = (crc & 0x8000);
			 crc <<= 1;
			 crc |= ((*buf & mask) ? 1 : 0);

			 if (flag)
				 crc ^= 0x1021;
		 }
	}

	 return crc;
}

static u32 calc_checksum(struct page *page)
{
	u32 checksum;
	void *addr = kmap_atomic(page, KM_USER0);
	checksum = jhash2(addr, PAGE_SIZE/4, 17);
	kunmap_atomic(addr, KM_USER0);
	return checksum;
}

/**
 * compare two block of memory in unit of 8-byte.
 * This function is written in x86 assembly so it runs faster than the normal c code version.
 */
static long cmp_x64(void *left, void *right, size_t n)
{
	size_t num = n / 8;
	register long res = 0;

	__asm__ __volatile__
	(
	 "testq %3,%3\n\t"
	 "repe  cmpsq\n\t"
	 "je        1f\n\t"
	 "sbbq      %0,%0\n\t"
	 "orq       $1,%0\n"
	 "1:"
         : "=&a"(res)
	 : "0"(res), "S"(left), "D"(right), "c"(num)
	 : "cc");

	return res;
}

/*This function print a block of binary memory into human-readable hexideciam string.*/
static char* bins2hexs(const unsigned char* mem, int mem_len, char* buff, int buff_len)
{
	int len_expected, i;
	char *buff_expected;
	char small_buff[3];

	if ( NULL == mem || 0 == mem_len || NULL == buff || 0 == buff_len ) 
	{
		if ( NULL != buff && 0 != buff_len )
		{
			memset(buff, 0, buff_len);
			return buff;
		}
		else
		{
			return NULL;
		}
	}

	memset(buff, 0, buff_len);

	len_expected = mem_len * 2;
	//char* buff_expected = new char[len_expected];
	buff_expected = kmalloc(len_expected, GFP_KERNEL);
	for ( i = 0; i < mem_len; i ++ )
	{
		int height = ( (mem[i] & 0xf0) >> 4);
		int low = (mem[i] & 0x0f);

		sprintf(small_buff, "%X", height);
		sprintf(small_buff+1, "%X", low);
		
		memcpy(buff_expected + i * 2, small_buff, 2);
	}
	
	if ( buff_len >= len_expected )
	{
		memcpy(buff, buff_expected, len_expected);
	}

	//delete []buff_expected;
	kfree(buff_expected);

	return buff;
}

static unsigned long simple_page_sum(const char* page_addr)
{
	int i;
	unsigned long sum;
	unsigned int *ptr;

	sum = 0;
	ptr = (unsigned int*)page_addr;

	for (i = 0; i < 1024; i++)
	{
		sum += (unsigned long)ptr[i];
		//output("sum %d %u %lu\n", i, page_addr[i], sum);
	}

	return 0;
}

/**
 * this is the function of calculate the md5 hash code.
 */
static int md5_hash(const char *mem, u32 len, u8 *hash)
{
	u32 size;
	struct shash_desc *sdescmd5;
	int err;

        struct crypto_shash *md5 = crypto_alloc_shash("md5", 0, 0);
      if (IS_ERR(md5)) 
			return -1;
      size = sizeof(struct shash_desc) + crypto_shash_descsize(md5);
      sdescmd5 = kmalloc(size, GFP_KERNEL);
      if (!sdescmd5) {
              err = -1;
              goto malloc_err;
      }
      sdescmd5->tfm = md5;
      sdescmd5->flags = 0x0;

      err = crypto_shash_init(sdescmd5);
      if (err) {
	      err = -1;
              goto hash_err;
      }
      crypto_shash_update(sdescmd5, mem, len);
      err = crypto_shash_final(sdescmd5, hash);

hash_err:
      kfree(sdescmd5);
malloc_err:
      crypto_free_shash(md5);

      return err;
}

static struct vm_area_struct *does_vma_exist(struct mm_struct *mm, struct vma_node *vma_node)
{
	struct vm_area_struct *vma = find_vma(mm, vma_node->start);
	if (vma && vma->vm_mm && vma->vm_start == vma_node->start && vma->vm_end == vma_node->end) {
		vma_node->vma = vma;	
		return vma;
	}
	else
		return NULL;
}

static int memcmp_pages(struct page *page1, struct page *page2)
{
	char *addr1, *addr2;
	int ret;

	//print_page_content(page1);
	//print_page_content(page2);

	//output("kmap_atomic page1:%lx  vaddr:%lx\n", (unsigned long)page1, page1->virtual);
	addr1 = kmap_atomic(page1, KM_USER0);
	//output("kmap_atomic page2:%lx.\n", (unsigned long)page2);
	addr2 = kmap_atomic(page2, KM_USER1);
	ret = memcmp(addr1, addr2, PAGE_SIZE);
	//ret = cmp_x64(addr1, addr2, PAGE_SIZE);
	kunmap_atomic(addr2, KM_USER1);
	kunmap_atomic(addr1, KM_USER0);

	return ret;
}

static inline int pages_identical(struct page *page1, struct page *page2)
{
	return !memcmp_pages(page1, page2);
}

static int write_protect_page(struct vm_area_struct *vma, struct page *page,
			      pte_t *orig_pte)
{
	struct mm_struct *mm = vma->vm_mm;
	unsigned long addr;
	pte_t *ptep;
	spinlock_t *ptl;
	int swapped;
	int err = -EFAULT;

	addr = page_address_in_vma(page, vma);
	if (addr == -EFAULT) {
		output("page doesn't belong to the vma.\n");
		goto out;
	}

	BUG_ON(PageTransCompound(page));
	// check that page is mapped at the address into mm. Return pte mapped and locked on success.
	ptep = page_check_address(page, mm, addr, &ptl, 0); 
	if (!ptep) {
		output("page_check_address failed.\n");
		goto out;
	}

	if (pte_write(*ptep) || pte_dirty(*ptep)) {
		pte_t entry;
		int mapcount, count;

		swapped = PageSwapCache(page);
		flush_cache_page(vma, addr, page_to_pfn(page));
		/*
		 * Ok this is tricky, when get_user_pages_fast() run it doesn't
		 * take any lock, therefore the check that we are going to make
		 * with the pagecount against the mapcount is racey and
		 * O_DIRECT can happen right after the check.
		 * So we clear the pte and flush the tlb before the check
		 * this assure us that no O_DIRECT can happen after the check
		 * or in the middle of the check.
		 */
		entry = ptep_clear_flush(vma, addr, ptep);
		/*
		 * Check that no O_DIRECT or similar I/O is in progress on the
		 * page
		 */
		mapcount = page_mapcount(page);	
		count = page_count(page);
		if ( mapcount + 1 + swapped != count ) { // why why why ...
			set_pte_at(mm, addr, ptep, entry);
			output("Err: page_mapcount returns %d, swapped is %d, page_count returns %d.", mapcount, swapped, count);
			goto out_unlock;
		}
		if (pte_dirty(entry))
			set_page_dirty(page);
		entry = pte_mkclean(pte_wrprotect(entry));   //  clear the dirty bit.
		set_pte_at_notify(mm, addr, ptep, entry);
	}
	*orig_pte = *ptep;
	err = 0;

out_unlock:
	pte_unmap_unlock(ptep, ptl);
out:
	return err;
}

/**
 * replace_page - replace page in vma by new ksm page
 * @vma:      vma that holds the pte pointing to page
 * @page:     the page we are replacing by kpage
 * @kpage:    the ksm page we replace page by
 * @orig_pte: the original value of the pte
 *
 * Returns 0 on success, -EFAULT on failure.
 */
static int replace_page(struct vm_area_struct *vma, struct page *page,
			struct page *kpage, pte_t orig_pte)
{
	struct mm_struct *mm = vma->vm_mm;
	pgd_t *pgd;
	pud_t *pud;
	pmd_t *pmd;
	pte_t *ptep;
	spinlock_t *ptl;
	unsigned long addr;
	int err = -EFAULT;

	addr = page_address_in_vma(page, vma);
	if (addr == -EFAULT)
		goto out;

	pgd = pgd_offset(mm, addr);
	if (!pgd_present(*pgd))
		goto out;

	pud = pud_offset(pgd, addr);
	if (!pud_present(*pud))
		goto out;

	pmd = pmd_offset(pud, addr);
	BUG_ON(pmd_trans_huge(*pmd));
	if (!pmd_present(*pmd))
		goto out;

	ptep = pte_offset_map_lock(mm, pmd, addr, &ptl);
	if (!pte_same(*ptep, orig_pte)) {
		pte_unmap_unlock(ptep, ptl);
		goto out;
	}

	get_page(kpage);
	page_add_anon_rmap(kpage, vma, addr);

	flush_cache_page(vma, addr, pte_pfn(*ptep));
	ptep_clear_flush(vma, addr, ptep);
	set_pte_at_notify(mm, addr, ptep, mk_pte(kpage, vma->vm_page_prot));

	page_remove_rmap(page);
	if (!page_mapped(page))
		try_to_free_swap(page);
	put_page(page);

	pte_unmap_unlock(ptep, ptl);
	err = 0;
out:
	return err;
}

static int page_trans_compound_anon_split(struct page *page)
{
	int ret = 0;
	struct page *transhuge_head = page_trans_compound_anon(page);
	if (transhuge_head) {
		/* Get the reference on the head to split it. */
		if (get_page_unless_zero(transhuge_head)) {
			/*
			 * Recheck we got the reference while the head
			 * was still anonymous.
			 */
			if (PageAnon(transhuge_head))
				ret = split_huge_page(transhuge_head);
			else
				/*
				 * Retry later if split_huge_page run
				 * from under us.
				 */
				ret = 1;
			put_page(transhuge_head);
		} else
			/* Retry later if split_huge_page run from under us. */
			ret = 1;
	}
	return ret;
}

/*
 * try_to_merge_one_page - take two pages and merge them into one
 * @vma: the vma that holds the pte pointing to page
 * @page: the PageAnon page that we want to replace with kpage
 * @kpage: the PageKsm page that we want to map instead of page,
 *         or NULL the first time when we want to use page as kpage.
 *
 * This function returns 0 if the pages were merged, -EFAULT otherwise.
 */
static int try_to_merge_one_page(struct vm_area_struct *vma,
				 struct page *page, struct page *kpage)
{
	pte_t orig_pte = __pte(0);
	int err = -EFAULT;

	if (page == kpage)			/* ksm page forked */
		return 0;

	if (!(vma->vm_flags & VM_MERGEABLE)) {
		output("not a mergeable vma.\n");
		goto out;
	}
	if (PageTransCompound(page) && page_trans_compound_anon_split(page)) {
		output("compound anon.\n");
		goto out;
	}
	BUG_ON(PageTransCompound(page));
	if (!PageAnon(page)) {
		output("This is not an anonymous page.\n");
		goto out;
	}

	/*
	 * We need the page lock to read a stable PageSwapCache in
	 * write_protect_page().  We use trylock_page() instead of
	 * lock_page() because we don't want to wait here - we
	 * prefer to continue scanning and merging different pages,
	 * then come back to this page when it is unlocked.
	 */
	if (!trylock_page(page)) {
		output("trylock_page failed.\n");
		goto out;
	}
	/*
	 * If this anonymous page is mapped only here, its pte may need
	 * to be write-protected.  If it's mapped elsewhere, all of its
	 * ptes are necessarily already write-protected.  But in either
	 * case, we need to lock and check page_count is not raised.
	 */
	if (write_protect_page(vma, page, &orig_pte) == 0) {
		if (!kpage) {
			/*
			 * While we hold page lock, upgrade page from
			 * PageAnon+anon_vma to PageKsm+NULL stable_node:
			 * stable_tree_insert() will update stable_node.
			 */
			set_page_stable_node(page, NULL);
			mark_page_accessed(page);
			err = 0;
		} else if (pages_identical(page, kpage))
			err = replace_page(vma, page, kpage, orig_pte);
			if ( err ) 
				output("replace_page failed.\n");
	} else {
		output("write_protect_page failed.\n");
	}

	if ((vma->vm_flags & VM_LOCKED) && kpage && !err) {
		munlock_vma_page(page);
		if (!PageMlocked(kpage)) {
			unlock_page(page);
			lock_page(kpage);
			mlock_vma_page(kpage);
			page = kpage;		/* for final unlock */
		}
	}

	unlock_page(page);
out:
	return err;
}

/*
 * try_to_merge_with_ksm_page - like try_to_merge_two_pages,
 * but no new kernel page is allocated: kpage must already be a ksm page.
 *
 * This function returns 0 if the pages were merged, -EFAULT otherwise.
 */
static int try_to_merge_with_ksm_page(struct rmap_item *rmap_item,
				      struct page *page, struct page *kpage)
{
	struct mm_struct *mm = rmap_item->mm;
	struct vm_area_struct *vma;
	int err = -EFAULT;

	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, rmap_item->address);
	if (!vma || vma->vm_start > rmap_item->address) {
		output("find_vma failed.\n");
		goto out;
	}

	err = try_to_merge_one_page(vma, page, kpage);
	if (err) {
		output("try_to_merge_one_page failed.\n");
		goto out;
	}

	/* Must get reference to anon_vma while still holding mmap_sem */
	rmap_item->anon_vma = vma->anon_vma;
	get_anon_vma(vma->anon_vma);
	output("get_anon_vma okay.\n");
out:
	up_read(&mm->mmap_sem);
	return err;
}

/*
 * try_to_merge_two_pages - take two identical pages and prepare them
 * to be merged into one page.
 *
 * This function returns the kpage if we successfully merged two identical
 * pages into one ksm page, NULL otherwise.
 *
 * Note that this function upgrades page to ksm page: if one of the pages
 * is already a ksm page, try_to_merge_with_ksm_page should be used.
 */
static struct page *try_to_merge_two_pages(struct rmap_item *rmap_item,
					   struct page *page,
					   struct rmap_item *tree_rmap_item,
					   struct page *tree_page)
{
	int err;

	err = try_to_merge_with_ksm_page(rmap_item, page, NULL);
	if (!err) {
		err = try_to_merge_with_ksm_page(tree_rmap_item,
							tree_page, page);
		/*
		 * If that fails, we have a ksm page with only one pte
		 * pointing to it: so break it.
		 */
		if (err) {
			break_cow(rmap_item);
			output("try_to_merge_with_ksm_page failed.\n");
		}
	} else {
		output("creating ksm page failed.");
	}
	return err ? NULL : page;
}

/*
 * stable_tree_search - search for page inside the stable tree
 *
 * This function checks if there is a page inside the stable tree
 * with identical content to the page that we are scanning right now.
 *
 * This function returns the stable tree node of identical content if found,
 * NULL otherwise.
 */
static struct page *stable_tree_search(struct page *page)
{
	struct rb_node *node = root_stable_tree.rb_node;
	struct stable_node *stable_node;

	stable_node = page_stable_node(page);
	if (stable_node) {			/* ksm page forked */
		get_page(page);
		return page;
	}

	while (node) {
		struct page *tree_page;
		int ret;

		cond_resched();
		stable_node = rb_entry(node, struct stable_node, node);
		tree_page = get_ksm_page(stable_node);
		if (!tree_page)
			return NULL;

		ret = memcmp_pages(page, tree_page);

		if (ret < 0) {
			put_page(tree_page);
			node = node->rb_left;
		} else if (ret > 0) {
			put_page(tree_page);
			node = node->rb_right;
		} else
			return tree_page;
	}

	return NULL;
}

static int is_f0_page(struct page *page)
{
	int i, ret;
	int zero_page, f_page;
	u8 *addr;

	zero_page = f_page = 0;
	ret = 0;

	addr = (u8*)kmap_atomic(page);
	if (0 == addr[0])
		zero_page = 1;
	else if (0xffffffffffffffff == addr[0])
		f_page = 1;

	if (zero_page){
		for (i = 1; i < 512; i++)
		{
			if (addr[i] != 0)		
				goto _out;	
		}
		ret = 1;
	}
	else if (f_page){
		for (i = 1; i < 512; i++)
		{
			if (addr[i] != 0xffffffffffffffff)
				goto _out;
		}
		ret = 1;
	}

_out:
	kunmap_atomic(addr);

	return ret;
}

static int print_page_content(struct page *page)
{
	char *buff;
	int buff_len;
	void *addr;
	unsigned long sum;

	buff_len = 4096 * 2 + 1;
	buff = kmalloc(buff_len, GFP_KERNEL);
	if (!buff)
		return -1;
	memset(buff, 0, buff_len);
	
	addr = kmap_atomic(page); 
	sum =  simple_page_sum(addr);
	bins2hexs(addr, 4096, buff, buff_len);
	kunmap_atomic(addr);
	output("%lu  %s\n", sum, buff);
	
	kfree(buff);

	return 0;
}

static void print_the_stable_tree(void)
{
	struct rb_node *rb_node;
	struct stable_node *stable_node;
	struct page *page;
	//struct rmap_item *item;
	struct hlist_node *hlist_node;
	int count;
	
	for (rb_node = rb_first(&root_stable_tree); rb_node; rb_node = rb_next(rb_node))
	{
		stable_node = rb_entry(rb_node, struct stable_node, node);	
		count = 0;		

		hlist_for_each(hlist_node, &stable_node->hlist)
			count++;

		page = pfn_to_page(stable_node->kpfn);
		print_page_content(page);
		output("%d\n", count);
	}
}

/*
 * stable_tree_insert - insert rmap_item pointing to new ksm page
 * into the stable tree.
 *
 * This function returns the stable tree node just allocated on success,
 * NULL otherwise.
 */
static struct stable_node *stable_tree_insert(struct page *kpage)
{
	struct rb_node **new = &root_stable_tree.rb_node;
	struct rb_node *parent = NULL;
	struct stable_node *stable_node;

	while (*new) {
		struct page *tree_page;
		int ret;

		cond_resched();
		stable_node = rb_entry(*new, struct stable_node, node);
		tree_page = get_ksm_page(stable_node);
		if (!tree_page)
			return NULL;

		ret = memcmp_pages(kpage, tree_page);
		put_page(tree_page);

		parent = *new;
		if (ret < 0)
			new = &parent->rb_left;
		else if (ret > 0)
			new = &parent->rb_right;
		else {
			/*
			 * It is not a bug that stable_tree_search() didn't
			 * find this node: because at that time our page was
			 * not yet write-protected, so may have changed since.
			 */
			return NULL;
		}
	}

	stable_node = alloc_stable_node();
	if (!stable_node)
		return NULL;

	rb_link_node(&stable_node->node, parent, new);
	rb_insert_color(&stable_node->node, &root_stable_tree);

	INIT_HLIST_HEAD(&stable_node->hlist);

	stable_node->kpfn = page_to_pfn(kpage);
	set_page_stable_node(kpage, stable_node);

	return stable_node;
}

/*
 * unstable_tree_search_insert - search for identical page,
 * else insert rmap_item into the unstable tree.
 *
 * This function searches for a page in the unstable tree identical to the
 * page currently being scanned; and if no identical page is found in the
 * tree, we insert rmap_item as a new object into the unstable tree.
 *
 * This function returns pointer to rmap_item found to be identical
 * to the currently scanned page, NULL otherwise.
 *
 * This function does both searching and inserting, because they share
 * the same walking algorithm in an rbtree.
 */
static struct rmap_item *unstable_tree_search_insert(struct rmap_item *rmap_item,
					      struct page *page,
					      struct page **tree_pagep)

{
	struct rb_node **new = &root_unstable_tree.rb_node;
	struct rb_node *parent = NULL;

	//output("*new: %lx.\n", (unsigned long)*new);
	while (*new) {
		struct rmap_item *tree_rmap_item;
		struct page *tree_page;
		int ret;

		cond_resched();
		tree_rmap_item = rb_entry(*new, struct rmap_item, node);
		tree_page = get_mergeable_page(tree_rmap_item);
		if (IS_ERR_OR_NULL(tree_page))
		{
			output("get_mergeable_page failed.\n");
			return NULL;
		}
		output("get_mergeable_page okay.\n");

		/*
		 * Don't substitute a ksm page for a forked page.
		 */
		if (page == tree_page) {
			put_page(tree_page);
			return NULL;
		}
		ret = memcmp_pages(page, tree_page);
		output("memcmp_pages return %d.\n", ret);

		parent = *new;
		if (ret < 0) {
			put_page(tree_page);
			new = &parent->rb_left;
		} else if (ret > 0) {
			put_page(tree_page);
			new = &parent->rb_right;
		} else {
			*tree_pagep = tree_page;
			return tree_rmap_item;
		}
	}

	rmap_item->address &= 0xfffffffffffffc00;
	rmap_item->address |= UNSTABLE_FLAG;
	rmap_item->address |= (sksm_scan.seqnr & SEQNR_MASK);
	rb_link_node(&rmap_item->node, parent, new);
	rb_insert_color(&rmap_item->node, &root_unstable_tree);

	ksm_pages_unshared++;
	output("a new rmap_item has been added to unstable tree.\n");	
	
	//new = &root_unstable_tree.rb_node;
	//output("*new new: %lx.\n", (unsigned long)*new);

	return NULL;
}

/*
 * stable_tree_append - add another rmap_item to the linked list of
 * rmap_items hanging off a given node of the stable tree, all sharing
 * the same ksm page.
 */
static void stable_tree_append(struct rmap_item *rmap_item,
			       struct stable_node *stable_node)
{
	rmap_item->head = stable_node;
	rmap_item->address |= STABLE_FLAG;
	hlist_add_head(&rmap_item->hlist, &stable_node->hlist);

	if (rmap_item->hlist.next)
		ksm_pages_sharing++;
	else
		ksm_pages_shared++;
}

/*
 * cmp_and_merge_page - first see if page can be merged into the stable tree;
 * if not, compare checksum to previous and if it's the same, see if page can
 * be inserted into the unstable tree, or merged with a page already there and
 * both transferred to the stable tree.
 *
 * @page: the page that we are searching identical page to.
 * @rmap_item: the reverse mapping into the virtual address of this page
 */
static void cmp_and_merge_page(struct page *page, struct rmap_item *rmap_item)
{
	struct rmap_item *tree_rmap_item;
	struct page *tree_page = NULL;
	struct stable_node *stable_node;
	struct page *kpage;
	void *addr;
	u16 checksum;
	int err;

	remove_rmap_item_from_tree(rmap_item);

	/* We first start with searching the page inside the stable tree */
	kpage = stable_tree_search(page);
	output("stable_tree_search returns kpage %lx.\n", (unsigned long)kpage);
	if (kpage) {
		output("found %lx in stable tree.\n", (unsigned long)kpage);
		err = try_to_merge_with_ksm_page(rmap_item, page, kpage);
		if (!err) {
			/*
			 * The page was successfully merged:
			 * add its rmap_item to the stable tree.
			 */
			lock_page(kpage);
			stable_tree_append(rmap_item, page_stable_node(kpage));
			unlock_page(kpage);
			output("%lx was merged successfully\n", (unsigned long)kpage);
		}
		put_page(kpage);
		return;
	}

	/* If the hash value of the page has changed from the last time
	 * we calculated it, this page is changing frequently: therefore we
	 * don't want to insert it in the unstable tree, and we don't want
	 * to waste our time searching for something identical to it there.
	 */
	addr = kmap_atomic(page);
	if (sksm_run != SKSM_RUN_F0PAGES_ONLY)
		checksum = crc16_checksum(addr, PAGE_SIZE);	
	else
		checksum = (u16)simple_page_sum(addr);
	kunmap_atomic(addr);
	if (rmap_item->oldchecksum != checksum) {
		rmap_item->oldchecksum = checksum;
		output("checksum doesn't match. return.\n");
		return;
	}

	tree_rmap_item =
		unstable_tree_search_insert(rmap_item, page, &tree_page);
	output("unstable_tree_search_insert returns: %lx\n", (unsigned long)tree_rmap_item);
	if (tree_rmap_item) {
		kpage = try_to_merge_two_pages(rmap_item, page,
						tree_rmap_item, tree_page);
		output("The same page is in unstable tree, we merge the two pages.\n");
		put_page(tree_page);
		/*
		 * As soon as we merge this page, we want to remove the
		 * rmap_item of the page we have merged with from the unstable
		 * tree, and insert it instead as new node in the stable tree.
		 */
		if (kpage) {
			remove_rmap_item_from_tree(tree_rmap_item);

			lock_page(kpage);
			stable_node = stable_tree_insert(kpage);
			if (stable_node) {
				output("Move them to stable tree OKAY.\n");	
				stable_tree_append(tree_rmap_item, stable_node);
				stable_tree_append(rmap_item, stable_node);
			}
			unlock_page(kpage);

			/*
			 * If we fail to insert the page into the stable tree,
			 * we will have 2 virtual addresses that are pointing
			 * to a ksm page left outside the stable tree,
			 * in which case we need to break_cow on both.
			 */
			if (!stable_node) {
				output("Move them to stable tree FAILED.\n");	
				break_cow(tree_rmap_item);
				break_cow(rmap_item);
			}
		}
	}
}

static void walk_through_tasks(void) 
{
	struct task_struct *p;
	char comm[256];
	int pid_nr;
	int i, count; 
	int matched;
	//const char *task_comms[] = {"mal", "gnome-terminal", "epiphany-browse"};
	const char *task_comms[] = {"mal"};

	read_lock(&tasklist_lock);
	for_each_process(p) {
		get_task_comm(comm, p);
		pid_nr = p->pid;
		matched = 0;	
		// testing code...
		count = sizeof(task_comms)/sizeof(task_comms[0]);
		for (i = 0; i < count; i++)
		{
			if (0 == strcasecmp(task_comms[i], comm))
			{
				matched = 1;
			}
		}
/*		if (SKSM_RUN_F0PAGES_ONLY != sksm_run)
		{
			spin_lock(&processes_to_scan_lock);		
			matched = process2scan_exist(comm);
			spin_unlock(&processes_to_scan_lock);		
		}
		else
		{
			matched = (pid_nr > 100 ? 1 : 0);
		}
*/	
		if (matched)
		{
			//pid_nr = p->pid;
			//output("@@@@@@@@@ Get %s's pid: %d\n", comm, pid_nr);
			task_ksm_enter(p);
		}
	}
	read_unlock(&tasklist_lock);
}

static struct rmap_item *scan_get_next_rmap_item(struct page **page)
{
	struct mm_struct *mm;
	struct mm_slot *slot;
	struct vm_area_struct *vma;
	struct rb_node *rb_node;
	struct tiny_stack stack;
	int tail_of_the_rmap_list_reached;
	
	init_tiny_stack(&stack);
again:
	if (list_empty(&sksm_mm_head.mm_list))
		return NULL;

	slot = sksm_scan.mm_slot;
	if (slot==&sksm_mm_head) // restart ...
	{
		/*
		 * A number of pages can hang around indefinitely on per-cpu
		 * pagevecs, raised page count preventing write_protect_page
		 * from merging them.  Though it doesn't really matter much,
		 * it is puzzling to see some stuck in pages_volatile until
		 * other activity jostles them out, and they also prevented
		 * LTP's KSM test from succeeding deterministically; so drain
		 * them here (here rather than on entry to ksm_do_scan(),
		 * so we don't IPI too often when pages_to_scan is set low).
		 */
		lru_add_drain_all();
		
		/*for (rb_node = rb_first(&root_unstable_tree); rb_node; rb_node = rb_next(rb_node))
		{
			struct rmap_item *item = rb_entry(rb_node, struct rmap_item, node);
			item->address &= ~UNSTABLE_FLAG;
		}*/
		root_unstable_tree = RB_ROOT;
		sksm_scan.seqnr++;
		output("reset root_unstable_tree.");

		spin_lock(&sksm_mmlist_lock);
		slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		sksm_scan.mm_slot = slot;
		spin_unlock(&sksm_mmlist_lock);

		/*
		 * Although we tested list_empty() above, a racing __ksm_exit
		 * of the last mm on the list may have removed it since then.
		 */
		if (slot == &sksm_mm_head)
			return NULL;
	} // end of the case of restarting.
	
	mm = slot->mm;
	down_read(&mm->mmap_sem);	
	if (ksm_test_exit(mm)) {   // the process has exited.
		// the current mm_slot will be invalid, so we move to the next mm_slot.
		spin_lock(&sksm_mmlist_lock);
		sksm_scan.mm_slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		spin_unlock(&sksm_mmlist_lock);

		nuke_mm_slot(slot, 1);
		clear_bit(MMF_VM_MERGEABLE, &mm->flags);
		up_read(&mm->mmap_sem);
		mmdrop(mm);

		goto again;
	}

	if (is_valid_vma_node_pointer(slot, slot->curr))
	{
		rb_node = &slot->curr->node;
	}
	else
	{
		rb_node = rb_first(&slot->vma_root);
		slot->curr = rb_entry(rb_node, struct vma_node, node);
		output("Go to the first vma_node %lx.\n", (unsigned long)rb_node);
	}

	for ( ; rb_node; rb_node = rb_next(rb_node))
	{
		// get the current vma_node.
		struct vma_node *current_vma_node = rb_entry(rb_node, struct vma_node, node);
		slot->curr= current_vma_node;
		
		// if this vma_node is NOT valid, NULL will be returned.
		vma = does_vma_exist(mm, current_vma_node);	
		if (NULL == vma)
		{
			// save this invalid vma_node. it will be erased later.
			push_tiny_stack(&stack, (void*)current_vma_node);
			// output("vma %lx does not exist.\n", (unsigned long)current_vma_node->vma);
			continue;
		}

		if (!is_valid_rmap_item_pointer(current_vma_node, current_vma_node->rmap_current))
		{
			current_vma_node->rmap_current = current_vma_node->rmap_list;
			vma_node_do_sampling(current_vma_node);
			continue;
		}
		
		while (current_vma_node->rmap_current)  // rmap_current points to a valid rmap_item. 
		{
			struct rmap_item *item = current_vma_node->rmap_current;
			if (item->rmap_list) // the next rmap_item still is valid, which means it's not the last one.
			{
				current_vma_node->rmap_current = item->rmap_list;
				tail_of_the_rmap_list_reached = 0;
			}
			else // the last one
			{
				current_vma_node->rmap_current = NULL;
				tail_of_the_rmap_list_reached = 1;
			}
			if (item->address & INVALID_FLAG) // this is a invalid address.
			{
				continue;
			}
			*page = follow_page(current_vma_node->vma, item->address, FOLL_GET);
			if ( IS_ERR_OR_NULL(*page)){
				// failed...
				item->address |= INVALID_FLAG;  // mark the address as invalid.
				continue;
			}
			if (PageAnon(*page) || page_trans_compound_anon(*page)) {
				// succeeded !!!
				flush_anon_page(vma, *page, item->address);
				flush_dcache_page(*page);
				up_read(&mm->mmap_sem);
				nuke_vma_node_from_stack(slot, &stack);
				clear_invalid_rmap_items(current_vma_node);
				
				if (tail_of_the_rmap_list_reached)
				{
					struct vma_node *next_vma_node;
					rb_node = rb_next(rb_node);	
					if (rb_node) {
						next_vma_node = rb_entry(rb_node, struct vma_node, node);
						slot->curr = next_vma_node;
					} else {
						slot->curr = NULL;
					}
				}
				output("return item: %lx\n", (unsigned long)item);	
				return item;
			}
			item->address |= INVALID_FLAG;
			// still failed ...
			put_page(*page);
		}

		if (current_vma_node->rmap_list)  // this vma_node has some rmap_items hanging off it.
		{	// so reset it to the first one. It will be handled in the next loop. 
			current_vma_node->rmap_current = current_vma_node->rmap_list; 
		} else {
			current_vma_node->rmap_current = NULL;
		}
		clear_invalid_rmap_items(current_vma_node); 
	        // when we reach here, we will go to the next vma_node.
	} // end of for loop. walk through all vam_node.

	up_read(&mm->mmap_sem);
	nuke_vma_node_from_stack(slot, &stack);  // clear the invalid vma_node.

	slot->curr = NULL;

	// when reach here, we get no rmap_items to this mm_slot. so, walk to the next mm_slot
	spin_lock(&sksm_mmlist_lock);
	slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
	sksm_scan.mm_slot = slot;
	spin_unlock(&sksm_mmlist_lock);
	
	if(slot != &sksm_mm_head )
		goto again;  // now let's go to the next mm_slot.

	output("Exit scan_get_next_rmap_item.\n");

	return NULL;
}

// This function is for f0pages only.
static struct rmap_item *get_next_rmap_item(struct mm_slot *slot)
{
	struct rmap_item *rmap_item;
	struct rmap_item **rmap_list;
	
	rmap_list = &slot->rmap_list;

	while (*rmap_list)
	{
		rmap_item = *rmap_list;
		if ((rmap_item->address & PAGE_MASK) < slot->address)
		{
			*rmap_list = rmap_item->rmap_list;
			//remove_rmap_item_from_tree(rmap_item);
		}
	}

	if ( *rmap_list && (rmap_item->address & PAGE_MASK) == slot->address)
		return rmap_item;

	rmap_item = alloc_rmap_item();
	if (rmap_item) {
		rmap_item->mm = slot->mm;
		rmap_item->address = slot->address;
		rmap_item->rmap_list = *rmap_list;
		*rmap_list = rmap_item;
	}

	return rmap_item;
}

static struct rmap_item *scan_get_next_rmap_item_f0pages(struct page **page)
{
	struct mm_struct *mm;
	struct mm_slot *slot;
	struct vm_area_struct *vma;
	struct rmap_item *rmap_item;
	unsigned long page_sum;
	void *addr;

again:
	if (list_empty(&sksm_mm_head.mm_list))
		return NULL;

	slot = sksm_scan.mm_slot;
	if (slot==&sksm_mm_head) // restart ...
	{
		
		lru_add_drain_all();
		
		root_unstable_tree = RB_ROOT;
		output("reset root_unstable_tree.");
		sksm_scan.seqnr++;

		spin_lock(&sksm_mmlist_lock);
		slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		sksm_scan.mm_slot = slot;
		spin_unlock(&sksm_mmlist_lock);

		if (slot == &sksm_mm_head)
			return NULL;
	} // end of the case of restarting.
	
	mm = slot->mm;
	down_read(&mm->mmap_sem);	
	if (ksm_test_exit(mm)) {   // the process has exited.
		vma = NULL;
		slot->address = 0;
	} else {
		vma = find_vma(mm, slot->address);
	}

	for (; vma; vma = vma->vm_next)
	{
		if (!is_mergeable_vma(vma))
			continue;
		vma->vm_flags |= VM_MERGEABLE;
		if (slot->address < vma->vm_start)
			slot->address = vma->vm_start;

		while (slot->address < vma->vm_end) {
			*page = follow_page(vma, slot->address, FOLL_GET);
			if (IS_ERR_OR_NULL(*page)){
				slot->address += PAGE_SIZE;
				cond_resched();
				continue;
			}
			addr = kmap_atomic(*page);
			page_sum = simple_page_sum(addr);
			kunmap_atomic(addr);
			//if ( 0 == page_sum || /*0x3fffffffc00 == page_sum || */ 
			if ((PageAnon(*page) || page_trans_compound_anon(*page)) 
				&& is_f0_page(*page))
			{
				flush_anon_page(vma, *page, slot->address);
				flush_dcache_page(*page);
				rmap_item = get_next_rmap_item(slot);
			
				if (rmap_item) {
					rmap_item->oldchecksum = (u16)page_sum;	
					slot->address += PAGE_SIZE;
				} else
					put_page(*page);	
				up_read(&mm->mmap_sem);
				return rmap_item;
			}
			put_page(*page);
			slot->address += PAGE_SIZE;
			cond_resched();
		}
	}

	reset_mm_slot_address(slot);
	
	spin_lock(&sksm_mmlist_lock);
	if (ksm_test_exit(mm)){
		hlist_del(&slot->link);
		list_del(&slot->mm_list);
		sksm_scan.mm_slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		spin_unlock(&sksm_mmlist_lock);
		remove_trailing_rmap_items(&slot->rmap_list);
		free_mm_slot(slot);
		slot = sksm_scan.mm_slot;
		mmdrop(mm);
	} else {
		// when reach here, we get no rmap_items to this mm_slot. so, walk to the next mm_slot
		slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		sksm_scan.mm_slot = slot;
		spin_unlock(&sksm_mmlist_lock);
	}
	
	up_read(&mm->mmap_sem);
		
	if(slot != &sksm_mm_head )
		goto again;  // now let's go to the next mm_slot.

	output("Exit scan_get_next_rmap_item_f0pages.\n");

	return NULL;
}

// the caller must make sure the mm->mmap_sem has been taken.
/*static void vma_node_do_sampling(struct vma_node *vma_node)
{
	int i, sample_count;
	int page_index, hit_count;
	u16 *mem;
	void *addr;
	struct page *page;
	unsigned long page_address;

	int size_of_pages = ((vma_node->end - vma_node->start) >> 12 );
	output("vma_node %lx size_of_pages %d\n", (unsigned long)vma_node, size_of_pages);

	// There are records of the last run of vma_node_do_sampling.
	if (vma_node->samples)
	{
		u16 old_check_sum, new_check_sum;
		struct rmap_item **item, *new, *sentinel;
		item = &vma_node->rmap_list;
		hit_count = 0;
		//output("sample_len: %ld\n", vn->sample_len);
		for ( i = 0; i < vma_node->sample_len; i++ )
		{
			page_index = vma_node->samples[i] & 0x0000ffff;	
			old_check_sum = ((vma_node->samples[i] & 0xffff0000)>>16);
			page_address = vma_node->start + page_index * PAGE_SIZE;
			page = follow_page(vma_node->vma, page_address, FOLL_GET);	
			if (IS_ERR_OR_NULL(page))
				continue;

			addr = kmap_atomic(page);
			new_check_sum = crc16_checksum(addr, PAGE_SIZE);	
			kunmap_atomic(addr);
			put_page(page);
			if (new_check_sum == old_check_sum) {
				hit_count++;
					
				while (*item && (*item)->address < page_address) 
				{
					struct rmap_item *ri;
					ri = *item;
					// The following logic finds if a rmap_item has been left over for too long.
					// So, we determine that this rmap_item is unlikely to been merged in the future.
					if (ri && (ri->address & UNSTABLE_FLAG) && !(ri->address & STABLE_FLAG))
					{
						char seqnr = (ri->address & SEQNR_MASK);
						if (seqnr - sksm_scan.seqnr >= 1) 
						{
							*item = ri->rmap_list;			
							free_rmap_item(ri);	
							output("rmap_item %lx has been evicted.\n", (unsigned long)ri);
							hit_count--;
							continue;
						}
					}
					item = &(*item)->rmap_list;
				}

				if ( (*item) && (*item)->address == page_address)
				{
					//output("Got a equal rmap_item.");
					if ( (*item)->address & STABLE_FLAG )
						hit_count--;
					continue;
				}

				// create rmap_item ....
				new = alloc_rmap_item();	
				if (NULL == new)
				{
					output("alloc_rmap_item failed.\n");		
				}
				new->mm = vma_node->vma->vm_mm;
				new->address = page_address;
				if(*item == NULL)
				{
					*item = new;
					item = &new->rmap_list;
					continue;
				}
				else if((*item)->address > page_address) {
					sentinel = *item;
					*item = new;
					new->rmap_list = sentinel;
					item = &new->rmap_list;
				} 
			} // end of if (new_check_sum == old_check_sum) {
		}
		if (hit_count >= 3*vma_node->sample_len/5 && vma_node->sample_coefficient <= 250)
			vma_node->sample_coefficient += 5;
		else // if ( hit_count < vma_node->sample_len/3 )
			vma_node->sample_coefficient -= 5;
		if (vma_node->sample_coefficient < 3)
			vma_node->sample_coefficient = 3;
		output("sample_coefficient: %d", vma_node->sample_coefficient);	
		kfree(vma_node->samples);
		vma_node->samples = NULL;
		vma_node->sample_len = 0;
	}

	mem = kmalloc(size_of_pages*2, GFP_KERNEL);
	if (!mem) {
		printk(KERN_EMERG"[%s] kmalloc(%d) failed.\n", __func__, size_of_pages*2);
		return;
	}
	//output("size_of_pages %d\n", size_of_pages);
	for (i = 0; i < size_of_pages; i++)
		mem[i] = i;
	// how many sample page is going to be checked.
	sample_count = size_of_pages * vma_node->sample_coefficient / 255;	
	if (sample_count < 3 && size_of_pages < 15)
		sample_count = 3;
	if (0 == sample_count)
		sample_count = 1;
	output("sample_count. %d\n", sample_count);
	for ( i = 0; i < sample_count; i++ )
	{
		u16 tmp;
		int idx = random32() % size_of_pages;	
		tmp = mem[i];
		mem[i] = mem[idx];
		mem[idx] = tmp;
	}
	// now, the first sample_count value of mem is the chosen random page indexs.
	vma_node->samples = kmalloc(sample_count*4, GFP_KERNEL);
	if (!vma_node->samples) {
		printk(KERN_EMERG"[%s] kmalloc(%d) failed.\n", __func__, sample_count*4);
		return;
	}
	//output("vma_node->samples %lx\n", vma_node->samples);
	memset(vma_node->samples, 0, sample_count*4);
	vma_node->sample_len = sample_count;
	for ( i = 0; i < sample_count; i++ ) {
		vma_node->samples[i] = mem[i];
	}
	kfree(mem);

	// sort it ~~ and calculate the checksum.
	quicksort(vma_node->samples, 0, vma_node->sample_len-1);
	for ( i = 0; i < vma_node->sample_len; i++ )
	{
		u16 check_sum;
		page_index = *(vma_node->samples + i) & 0x0000ffff;	
		page_address = vma_node->start + page_index * PAGE_SIZE;
		page = follow_page(vma_node->vma, page_address, FOLL_GET);	
		if (IS_ERR_OR_NULL(page))
			continue;
		addr = kmap_atomic(page);
		check_sum = crc16_checksum(addr, PAGE_SIZE);	
		kunmap_atomic(addr);
		put_page(page);
		vma_node->samples[i] |= (check_sum << 16);
	}
}
*/

static void vma_node_do_sampling(struct vma_node *vma_node)
{
	int pages_count, sample_count;
	int gap_len;
	int left/*include*/, right/*exclude*/;
	int index;
	unsigned long address, addr;
	struct rmap_item **item;
	struct rmap_item *new;
	struct page *page;

	BUG_ON(0 == vma_node->coefficient);
	pages_count = (vma_node->end - vma_node->start) >> 12;
	sample_count = pages_count * vma_node->coefficient / 100;
	if (3 > sample_count)
		sample_count = 3;
	gap_len = pages_count / sample_count ;
	left = right = 0;
	item = &vma_node->rmap_list;

	/*if (vma_node->coefficient < 100){
		output("return immediately.\n");
		//goto __e;
		return;
	}*/

	while (1)
	{
		left = right;	
		right = left + gap_len;
		if ( right > pages_count ) {
			output("break out: right:%d pages_count:%d\n", right, pages_count);
			break;
		}

		index = left + random32() % gap_len;
	//	output("left: %d, right: %d, hit: %d\n", left, right, index);
		address = vma_node->start + (index << 12);
		
		while (*item && ((*item)->address & PAGE_MASK) < address)
		{
			addr = (*item)->address;
			// smaller then the current sample and it's not in stable_tree.
			if(!(addr & STABLE_FLAG)) 
			{
				char seqnr = (addr & SEQNR_MASK);
				if ( !(addr & UNSTABLE_FLAG) || seqnr - sksm_scan.seqnr >= 1) 
				{
					struct rmap_item *ri = *item;
					output("Ask: %lx, but %lx now\n", (unsigned long)address, (unsigned long)addr);
					*item = ri->rmap_list;			 
					remove_rmap_item_from_tree(ri);
					free_rmap_item(ri);	
					//output("rmap_item %lx has been evicted.\n", (unsigned long)ri);
					continue;
				}

			}
			item = &(*item)->rmap_list;
		}

		if (*item) {
			addr = ((*item)->address & PAGE_MASK);
			if (addr == address) {
				item = &(*item)->rmap_list;
				continue;
			}
		}

		new = alloc_rmap_item();	
		if (NULL == new)
		{
			output("alloc_rmap_item failed.\n");		
			continue;
		}
		new->mm = vma_node->vma->vm_mm;
		new->address = address;
		if (*item)
			new->rmap_list = (*item)->rmap_list;
		else
			new->rmap_list = NULL;
		page = follow_page(vma_node->vma, address, FOLL_GET);	
		if (!IS_ERR_OR_NULL(page))
		{
			void *a;
			a = kmap_atomic(page);
			new->oldchecksum = crc16_checksum(a, PAGE_SIZE);	
			kunmap_atomic(a);
			put_page(page);
		}
		*item = new;
		item = &new->rmap_list;

		//output("push new address %lx\n", (unsigned long)address);
	}
			
	if (1 < vma_node->coefficient)
		vma_node->coefficient--;

	// for debug's purpose.
	if ( vma_node->rmap_list )
	{
		int nr = 0;
		struct rmap_item *item = vma_node->rmap_list;
		while ( item ){
			nr++;
			item = item->rmap_list;
		}
		output("vma %lx pages_count: %d rmap_items_count: %d coefficient: %d\n",
			 (unsigned long)vma_node->vma, pages_count, nr, vma_node->coefficient);
	}
	
}

static void sksm_do_recruit(unsigned int nr)
{
	struct mm_slot *slot;
	struct mm_struct *mm;
	struct vm_area_struct *vma;

	if (list_empty(&sksm_mm_head.mm_list))
		return;
		
	slot = sksm_scan.mm_slot;

	while (nr-- && likely(!freezing(current)))
	{
		if (slot==&sksm_mm_head)
		{
			spin_lock(&sksm_mmlist_lock);
			slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
			spin_unlock(&sksm_mmlist_lock);
		}

		if (slot == &sksm_mm_head){
			return;
		}

		mm = slot->mm;

		down_read(&mm->mmap_sem);
		// At current only one postion in ksmd is responsible to free mm_slot.
		// Return imediately, so let it have the chance sooner.
		if (ksm_test_exit(mm)) 
		{
			up_read(&mm->mmap_sem);
			return;
		}
		for (vma = mm->mmap; vma; vma = vma->vm_next)
		{
			if (is_mergeable_vma(vma)) {
				insert_vma_node(slot, vma);
			}
		}
		up_read(&mm->mmap_sem);
	
		spin_lock(&sksm_mmlist_lock);
		slot = list_entry(slot->mm_list.next, struct mm_slot, mm_list);
		spin_unlock(&sksm_mmlist_lock);
	}
} 
/**
 * sksm_do_scan  - the ksm scanner main worker function.
 * @scan_npages - number of pages we want to scan before we return.
 */
static void sksm_do_scan(unsigned int scan_npages)
{
	struct rmap_item *rmap_item;
	struct page *uninitialized_var(page);

	rmap_item = NULL;
	while (scan_npages && likely(!freezing(current))) {
		cond_resched();
		if ( sksm_run != SKSM_RUN_F0PAGES_ONLY) {
			rmap_item = scan_get_next_rmap_item(&page);
		} else {
			rmap_item = scan_get_next_rmap_item_f0pages(&page);
		}
		if  (rmap_item) 
			 output("rmap_item: %lx\n", (unsigned long)rmap_item);
		if (!rmap_item) {
			scan_npages--;
			return;
		}
		if (!PageKsm(page) || !in_stable_tree(rmap_item)) {
			output("Before entering cmp_and_merge_page.\n");
			cmp_and_merge_page(page, rmap_item);
			scan_npages--;
		}
		put_page(page);
	}
}

static int sksmd_should_run(void)
{
//	return (sksm_run & SKSM_RUN_MERGE) && !list_empty(&sksm_mm_head.mm_list);
	if ( sksm_run == SKSM_RUN_MERGE || sksm_run == SKSM_RUN_F0PAGES_ONLY )
		return 1;
	else
		return 0;
}

static int sksm_scan_thread(void *nothing)
{
	int err;
	unsigned int counter;
	struct mm_slot *slot;

	set_freezable();
	set_user_nice(current, 5);

	counter = 0;
	
	output("Enter into sksm_scan_thread.\n");

	while (!kthread_should_stop()) {
		output("Before mutex_lock.\n");
		mutex_lock(&sksm_thread_mutex);
		if (sksmd_should_run()) {
			if (sksm_run != SKSM_RUN_F0PAGES_ONLY)   
			{
				walk_through_tasks();
				sksm_do_recruit(ksm_thread_processes_to_recruit);
				sksm_do_scan(ksm_thread_pages_to_scan);
			}
			else
			{
				walk_through_tasks();
				sksm_do_scan(ksm_thread_pages_to_scan);
			}
			output("###### Heart beat ...\n");
		}
		mutex_unlock(&sksm_thread_mutex);
		
		try_to_freeze();

		if (sksmd_should_run()) {
			output("sksmd_should_run returns 1.\n");
			schedule_timeout_interruptible(
				msecs_to_jiffies(sksm_thread_sleep_millisecs));
		} else {
			output("wait_event_freezable.\n\n");
			wait_event_freezable(sksm_thread_wait,
				sksmd_should_run() || kthread_should_stop());
		}
	} // end of while loop
	//preempt_disable();
	print_the_stable_tree();
	//preempt_enable();
	err = unmerge_and_remove_all_rmap_items(sksm_run != SKSM_RUN_F0PAGES_ONLY);
	if (err) {
		output("unmerge_and_remove_all_rmap_items() returns %d.\n", err);
		while (1)
		{
			spin_lock(&sksm_mmlist_lock);
			slot = list_entry(sksm_mm_head.mm_list.next, struct mm_slot, mm_list);
			spin_unlock(&sksm_mmlist_lock);

			if (slot == &sksm_mm_head)
				break;
			down_read(&slot->mm->mmap_sem);
			nuke_mm_slot(slot, sksm_run != SKSM_RUN_F0PAGES_ONLY);
			up_read(&slot->mm->mmap_sem);
			mmdrop(slot->mm);
		}
	}

	return 0;
}

/*static int sksm_scan_thread(void *nothing)
{
	do {
		set_current_state(TASK_INTERRUPTIBLE);
		schedule_timeout(sksm_thread_sleep_millisecs); 
		output("works.\n");		
		if (kthread_should_stop())
			break;
	} while (!kthread_should_stop());

	return 0;
}*/

int ksm_madvise(struct vm_area_struct *vma, unsigned long start,
		unsigned long end, int advice, unsigned long *vm_flags)
{
	struct mm_struct *mm = vma->vm_mm;
	int err;
	// just ignore the advice.
	return 0;

	switch (advice) {
	case MADV_MERGEABLE:
		/*
		 * Be somewhat over-protective for now!
		 */
		if (*vm_flags & (VM_MERGEABLE | VM_SHARED  | VM_MAYSHARE   |
				 VM_PFNMAP    | VM_IO      | VM_DONTEXPAND |
				 VM_RESERVED  | VM_HUGETLB | VM_INSERTPAGE |
				 VM_NONLINEAR | VM_MIXEDMAP | VM_SAO))
			return 0;		/* just ignore the advice */

		if (!test_bit(MMF_VM_MERGEABLE, &mm->flags)) {
			err = __ksm_enter(mm);
			if (err)
				return err;
		}

		*vm_flags |= VM_MERGEABLE;
		break;

	case MADV_UNMERGEABLE:
		if (!(*vm_flags & VM_MERGEABLE))
			return 0;		/* just ignore the advice */

		if (vma->anon_vma) {
			err = unmerge_ksm_pages(vma, start, end);
			if (err)
				return err;
		}

		*vm_flags &= ~VM_MERGEABLE;
		break;
	}

	return 0;
}

static int task_ksm_enter(struct task_struct *task)
{
	struct mm_struct *mm;
	struct mm_slot *mm_slot;

	mm = task->mm;	
	if (task->mm == NULL)
		return 1;
	if (test_bit(MMF_VM_MERGEABLE, &mm->flags))
		return 1;
	
	mm_slot = alloc_mm_slot();	
	if (!mm_slot) {
		output("alloc_mm_slot failed.\n");
		return -ENOMEM;
	}
	
	spin_lock(&sksm_mmlist_lock);
	insert_to_mm_slots_hash(mm, mm_slot);
	list_add_tail(&mm_slot->mm_list, &sksm_scan.mm_slot->mm_list);
	set_bit(MMF_VM_MERGEABLE, &mm->flags);
	atomic_inc(&mm->mm_count);   // we have to get a reference count to this mm.
	spin_unlock(&sksm_mmlist_lock);
	
	output("track a new task. mm: %lx.\n", (unsigned long)mm);
	
	return 0;
}

struct page *ksm_does_need_to_copy(struct page *page,
			struct vm_area_struct *vma, unsigned long address)
{
	struct page *new_page;

	new_page = alloc_page_vma(GFP_HIGHUSER_MOVABLE, vma, address);
	if (new_page) {
		copy_user_highpage(new_page, page, address, vma);

		SetPageDirty(new_page);
		__SetPageUptodate(new_page);
		SetPageSwapBacked(new_page);
		__set_page_locked(new_page);

		if (page_evictable(new_page, vma))
			lru_cache_add_lru(new_page, LRU_ACTIVE_ANON);
		else
			add_page_to_unevictable_list(new_page);
	}

	return new_page;
}

int page_referenced_ksm(struct page *page, struct mem_cgroup *memcg,
			unsigned long *vm_flags)
{
	struct stable_node *stable_node;
	struct rmap_item *rmap_item;
	struct hlist_node *hlist;
	unsigned int mapcount = page_mapcount(page);
	int referenced = 0;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return 0;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct anon_vma_chain *vmac;
		struct vm_area_struct *vma;

		anon_vma_lock(anon_vma);
		list_for_each_entry(vmac, &anon_vma->head, same_anon_vma) {
			vma = vmac->vma;
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			if (memcg && !mm_match_cgroup(vma->vm_mm, memcg))
				continue;

			referenced += page_referenced_one(page, vma,
				rmap_item->address, &mapcount, vm_flags);
			if (!search_new_forks || !mapcount)
				break;
		}
		anon_vma_unlock(anon_vma);
		if (!mapcount)
			goto out;
	}
	if (!search_new_forks++)
		goto again;
out:
	return referenced;
}

int try_to_unmap_ksm(struct page *page, enum ttu_flags flags)
{
	struct stable_node *stable_node;
	struct hlist_node *hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return SWAP_FAIL;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct anon_vma_chain *vmac;
		struct vm_area_struct *vma;

		anon_vma_lock(anon_vma);
		list_for_each_entry(vmac, &anon_vma->head, same_anon_vma) {
			vma = vmac->vma;
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			ret = try_to_unmap_one(page, vma,
					rmap_item->address, flags);
			if (ret != SWAP_AGAIN || !page_mapped(page)) {
				anon_vma_unlock(anon_vma);
				goto out;
			}
		}
		anon_vma_unlock(anon_vma);
	}
	if (!search_new_forks++)
		goto again;
out:
	return ret;
}

#ifdef CONFIG_MIGRATION
int rmap_walk_ksm(struct page *page, int (*rmap_one)(struct page *,
		  struct vm_area_struct *, unsigned long, void *), void *arg)
{
	struct stable_node *stable_node;
	struct hlist_node *hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return ret;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct anon_vma_chain *vmac;
		struct vm_area_struct *vma;

		anon_vma_lock(anon_vma);
		list_for_each_entry(vmac, &anon_vma->head, same_anon_vma) {
			vma = vmac->vma;
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			ret = rmap_one(page, vma, rmap_item->address, arg);
			if (ret != SWAP_AGAIN) {
				anon_vma_unlock(anon_vma);
				goto out;
			}
		}
		anon_vma_unlock(anon_vma);
	}
	if (!search_new_forks++)
		goto again;
out:
	return ret;
}

void ksm_migrate_page(struct page *newpage, struct page *oldpage)
{
	struct stable_node *stable_node;

	VM_BUG_ON(!PageLocked(oldpage));
	VM_BUG_ON(!PageLocked(newpage));
	VM_BUG_ON(newpage->mapping != oldpage->mapping);

	stable_node = page_stable_node(newpage);
	if (stable_node) {
		VM_BUG_ON(stable_node->kpfn != page_to_pfn(oldpage));
		stable_node->kpfn = page_to_pfn(newpage);
	}
}
#endif /* CONFIG_MIGRATION */

#ifdef CONFIG_MEMORY_HOTREMOVE
static struct stable_node *ksm_check_stable_tree(unsigned long start_pfn,
						 unsigned long end_pfn)
{
	struct rb_node *node;

	for (node = rb_first(&root_stable_tree); node; node = rb_next(node)) {
		struct stable_node *stable_node;

		stable_node = rb_entry(node, struct stable_node, node);
		if (stable_node->kpfn >= start_pfn &&
		    stable_node->kpfn < end_pfn)
			return stable_node;
	}
	return NULL;
}

static int ksm_memory_callback(struct notifier_block *self,
			       unsigned long action, void *arg)
{
	struct memory_notify *mn = arg;
	struct stable_node *stable_node;

	switch (action) {
	case MEM_GOING_OFFLINE:
		/*
		 * Keep it very simple for now: just lock out ksmd and
		 * MADV_UNMERGEABLE while any memory is going offline.
		 * mutex_lock_nested() is necessary because lockdep was alarmed
		 * that here we take sksm_thread_mutex inside notifier chain
		 * mutex, and later take notifier chain mutex inside
		 * sksm_thread_mutex to unlock it.   But that's safe because both
		 * are inside mem_hotplug_mutex.
		 */
		mutex_lock_nested(&sksm_thread_mutex, SINGLE_DEPTH_NESTING);
		break;

	case MEM_OFFLINE:
		/*
		 * Most of the work is done by page migration; but there might
		 * be a few stable_nodes left over, still pointing to struct
		 * pages which have been offlined: prune those from the tree.
		 */
		while ((stable_node = ksm_check_stable_tree(mn->start_pfn,
					mn->start_pfn + mn->nr_pages)) != NULL)
			remove_node_from_stable_tree(stable_node);
		/* fallthrough */

	case MEM_CANCEL_OFFLINE:
		mutex_unlock(&sksm_thread_mutex);
		break;
	}
	return NOTIFY_OK;
}
#endif /* CONFIG_MEMORY_HOTREMOVE */

#ifdef CONFIG_SYSFS
/*
 * This all compiles without CONFIG_SYSFS, but is a waste of space.
 */

#define KSM_ATTR_RO(_name) \
	static struct kobj_attribute _name##_attr = __ATTR_RO(_name)
#define KSM_ATTR(_name) \
	static struct kobj_attribute _name##_attr = \
		__ATTR(_name, 0644, _name##_show, _name##_store)

static ssize_t sleep_millisecs_show(struct kobject *kobj,
				    struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", sksm_thread_sleep_millisecs);
}

static ssize_t sleep_millisecs_store(struct kobject *kobj,
				     struct kobj_attribute *attr,
				     const char *buf, size_t count)
{
	unsigned long msecs;
	int err;

	err = strict_strtoul(buf, 10, &msecs);
	if (err || msecs > UINT_MAX)
		return -EINVAL;

	sksm_thread_sleep_millisecs = msecs;

	return count;
}
KSM_ATTR(sleep_millisecs);

static ssize_t pages_to_scan_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", ksm_thread_pages_to_scan);
}

static ssize_t pages_to_scan_store(struct kobject *kobj,
				   struct kobj_attribute *attr,
				   const char *buf, size_t count)
{
	int err;
	unsigned long nr_pages;

	err = strict_strtoul(buf, 10, &nr_pages);
	if (err || nr_pages > UINT_MAX)
		return -EINVAL;

	ksm_thread_pages_to_scan = nr_pages;

	return count;
}
KSM_ATTR(pages_to_scan);

static ssize_t run_show(struct kobject *kobj, struct kobj_attribute *attr,
			char *buf)
{
	return sprintf(buf, "%u\n", sksm_run);
}

static ssize_t run_store(struct kobject *kobj, struct kobj_attribute *attr,
			 const char *buf, size_t count)
{
	int err;
	unsigned long flags, old_flags;

	err = strict_strtoul(buf, 10, &flags);
	if (err || flags > UINT_MAX)
		return -EINVAL;
	if (flags > SKSM_RUN_UNMERGE)
		return -EINVAL;

	/*
	 * SKSM_RUN_MERGE sets ksmd running, and 0 stops it running.
	 * SKSM_RUN_UNMERGE stops it running and unmerges all rmap_items,
	 * breaking COW to free the pages_shared (but leaves mm_slots
	 * on the list for when ksmd may be set running again).
	 */

	mutex_lock(&sksm_thread_mutex);
	if (sksm_run != flags) {
		old_flags = sksm_run;
		sksm_run = flags;
		if (flags & SKSM_RUN_UNMERGE) {
			int oom_score_adj;

			oom_score_adj = test_set_oom_score_adj(OOM_SCORE_ADJ_MAX);
			print_the_stable_tree();
			err = unmerge_and_remove_all_rmap_items(old_flags != SKSM_RUN_F0PAGES_ONLY);
			test_set_oom_score_adj(oom_score_adj);
			if (err) {
				sksm_run = SKSM_RUN_STOP;
				count = err;
			}
		}

		if (flags & SKSM_RUN_F0PAGES_ONLY)
		{
			err = unmerge_and_remove_all_rmap_items(old_flags != SKSM_RUN_F0PAGES_ONLY);
			count = err;
		}
	}
	mutex_unlock(&sksm_thread_mutex);

	if (flags & SKSM_RUN_MERGE)
		wake_up_interruptible(&sksm_thread_wait);

	return count;
}
KSM_ATTR(run);

static ssize_t rmap_items_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_rmap_items);
}
KSM_ATTR_RO(rmap_items);

static ssize_t pages_shared_show(struct kobject *kobj,
				 struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_shared);
}
KSM_ATTR_RO(pages_shared);

static ssize_t pages_sharing_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_sharing);
}
KSM_ATTR_RO(pages_sharing);

static ssize_t pages_unshared_show(struct kobject *kobj,
				   struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_unshared);
}
KSM_ATTR_RO(pages_unshared);

static ssize_t pages_volatile_show(struct kobject *kobj,
				   struct kobj_attribute *attr, char *buf)
{
	long ksm_pages_volatile;

	ksm_pages_volatile = ksm_rmap_items - ksm_pages_shared
				- ksm_pages_sharing - ksm_pages_unshared;
	/*
	 * It was not worth any locking to calculate that statistic,
	 * but it might therefore sometimes be negative: conceal that.
	 */
	if (ksm_pages_volatile < 0)
		ksm_pages_volatile = 0;
	return sprintf(buf, "%ld\n", ksm_pages_volatile);
}
KSM_ATTR_RO(pages_volatile);

static ssize_t full_scans_show(struct kobject *kobj,
			       struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", sksm_scan.seqnr);
}
KSM_ATTR_RO(full_scans);

static ssize_t processes_to_scan_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	struct process_to_scan *pts;
	int count;
	count = 0;
	list_for_each_entry(pts, &processes_to_scan_head, list)
	{
		count += sprintf(buf + count, "%s\n", pts->comm);
	}
	return count;
}
static ssize_t processes_to_scan_store(struct kobject *kobj,
				   struct kobj_attribute *attr,
				   const char *buf, size_t count)
{
	char op;
	char comm[64];
	int exist;
	int len;
	struct process_to_scan *pts;

	sscanf(buf, "%c %s", &op, comm);
	output("%c %s\n", op, comm);
	len = strlen(comm);
	
	spin_lock(&processes_to_scan_lock);
	exist = process2scan_exist(comm);
	output("Exist %d\n", exist);
	if (op == '+' && !exist)
	{
		pts = alloc_process_to_scan();
		pts->comm = kmalloc(len+1, GFP_KERNEL);
		if (!pts->comm) {
			free_process_to_scan(pts);
			goto _err;
		}
		strcpy(pts->comm, comm);	
		list_add(&pts->list, &processes_to_scan_head);
		goto _out;
	}
	else if (op == '-' && exist)
	{
		list_for_each_entry(pts, &processes_to_scan_head, list)
		{
			if (0 == strcmp(comm, pts->comm)) 
			{
				list_del(&pts->list);
				kfree(pts->comm);
				free_process_to_scan(pts);
				output("remove okay.\n");
				goto _out;
			}
		}
		goto _err;
	}

_out:
	spin_unlock(&processes_to_scan_lock);
	return count;
_err:
	spin_unlock(&processes_to_scan_lock);
	return -EINVAL;
}
KSM_ATTR(processes_to_scan);

static struct attribute *sksm_attrs[] = {
	&sleep_millisecs_attr.attr,
	&pages_to_scan_attr.attr,
	&run_attr.attr,
	&rmap_items_attr.attr,
	&pages_shared_attr.attr,
	&pages_sharing_attr.attr,
	&pages_unshared_attr.attr,
	&pages_volatile_attr.attr,
	&full_scans_attr.attr, 
	&processes_to_scan_attr.attr,
	NULL,
};

static struct attribute_group sksm_attr_group = {
	.attrs = sksm_attrs,
	.name = "sksm",
};
#endif /* CONFIG_SYSFS */

// The sksmd kernel thread.
static struct task_struct *sksm_thread;

int __init sksm_init(void)
{
	int err;

	err = sksm_slab_init();
	if (err)
		goto out;

	sksm_thread = kthread_run(sksm_scan_thread, NULL, "sksmd");
	if (IS_ERR(sksm_thread)) {
		output("kthread_run failed !!!");
		err = PTR_ERR(sksm_thread);
		goto out_free;
	}
	output("kthread_run ok !!!");

	err = sysfs_create_group(mm_kobj, &sksm_attr_group);
	if (err) {
		output("sksm: register sysfs failed !!!\n");
		kthread_stop(sksm_thread);
		goto out_free;
	}

	return 0;

out_free:
	sksm_slab_free();
out:
	return err;
}

void __exit sksm_exit(void)
{
	kthread_stop(sksm_thread);
	sysfs_remove_group(mm_kobj, &sksm_attr_group);
	destroy_processes_to_scan();
	sksm_slab_free();
}

module_init(sksm_init)
module_exit(sksm_exit);
MODULE_LICENSE("GPL");
