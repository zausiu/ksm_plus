ifneq ($(KERNELRELEASE),)
	obj-m := sksm.o
else
	KERNELDIR ?= /lib/modules/`uname -r`/build/
	PWD := $(shell pwd)

default:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

endif
