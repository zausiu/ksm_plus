ifneq ($(KERNELRELEASE),)
	obj-m := sksm.o
else
	KERNELDIR ?= /usr/src/linux/
	PWD := $(shell pwd)

default:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

endif
