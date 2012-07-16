	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"

start:
	mov $0x1, %ah
	mov $0x2, %bh
	mov $0x3, %ch
	mov $0x4, %dh
	push %ax
	push %bx
	push %cx
	push %dx
	pop %ax
	pop %bx
	pop %cx
	pop %dx
	cmp $0x400, %ax
	jne error
	cmp $0x300, %bx
	jne error
	cmp $0x200, %cx
	jne error
	cmp $0x100, %dx
	jne error	
	.include "x86_32-simulator-end.s"
