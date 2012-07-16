	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"
start:
	mov $0x12345678, %eax
	push %eax
	pop %bx
	pop %cx
	cmp $0x5678, %bx
	jne error
	cmp $0x1234, %cx
	jne error

	.include "x86_32-simulator-end.s"
