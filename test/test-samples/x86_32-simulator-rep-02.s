	.set	INIT_EFLAGS, 1
	.include "x86_32-simulator-header.s"
	
start:
	cld
	mov	$0x1111, %edi
	mov	$0xA00A, %ax
	mov	$0x8, %cx

	rep	stosw
	mov	$0x8, %cx
	mov	%cx, %ax
l1:
	dec	%ax
	cmpw	$0xA00A, 0x1111(%eax, %eax, 1)
	loop	l1
	
	
	.include "x86_32-simulator-end.s"
