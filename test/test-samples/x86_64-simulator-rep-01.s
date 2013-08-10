	.set	INIT_EFLAGS, 1
	.include "x86_64-simulator-header.s"
	
start:
	cld
	mov	$0x1111, %edi
	mov	$0x78563412, %eax
	stosl
	mov	$0xF0DEBC9A, %eax
	stosl
	
	mov	$0x8, %cx
	mov	$0x1111, %esi
	mov	$0x2222, %edi
	rep	movsb

	mov	$0x2222, %esi
	lodsl
	cmp	$0x78563412, %eax
	jne	error
	lodsl
	cmp	$0xF0DEBC9A, %eax
	jne  	error
	
	.include "x86_64-simulator-end.s"
