	.include "x86_64-simulator-header.s"
start:
	movw	$0x1000, 0x2222
	mov	$0x2345, %ax
	xadd	%ax, 0x2222
	cmp	$0x3345, %ax
	jne	error
	cmpw	$0x2345, 0x2222
	jne	error


	movb	$0x11, 0x2222
	mov	$0x2345, %ax
	xadd	%ah, 0x2222
	cmp	$0x34, %ah
	jne	error
	cmpb	$0x23, 0x2222
	jne	error


	movl	$0x11112222, 0x2222
	mov	$0x12345678, %eax
	xadd	%eax, 0x2222
	cmp	$0x2345789A, %eax
	jne	error
	cmpl	$0x12345678, 0x2222
	jne	error
	
	.include "x86_64-simulator-end.s"
