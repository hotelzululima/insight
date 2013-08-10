	.include "x86_64-simulator-header.s"
	
	mov	$0, %cx
	mov	$0xFFFF, %ax
loop:
	clc
	btr	%cx, %ax
	jnb	error
	inc	%cx
	cmp	$16, %cx
	jne	loop
	cmp	$0x0, %ax
	jne	error

	.include "x86_64-simulator-end.s"
