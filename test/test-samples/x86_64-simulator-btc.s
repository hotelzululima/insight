	.include "x86_64-simulator-header.s"
	
	mov	$0, %cx
	mov	$0xFFFF, %ax
	mov	$0xFFFF, %bx
loop:
	clc
	btc	%cx, %ax
	jnb	error
	shl	%bx
	cmp	%bx, %ax
	jne	error
	inc	%cx
	cmp	$16, %cx
	jne	loop
	test	%ax, %ax
	jne	error

	.include "x86_64-simulator-end.s"
	