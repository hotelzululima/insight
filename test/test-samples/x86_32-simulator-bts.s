	.include "x86_32-simulator-header.s"
	
	mov	$0, %cx
	mov	$0x0, %ax
loop:
	clc
	bts	%cx, %ax
	jb	error
	inc	%cx
	cmp	$16, %cx
	jne	loop
	cmp	$0xFFFF, %ax
	jne	error

	.include "x86_32-simulator-end.s"
