	.include "x86_64-simulator-header.s"
	
	mov	$0, %cx
	mov	$0x1, %ax

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	clc
	bt	%cx, %ax
	jnb	error
	shl	%ax
	inc	%cx

	.include "x86_64-simulator-end.s"
	