	.include "x86_32-simulator-header.s"
	
	mov	$0, %cx

	movl	$0x1, 0x31415
	mov	$0x1, %ax
	
	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	clc
	bt	%cx, 0x31415
	jnb	error
	shlw	0x31415
	inc	%cx

	.include "x86_32-simulator-end.s"
