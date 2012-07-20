	.include "x86_32-simulator-header.s"

	.set	SF,	0x80
	.set	ZF,	0x40
	.set	AF,	0x10
	.set	PF,	0x04
	.set	CF,	0x01
	
	# set CF	
	mov	$0xFF, %cl
	add	$0x5, %cl
	jnb	error
	lahf
	cmp	$0x3, %ah
	jne	error
	cmp	$0x04, %cl
	jne	error
	
	# set PF
	inc	%cl
	jnp	error
	lahf
	cmp	$0x6, %ah
	jne	error

	# set AF
	cmp	$0x05, %cl
	jne	error
	add	$0x2D, %cl
	lahf
	cmp	$0x12, %ah
	jne	error

	# set ZF
	cmp	$0x32, %cl
	jne	error
	add	$0xCE, %cl
	jnz	error
	lahf
	cmp	$0x47, %ah
	jne	error

	# set ZF
	add	$0x80, %cl
	jns	error
	lahf
	cmp	$0x82, %ah
	jne	error

	mov	$SF, %ah
	sahf
	jns	error

	mov	$ZF, %ah
	sahf
	jnz	error


	mov	$AF, %ah	
	mov	$0x0, %al
	sahf
	aaa
	jnc	error
	cmp	$0x6, %al
	jne	error
	cmp	$0x11, %ah
	jne	error

	mov	$PF, %ah
	sahf
	jnp	error

	mov	$CF, %ah
	sahf
	jnc	error

	mov	$0x0, %ah
	sahf
	js 	error
	jp 	error
	jc 	error
	jz 	error
	
	.include "x86_32-simulator-end.s"
	