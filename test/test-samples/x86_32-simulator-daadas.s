	.include "x86_32-simulator-header.s"
start:
	mov	$0x79, %al
	mov	$0x35, %bl
	add 	%bl, %al

	daa
	js	error
	jz	error
	jnp	error
	jnb	error	
	
	cmp	$0x14, %al
	jne 	error
	cmp	$0x35, %bl
	jne 	error

	mov	$0x79, %al
	mov	$0x35, %bl
	add 	%bl, %al
	mov	$0x2e, %al
	daa
	js	error
	jz	error
	jp	error
	jb	error	
	
	cmp	$0x34, %al
	jne 	error
	cmp	$0x35, %bl
	jne 	error

	mov	$0x35, %al
	mov	$0x47, %bl
	sub 	%bl, %al
	jo	error
	
	das
	jns	error
	jz	error
	jnp	error
	jnb	error	
	
	cmp	$0x88, %al
	jne 	error
	cmp	$0x47, %bl
	jne 	error

	.include "x86_32-simulator-end.s"
	