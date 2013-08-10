	.include "x86_64-simulator-header.s"
	
start:
	# 8 bits SAL
	mov	$0x2DE3AD7B, %eax	
	sal	%ah
	jnc	error
	cmp	$0x5A, %ah
	jne	error
	
	sal	$3, %ah
	jc	error
	cmp	$0xD0, %ah
	jne	error

	sal	$32, %ah	# should have no effect
	jc	error
	cmp	$0xD0, %ah
	jne	error

	sal	$9, %ah	
	jc	error
	cmp	$0x00, %ah
	jne	error

	# 16 bits SAL
	mov	$0x2DE3AD7B, %eax
	sal	%ax
	jnc	error
	cmp	$0x5af6, %ax
	jne	error
	
	sal	$3, %ax
	jc	error
	cmp	$0xd7b0, %ax
	jne	error

	sal	$32, %ax	# should have no effect
	jc	error
	cmp	$0xd7b0, %ax
	jne	error
	
	sal	$9, %ax		
	jnc	error
	cmp	$0x6000, %ax
	jne 	error
	
	# 32 bits SAL	
	mov	$0x2DE3AD7B, %eax

	sal	%eax
	jc	error
	cmp	$0x5bc75af6, %eax
	jne	error
	
	sal	$3, %eax
	jc	error
	cmp	$0xde3ad7b0, %eax
	jne	error

	sal	$32, %eax	# should have no effect
	jc	error
	cmp	$0xde3ad7b0, %eax
	jne	error
	
	sal	$9, %eax		
	jc	error
	cmp	$0x75af6000, %eax
	jne 	error
	
	.include "x86_64-simulator-end.s"
