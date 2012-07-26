	.include "x86_32-simulator-header.s"
	
start:
	# 8 bits SHR
	mov	$0x2DE3AD7B, %eax	
	shr	%ah
	jnc	error
	cmp	$0x56, %ah
	jne	error

	shr	$3, %ah
	jnc	error
	cmp	$0x0A, %ah
	jne	error

	stc			# restore CF that has been reset by cmp
	shr	$32, %ah	# should have no effect
	jnc	error
	cmp	$0x0A, %ah
	jne	error

	shr	$9, %ah	
	jc	error
	cmp	$0x00, %ah
	jne	error

	# 16 bits SHR
	mov	$0x2DE3AD7B, %eax
	shr	%ax
	jnc	error
	cmp	$0x56bd, %ax
	jne	error

	shr	$3, %ax
	jnc	error
	cmp	$0x0ad7, %ax
	jne	error

	stc			# restore CF that has been reset by cmp
	shr	$32, %ax	# should have no effect
	jnc	error
	cmp	$0x0ad7, %ax
	jne	error

	shr	$9, %ax		
	jc	error
	cmp	$0x5, %ax
	jne 	error

	# 32 bits SHR	
	mov	$0x2DE3AD7B, %eax

	shr	%eax
	jnc	error
	cmp	$0x16f1d6bd, %eax
	jne	error

	shr	$3, %eax
	jnc	error
	cmp	$0x2de3ad7, %eax
	jne	error

	stc			# restore CF that has been reset by cmp	
	shr	$32, %eax	# should have no effect
	jnc	error
	cmp	$0x2de3ad7, %eax
	jne	error

	shr	$9, %eax		
	jc	error
	cmp	$0x16f1d, %eax
	jne 	error
	
	.include "x86_32-simulator-end.s"
