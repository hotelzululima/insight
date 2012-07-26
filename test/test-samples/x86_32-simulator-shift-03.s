	.include "x86_32-simulator-header.s"
	
start:
	# 8 bits SAR
	mov	$0x2DE3AD7B, %eax	
	sar	%ah
	jnc	error
	cmp	$0xD6, %ah
	jne	error
	
	sar	$3, %ah
	jnc	error
	cmp	$0xFA, %ah
	jne	error

	stc			# restore CF that has been reset by cmp
	sar	$32, %ah	# should have no effect
	jnc	error
	cmp	$0xFA, %ah
	jne	error

	sar	$9, %ah	
	jnc	error
	cmp	$0xFF, %ah
	jne	error

	# 16 bits SAR
	mov	$0x2DE3AD7B, %eax
	sar	%ax
	jnc	error
	cmp	$0xd6bd, %ax
	jne	error
	
	sar	$3, %ax
	jnc	error
	cmp	$0xfad7, %ax
	jne	error

	stc			# restore CF that has been reset by cmp
	sar	$32, %ax	# should have no effect
	jnc	error
	cmp	$0xfad7, %ax
	jne	error
	
	sar	$9, %ax		
	jc	error
	cmp	$0xFFFD, %ax
	jne 	error

	# 32 bits SAR	
	mov	$0x2DE3AD7B, %eax

	sar	%eax
	jnc	error
	cmp	$0x16f1d6bd, %eax
	jne	error
	
	sar	$3, %eax
	jnc	error
	cmp	$0x2de3ad7, %eax
	jne	error

	stc			# restore CF that has been reset by cmp	
	sar	$32, %eax	# should have no effect
	jnc	error
	cmp	$0x2de3ad7, %eax
	jne	error
	
	sar	$9, %eax		
	jc	error
	cmp	$0x16f1d, %eax
	jne 	error
	
	.include "x86_32-simulator-end.s"
