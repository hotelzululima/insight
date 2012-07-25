	.include "x86_32-simulator-header.s"
	
start:
	# RCR 8 bits test
	mov	$0x12345678, %eax	
	stc	

	rcr	%ah
	jc	error
	jno	error
	cmp 	$0xAB, %ah
	jne	error

	rcr	$3, %ah
	jc	error
	cmp 	$0xD5, %ah
	jne	error

	rcr	$9, %ah # should have no effect
	jc	error
	cmp 	$0xD5, %ah
	jne	error

	rcr	$8, %ah
	jnc	error
	cmp 	$0xAA, %ah
	jne	error

	# RCR 16 bits test
	stc		
	rcr	%ax
	jc	error
	jo	error
	cmp 	$0xD53C, %ax
	jne	error

	rcr	$3, %ax
	jnc	error
	cmp 	$0x1AA7, %ax
	jne	error

	stc
	rcr	$17, %ax # should have no effect
	jnc	error
	cmp 	$0x1AA7, %ax
	jne	error

	stc
	rcr	$16, %ax
	jc	error
	cmp 	$0x354F, %ax
	jne	error

	# RCR 32 bits test 
	stc		
	rcr	%eax
	jnc	error
	jno	error
	cmp 	$0x891A1AA7, %eax
	jne	error
	
	rcr	$3, %eax
	jnc	error
	cmp 	$0xD1234354, %eax
	jne	error

	stc
	rcr	$32, %eax # should have no effect
	jnc	error
	cmp 	$0xD1234354, %eax
	jne	error	
	
	.include "x86_32-simulator-end.s"
	