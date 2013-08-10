	.include "x86_64-simulator-header.s"
	
start:
	# ROR 8 bits test
	mov	$0x12345678, %eax	

	ror	%ah
	jc	error
	jo	error
	cmp 	$0x2B, %ah
	jne	error

	ror	$3, %ah
	jc	error
	cmp 	$0x65, %ah
	jne	error

	ror	$9, %ah # should have effect of ror $1, %ah
	jnc	error
	cmp 	$0xB2, %ah
	jne	error

	ror	$8, %ah # should have no effect
	jnc	error
	cmp 	$0xB2, %ah
	jne	error

	# ROR 16 bits test
	ror	%ax
	jc	error
	jno	error
	cmp 	$0x593C, %ax
	jne	error

	ror	$3, %ax
	jnc	error
	cmp 	$0x8B27, %ax
	jne	error

	ror	$17, %ax # should have effect of ror $1, %ax
	jnc	error
	cmp 	$0xC593, %ax
	jne	error

	ror	$16, %ax # should have no effect
	jnc	error
	cmp 	$0xC593, %ax
	jne	error

	# ROR 32 bits test 
	ror	%eax
	jnc	error
	jno	error
	cmp 	$0x891a62c9, %eax
	jne	error

	ror	$3, %eax
	jc	error
	cmp 	$0x31234C59, %eax
	jne	error

	ror	$33, %eax # should have effect of ror $1, %eax
	jnc	error
	cmp 	$0x9891a62c, %eax
	jne	error

	stc 	#restore CF
	ror	$32, %eax # should have no effect
	jnc	error
	cmp 	$0x9891a62c, %eax	
	jne	error	

	.include "x86_64-simulator-end.s"
	