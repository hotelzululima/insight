	.include "x86_32-simulator-header.s"
	
start:
	# ROL 8 bits test
	mov	$0x12345678, %eax	

	rol	%ah
	jc	error
	jno	error
	cmp 	$0xAC, %ah
	jne	error

	rol	$3, %ah
	jnc	error
	cmp 	$0x65, %ah
	jne	error

	rol	$9, %ah # should have effect of rol $1, %ah
	jc	error
	cmp 	$0xCA, %ah
	jne	error

	rol	$8, %ah # should have no effect
	jc	error
	cmp 	$0xCA, %ah
	jne	error

	# ROL 16 bits test
	rol	%ax
	jnc	error
	jno	error
	cmp 	$0x94F1, %ax
	jne	error

	rol	$3, %ax
	jc	error
	cmp 	$0xA78C, %ax
	jne	error

	rol	$17, %ax # should have effect of rol $1, %ax
	jnc	error
	cmp 	$0x4F19, %ax
	jne	error

	rol	$16, %ax # should have no effect
	jnc	error
	cmp 	$0x4F19, %ax
	jne	error

	# ROL 32 bits test
	rol	%eax
	jc	error
	jo	error
	cmp 	$0x24689e32, %eax
	jne	error

	rol	$3, %eax
	jnc	error
	cmp 	$0x2344f191, %eax
	jne	error

	rol	$33, %eax # should have effect of rol $1, %eax
	jc	error
	cmp 	$0x4689e322, %eax
	jne	error

	rol	$32, %eax # should have no effect
	jc	error
	cmp 	$0x4689e322, %eax
	jne	error

	.include "x86_32-simulator-end.s"
	