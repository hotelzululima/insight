	.include "x86_64-simulator-header.s"
	
start:
	# RCL 8 bits test
	mov	$0x12345678, %eax	
	stc	

	rcl	%ah
	jc	error
	jno	error
	cmp 	$0xAD, %ah
	jne	error

	rcl	$3, %ah
	jnc	error
	cmp 	$0x6A, %ah
	jne	error

	rcl	$9, %ah # should have no effect
	jc	error
	cmp 	$0x6A, %ah
	jne	error

	rcl	$8, %ah
	jc	error
	cmp 	$0x35, %ah
	jne	error

	# RCL 16 bits test
	stc		
	rcl	%ax
	jc	error
	jo	error
	cmp 	$0x6AF1, %ax
	jne	error

	rcl	$3, %ax
	jnc	error
	cmp 	$0x5789, %ax
	jne	error

	stc
	rcl	$17, %ax # should have no effect
	jnc	error
	cmp 	$0x5789, %ax
	jne	error

	stc
	rcl	$16, %ax
	jnc	error
	cmp 	$0xABC4, %ax
	jne	error

	# RCL 32 bits test 
	stc		
	rcl	%eax
	jc	error
	jo	error
	cmp 	$0x24695789, %eax
	jne	error
	
	rcl	$3, %eax
	jnc	error
	cmp 	$0x234ABC48, %eax
	jne	error

	stc
	rcl	$32, %eax # should have no effect
	jnc	error
	cmp 	$0x234ABC48, %eax
	jne	error	

	.include "x86_64-simulator-end.s"
	