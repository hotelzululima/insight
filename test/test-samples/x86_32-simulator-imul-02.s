	#
	# Test second form of signed multiplication
	# Same operands than first form but we replace [e]ax by [e]cx.
	# References [e]dx are removed because the register is not used
	# by this form
	#
	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"

start:
	# 16 bits operands
	mov 	$0x1111, %cx
	mov 	%cx, %bx
	imul	%bx, %cx
	call	chk1	
	cmp	$0x4321, %cx
	jne	error

	mov	$0x1234, %cx
	mov 	$0x3, %bx
	imul	%bx, %cx
	call	chk0	
	cmp	$0x369C, %cx
	jne	error
	
	mov 	$0xFFFD, %bx
	imul	%bx, %cx
	call	chk1	
	cmp	$0x5C2C, %cx
	jne	error

	mov	$0xF234, %cx
	mov 	$0xFFFD, %bx
	imul	%bx, %cx
	call	chk0	
	cmp	$0x2964, %cx
	jne	error

	# 32 bits operands
	mov 	$0x11111111, %ecx
	mov 	%ecx, %ebx
	imul	%ebx, %ecx
	call	chk1	
	cmp	$0x87654321, %ecx
	jne	error

	mov	$0x12345678, %ecx
	mov 	$0x3, %ebx
	imul	%ebx, %ecx
	call	chk0	
	cmp	$0x369d0368, %ecx
	jne	error

	mov 	$0xFFFFFFFD, %ebx
	imul	%ebx, %ecx
	call	chk1	
	cmp	$0x5C28F5C8, %ecx
	jne	error

	mov	$0xF2345678, %ecx
	mov 	$0xFFFFFFFD, %ebx
	imul	%ebx, %ecx
	call	chk0	
	cmp	$0x2962fc98, %ecx
	jne	error
	
	.include "x86_32-simulator-end.s"

chk1:
	jnc	error
	jno	error
	ret

chk0:
	jc	error
	jo	error
	ret
	