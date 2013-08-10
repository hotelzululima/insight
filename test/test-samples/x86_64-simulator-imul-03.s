	#
	# Test third form of signed multiplication
	#
	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"
start:
	# 16 bits operands
	mov 	$0x1111, %bx
	imul	$0x1111, %bx, %cx
	call	chk1	
	cmp	$0x4321, %cx
	jne	error

	mov	$0x1234, %bx
	imul	$0x3, %bx, %cx
	call	chk0	
	cmp	$0x369C, %cx
	jne	error
	
	mov 	%cx, %bx
	imul	$0xFD, %bx, %cx
	call	chk1	
	cmp	$0x5C2C, %cx
	jne	error

	mov	$0xF234, %bx
	imul	$0xFD, %bx, %cx
	call	chk0	
	cmp	$0x2964, %cx
	jne	error

	# 32 bits operands
	mov 	$0x11111111, %ebx
	imul	$0x11111111, %ebx, %ecx
	call	chk1	
	cmp	$0x87654321, %ecx
	jne	error

	mov	$0x12345678, %ebx
	imul	$0x00000003, %ebx, %ecx
	call	chk0	
	cmp	$0x369d0368, %ecx
	jne	error

	mov	%ecx, %ebx
	imul	$0xFFFFFFFD, %ebx, %ecx
	call	chk1	
	cmp	$0x5C28F5C8, %ecx
	jne	error

	mov 	$0xFFFFFFFD, %ebx
	imul	$0xF2345678, %ebx, %ecx
	call	chk0	
	cmp	$0x2962fc98, %ecx
	jne	error
	
	.include "x86_64-simulator-end.s"

chk1:
	jnc	error
	jno	error
	ret

chk0:
	jc	error
	jo	error
	ret
	