	#
	# Test first form of signed multiplication
	#
	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"
start:
	# 8 bits operands
	mov 	$0x11, %al
	mov 	%al, %bl	
	imul	%bl
	call	chk1	
	cmp	$0x121, %ax
	jne	error

	mov 	$0x2, %al
	mov 	%al, %bl
	imul	%bl
	call	chk0	
	cmp	$0x4, %ax
	jne	error

	mov 	$0xFE, %bl
	imul	%bl
	call	chk1	
	cmp	$0xFFF8, %ax
	jne	error

	mov 	$0xFE, %bl
	imul	%bl
	call	chk0	
	cmp	$0x10, %ax
	jne	error

	# 16 bits operands
	mov 	$0x1111, %ax
	mov 	%ax, %bx
	imul	%bx
	call	chk1	
	cmp	$0x4321, %ax
	jne	error
	cmp	$0x123, %dx
	jne	error

	mov	$0x1234, %ax
	mov 	$0x3, %bx
	imul	%bx
	call	chk0	
	cmp	$0x369C, %ax
	jne	error
	test	%dx, %dx
	jnz	error
	
	mov 	$0xFFFD, %bx
	imul	%bx
	call	chk1	
	cmp	$0x5C2C, %ax
	jne	error
	cmp	$0xFFFF, %dx
	jne	error

	mov	$0xF234, %ax
	mov 	$0xFFFD, %bx
	imul	%bx
	call	chk0	
	cmp	$0x2964, %ax
	jne	error
	test	%dx, %dx
	jne	error	

	# 32 bits operands
	mov 	$0x11111111, %eax
	mov 	%eax, %ebx
	imul	%ebx
	call	chk1	
	cmp	$0x87654321, %eax
	jne	error
	cmp	$0x1234567, %edx
	jne	error

	mov	$0x12345678, %eax
	mov 	$0x3, %ebx
	imul	%ebx
	call	chk0	
	cmp	$0x369d0368, %eax
	jne	error
	test	%edx, %edx
	jnz	error

	mov 	$0xFFFFFFFD, %ebx
	imul	%ebx
	call	chk1	
	cmp	$0x5C28F5C8, %eax
	jne	error
	cmp	$0xFFFFFFFF, %edx
	jne	error

	mov	$0xF2345678, %eax
	mov 	$0xFFFFFFFD, %ebx
	imul	%ebx
	call	chk0	
	cmp	$0x2962fc98, %eax
	jne	error
	test	%edx, %edx
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
	