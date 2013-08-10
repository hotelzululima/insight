	.include "x86_64-simulator-header.s"
start:
	mov	$0x7AB7, %ax
	mov	$0x1B, %bh
	idiv	%bh	# al = Q = 0x48B, ah = R = 0xE --> error
	cmp 	$0x7AB7, %ax
	jne 	error

	mov	$0xC45, %ax
	mov	$0x1B, %bh
	idiv	%bh	# al = Q = 0x74, ah = R = 0x9 --> ok
	cmp 	$0x0974, %ax
	jne 	error

	mov	$0xbb77, %dx
	mov	$0x5261, %ax
	mov	$0x6A2E, %bx
	idiv	%bx	# ax = Q = 0x1c3fb, dx = R = 0x2d47 --> error
	cmp 	$0x5261, %ax
	jne 	error
	cmp 	$0xbb77, %dx
	jne 	error

	mov	$0x12BF, %dx
	mov	$0x21D6, %ax
	mov	$0x6A2E, %bx
	idiv	%bx	# ax = Q = 0x2d32, dx = R = 0x4eda --> ok
	cmp 	$0x2d32, %ax
	jne 	error
	cmp 	$0x4eda, %dx
	jne 	error
	
	mov	$0x0, %edx
	mov	$0xbb775261, %eax
	mov	$0x6A2E, %ebx
	idiv	%ebx	# eax = Q = 0x1c3fb, edx = R = 0x2d47 --> ok
	cmp 	$0x1c3fb, %eax
	jne 	error
	cmp 	$0x2d47, %edx
	jne 	error
	
	.include "x86_64-simulator-end.s"
	