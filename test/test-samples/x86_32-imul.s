	imul 	%bh
	imulb 	0x12345678
	imul 	%bx
	imulw 	0x12345678
	imul 	%ebx
	imull 	0x12345678

	imul 	%bx, %cx
	imulw 	0x12345678, %cx
	imul 	%ebx, %ecx
	imull 	0x12345678, %ecx

	imul 	$0x10, %bx, %cx
	imulw 	$0x10, 0x12345678, %cx
	imul 	$0x10, %ebx, %ecx
	imull 	$0x10, 0x12345678, %ecx

	imul 	$0x1010, %bx, %cx
	imulw 	$0x1010, 0x12345678, %cx

	imul 	$0x10101010, %ebx, %ecx
	imull 	$0x10101010, 0x12345678, %ecx
	
	