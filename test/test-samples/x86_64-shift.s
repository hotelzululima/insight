#
# SHIFT OPERATORS
#

	# SAL r/m8, 1 A Valid Valid Multiply r/m8 by 2, once.
	sal $1, %bh
	salb $1, 0x12345678
	
	# SAL r/m8, CL B Valid Valid Multiply r/m8 by 2, CL times.
	sal %cl, %bh
	sal %cl, %ch
	salb %cl, 0x12345678

	# SAL r/m8, imm8 C Valid Valid Multiply r/m8 by 2, imm8 times.
	sal $3, %bh
	salb $3, 0x12345678
	
	# SAL r/m16, 1 A Valid Valid Multiply r/m16 by 2, once.
	sal  $1, %bx
	salw $1, 0x12345678
	
	# SAL r/m16, CL B Valid Valid Multiply r/m16 by 2, CL times.
	sal  %cl, %bx
	sal  %cl, %cx
	salw %cl, 0x12345678

	# SAL r/m16, imm8 C Valid Valid Multiply r/m16 by 2, imm8 times.
	sal $3, %bx
	salw $3, 0x12345678

	# SAL r/m32, 1 A Valid Valid Multiply r/m32 by 2, once.
	sal $1, %ebx
	sall $1, 0x12345678
	
	# SAL r/m32, CL B Valid Valid Multiply r/m32 by 2, CL times.
	sal  %cl, %ebx
	sal  %cl, %ecx
	sall %cl, 0x12345678

	# SAL r/m32, imm8 C Valid Valid Multiply r/m32 by 2, imm8 times.
	sal  $3, %ebx
	sal  $3, %ecx
	sall $3, 0x12345678

	# SAR r/m8, 1 A Valid Valid Multiply r/m8 by 2, once.
	sar $1, %bh
	sarb $1, 0x12345678
	
	# SAR r/m8, CL B Valid Valid Multiply r/m8 by 2, CL times.
	sar %cl, %bh
	sar %cl, %ch
	sarb %cl, 0x12345678

	# SAR r/m8, imm8 C Valid Valid Multiply r/m8 by 2, imm8 times.
	sar $3, %bh
	sarb $3, 0x12345678
	
	# SAR r/m16, 1 A Valid Valid Multiply r/m16 by 2, once.
	sar  $1, %bx
	sarw $1, 0x12345678
	
	# SAR r/m16, CL B Valid Valid Multiply r/m16 by 2, CL times.
	sar  %cl, %bx
	sar  %cl, %cx
	sarw %cl, 0x12345678

	# SAR r/m16, imm8 C Valid Valid Multiply r/m16 by 2, imm8 times.
	sar $3, %bx
	sarw $3, 0x12345678

	# SAR r/m32, 1 A Valid Valid Multiply r/m32 by 2, once.
	sar $1, %ebx
	sarl $1, 0x12345678
	
	# SAR r/m32, CL B Valid Valid Multiply r/m32 by 2, CL times.
	sar  %cl, %ebx
	sar  %cl, %ecx
	sarl %cl, 0x12345678

	# SAR r/m32, imm8 C Valid Valid Multiply r/m32 by 2, imm8 times.
	sar  $3, %ebx
	sar  $3, %ecx
	sarl $3, 0x12345678

	# SHL r/m8, 1 A Valid Valid Multiply r/m8 by 2, once.
	shl $1, %bh
	shlb $1, 0x12345678
	
	# SHL r/m8, CL B Valid Valid Multiply r/m8 by 2, CL times.
	shl %cl, %bh
	shl %cl, %ch
	shlb %cl, 0x12345678

	# SHL r/m8, imm8 C Valid Valid Multiply r/m8 by 2, imm8 times.
	shl $3, %bh
	shlb $3, 0x12345678
	
	# SHL r/m16, 1 A Valid Valid Multiply r/m16 by 2, once.
	shl  $1, %bx
	shlw $1, 0x12345678
	
	# SHL r/m16, CL B Valid Valid Multiply r/m16 by 2, CL times.
	shl  %cl, %bx
	shl  %cl, %cx
	shlw %cl, 0x12345678

	# SHL r/m16, imm8 C Valid Valid Multiply r/m16 by 2, imm8 times.
	shl $3, %bx
	shlw $3, 0x12345678

	# SHL r/m32, 1 A Valid Valid Multiply r/m32 by 2, once.
	shl $1, %ebx
	shll $1, 0x12345678
	
	# SHL r/m32, CL B Valid Valid Multiply r/m32 by 2, CL times.
	shl  %cl, %ebx
	shl  %cl, %ecx
	shll %cl, 0x12345678

	# SHL r/m32, imm8 C Valid Valid Multiply r/m32 by 2, imm8 times.
	shl  $3, %ebx
	shl  $3, %ecx
	shll $3, 0x12345678

	# SHR r/m8, 1 A Valid Valid Multiply r/m8 by 2, once.
	shr $1, %bh
	shrb $1, 0x12345678
	
	# SHR r/m8, CL B Valid Valid Multiply r/m8 by 2, CL times.
	shr %cl, %bh
	shr %cl, %ch
	shrb %cl, 0x12345678

	# SHR r/m8, imm8 C Valid Valid Multiply r/m8 by 2, imm8 times.
	shr $3, %bh
	shrb $3, 0x12345678
	
	# SHR r/m16, 1 A Valid Valid Multiply r/m16 by 2, once.
	shr  $1, %bx
	shrw $1, 0x12345678
	
	# SHR r/m16, CL B Valid Valid Multiply r/m16 by 2, CL times.
	shr  %cl, %bx
	shr  %cl, %cx
	shrw %cl, 0x12345678

	# SHR r/m16, imm8 C Valid Valid Multiply r/m16 by 2, imm8 times.
	shr $3, %bx
	shrw $3, 0x12345678

	# SHR r/m32, 1 A Valid Valid Multiply r/m32 by 2, once.
	shr $1, %ebx
	shrl $1, 0x12345678
	
	# SHR r/m32, CL B Valid Valid Multiply r/m32 by 2, CL times.
	shr  %cl, %ebx
	shr  %cl, %ecx
	shrl %cl, 0x12345678

	# SHR r/m32, imm8 C Valid Valid Multiply r/m32 by 2, imm8 times.
	shr  $3, %ebx
	shr  $3, %ecx
	shrl $3, 0x12345678
