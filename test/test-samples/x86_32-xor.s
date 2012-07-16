	## XOR imm8, AL
	xor $0x12, %al
	
	## XOR imm16, AX
	xor $0x1234, %ax
	
	## XOR imm32, EAX
	xor $0x12345678, %eax
	
	## XOR imm8, r/m8
	xor $0x12, %bh
	xorb $0x12, 0x11011972

	## XOR imm16 , r/m16
	xor $0x1234, %bx
	xorw $0x1234, 0x11011972
	
	## XOR imm32 , r/m32
	xor $0x12345678, %ebx
	xorl $0x12345678, 0x11011972
	
	## XOR imm8 , r/m16
	xor $0x12, %ax
	xorb $0x12, 0x11011972
	
	## XOR imm8 , r/m32
	xor $0x12, %eax
	xorb $0x12, 0x11011972
	
	## XOR r8, r/m8
	xor %bh, %cl
	xor %ch, 0x11011972	

	## XOR r16, r/m16
	xor %bx, %cx
	xor %cx, 0x11011972	

	## XOR r32	, r/m32
	xor %ebx, %ecx
	xor %ecx, 0x11011972
	
	## XOR r/m8, r8
	xor %bh, %cl
	xor 0x11011972, %ch

	## XOR r/m16, r16
	xor %bx, %cx
	xor 0x11011972, %cx
	
	## XOR r/m32, r32
	xor %ebx, %ecx
	xor 0x11011972, %ecx
