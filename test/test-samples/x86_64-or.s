	## OR imm8, AL
	or $0x12, %al
	
	## OR imm16, AX
	or $0x1234, %ax
	
	## OR imm32, EAX
	or $0x12345678, %eax
	
	## OR imm8, r/m8
	or $0x12, %bh
	orb $0x12, 0x11011972

	## OR imm16 , r/m16
	or $0x1234, %bx
	orw $0x1234, 0x11011972
	
	## OR imm32 , r/m32
	or $0x12345678, %ebx
	orl $0x12345678, 0x11011972
	
	## OR imm8 , r/m16
	or $0x12, %ax
	orb $0x12, 0x11011972
	
	## OR imm8 , r/m32
	or $0x12, %eax
	orb $0x12, 0x11011972
	
	## OR r8, r/m8
	or %bh, %cl
	or %ch, 0x11011972	

	## OR r16, r/m16
	or %bx, %cx
	or %cx, 0x11011972	

	## OR r32	, r/m32
	or %ebx, %ecx
	or %ecx, 0x11011972
	
	## OR r/m8, r8
	or %bh, %cl
	or 0x11011972, %ch

	## OR r/m16, r16
	or %bx, %cx
	or 0x11011972, %cx
	
	## OR r/m32, r32
	or %ebx, %ecx
	or 0x11011972, %ecx
