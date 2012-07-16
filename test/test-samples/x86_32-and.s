	## AND imm8, AL
	and $0x12, %ah
	
	## AND imm16, AX
	and $0x1234, %ax
	
	## AND imm32, EAX
	and $0x12345678, %eax
	
	## AND imm8, r/m8
	and $0x12, %bh
	andb $0x12, 0x11011972

	## AND imm16 , r/m16
	and $0x1234, %bx
	andw $0x1234, 0x11011972
	
	## AND imm32 , r/m32
	and $0x12345678, %ebx
	andl $0x12345678, 0x11011972
	
	## AND imm8 , r/m16
	and $0x12, %ax
	andb $0x12, 0x11011972
	
	## AND imm8 , r/m32
	and $0x12, %eax
	andb $0x12, 0x11011972
	
	## AND r8, r/m8
	and %bh, %cl
	and %ch, 0x11011972	

	## AND r16, r/m16
	and %bx, %cx
	and %cx, 0x11011972	

	## AND r32	, r/m32
	and %ebx, %ecx
	and %ecx, 0x11011972
	
	## AND r/m8, r8
	and %bh, %cl
	and 0x11011972, %ch

	## AND r/m16, r16
	and %bx, %cx
	and 0x11011972, %cx
	
	## AND r/m32, r32
	and %ebx, %ecx
	and 0x11011972, %ecx
