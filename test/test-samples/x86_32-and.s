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

	## TEST

	## TEST imm8, AL
	test $0x12, %ah
	
	## TEST imm16, AX
	test $0x1234, %ax
	
	## TEST imm32, EAX
	test $0x12345678, %eax
	
	## TEST imm8, r/m8
	test $0x12, %bh
	testb $0x12, 0x11011972

	## TEST imm16 , r/m16
	test $0x1234, %bx
	testw $0x1234, 0x11011972
	
	## TEST imm32 , r/m32
	test $0x12345678, %ebx
	testl $0x12345678, 0x11011972
	
	## TEST imm8 , r/m16
	test $0x12, %ax
	testb $0x12, 0x11011972
	
	## TEST imm8 , r/m32
	test $0x12, %eax
	testb $0x12, 0x11011972
	
	## TEST r8, r/m8
	test %bh, %cl
	test %ch, 0x11011972	

	## TEST r16, r/m16
	test %bx, %cx
	test %cx, 0x11011972	

	## TEST r32	, r/m32
	test %ebx, %ecx
	test %ecx, 0x11011972
	
	## TEST r/m8, r8
	test %bh, %cl
	test 0x11011972, %ch

	## TEST r/m16, r16
	test %bx, %cx
	test 0x11011972, %cx
	
	## TEST r/m32, r32
	test %ebx, %ecx
	test 0x11011972, %ecx
	