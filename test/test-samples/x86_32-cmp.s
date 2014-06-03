 	/* cmp imm8, AL Compare imm8 with AL. */
	cmp $0x12, %al

	/* cmp imm16, AX  Compare imm16 with AX. */
	cmp $0x1234, %ax
	
	/* cmp imm32, EAX Compare imm32 with EAX. */
	cmp $0x12345678, %eax
	
	/* cmp imm8, r/m8 Compare imm8 with r/m8. */
	cmp $0x12, %bl
	cmpb $0x12, -100(%eax)
	
	/* cmp imm16, r/m16 Compare imm16 with imm16 r/m16. */
	cmp $0x12, %bx
	cmpw $0x12, -100(%eax)
	
	/* cmp imm32, r/m32 Compare imm32 with imm32 r/m32. */
	cmp $0x12, %ebx
	cmpl $0x12, -100(%eax)
	
	/* cmp imm8, r/m16 Compare imm8 with r/m16. */
	cmp $0x12, %bx
	cmpw $0x1234, -100(%eax)
	
	/* cmp imm8, r/m32 Compare imm8 with r/m32. */
	cmp $0x12, %ebx
	cmpl $0x12345678, -100(%eax)
	
	/* cmp r8, r/m8 Compare r8 with r/m8. */
	cmp %cl, %bl
	cmpb %cl, -100(%eax)

	/* cmp r16, r/m16 Compare r16 with r/m16. */
	cmp %cx, %bx
	cmpw %cx, -100(%eax)

	/* cmp r32, r/m32 Compare r32 with r/m32. */
	cmp %ecx, %ebx
	cmpl %ecx, -100(%eax)
	
	/* cmp r/m8, r8 Compare r/m8 with r8. */
	cmp %dl, %bl
	cmpb -100(%eax), %bl

	/* cmp r/m16, r16 Compare r/m16 with r16. */
	cmp %dx, %bx
	cmpw -100(%eax), %bx

	/* cmp r/m32, r32 Compare r/m32 with r32. */
	cmp %edx, %ebx
	cmpl -100(%eax), %ebx
	