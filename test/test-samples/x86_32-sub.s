	/* SUB imm8, AL -- Subtract imm8 from AL. */
	sub $0x12, %al
	
	/* SUB imm16, AX -- Subtract imm16 from AX. */
	sub $0x1234, %ax
	
	/* SUB imm32, EAX -- Subtract imm32 from EAX. */
	sub $0x12345678, %eax
	
	/* SUB imm8, r/m8 -- Subtract imm8 from r/m8. */
	sub $0x12, %bl
	subb $0x12, -100(%eax,%ebx,4)
	
	/* SUB imm16, r/m16 -- Subtract imm16 from r/m16. */
	sub $0x1234, %bx
	subw $0x1234, -100(%eax,%ebx,4)
	
	/* SUB imm32, r/m32 -- Subtract imm32 from r/m32. */
	sub $0x12345678, %ebx
	subl $0x12345678, -100(%eax,%ebx,4)
	
	/* SUB imm8, r/m16 -- Subtract sign-extended imm8 from r/m16. */
	sub $0x12, %bx
	subw $0x12, -100(%eax,%ebx,4)

	/* SUB imm8, r/m32 -- Subtract sign-extended imm8 from r/m32. */
	sub $0x12, %ebx
	subl $0x12, -100(%eax,%ebx,4)
	
	/* SUB r8, r/m8 -- Subtract r8 from r/m8. */
	sub %ch, %bl
	sub %ch, -100(%eax,%ebx,4)

	/* SUB r16, r/m16 -- Subtract r16 from r/m16. */
	sub %cx, %bx
	sub %cx, -100(%eax,%ebx,4)
	
	/* SUB r32, r/m32 -- Subtract r32 from r/m32. */
	sub %ecx, %ebx
	sub %ecx, -100(%eax,%ebx,4)

	/* SUB r/m8, r8 -- Subtract r/m8 from r8. */
	sub %ch, %bl
	sub -100(%eax,%ebx,4), %bl

	/* SUB r/m16, r16 -- Subtract r/m16 from r16. */
	sub %cx, %bx
	sub -100(%eax,%ebx,4), %bx
	
	/* SUB r/m32, r32 -- Subtract r/m32 from r32. */
	sub %ecx, %ebx
	sub -100(%eax,%ebx,4), %ebx
