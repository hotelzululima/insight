	# JMP rel8 A Valid Valid Jump short,
	# RIP = RIP + 8-bit displacement sign extended to 64-bits
	jmp  0x12
	jmpq *0x12
	
	# JMP rel16 A N.S. Valid Jump near, relative, displacement
	# relative to next instruction. Not supported in 64-bit mode.
	jmp  0x1234
	jmpq *0x1234
	
	# JMP rel32 A Valid Valid Jump near, relative,
	# RIP = RIP + 32-bit displacement sign extended to 64-bits
	jmp  -0x12345678
	
	# JMP r/m16 B N.S. Valid Jump near, absolute indirect,
	# address = zero-extended r/m16. Not supported in 64-bit mode.	
	jmp *%ax
	jmp *0x12345678
	
	# JMP r/m32 B N.S. Valid Jump near, absolute indirect,
	# address given in r/m32. Not supported in 64-bit mode.
	jmp  *%rax
	jmpq *%rax
	jmp  *0x12345678
	jmpq *0x12345678
	
	# JMP ptr16:16 A Inv. Valid Jump far, absolute,
	# address given in operand
	
	# JMP ptr16:32 A Inv. Valid Jump far, absolute,
	# address given in operand
	
	# JMP m16:16 A Valid Valid Jump far, absolute indirect,
	# address given in m16:16
	
	# JMP m16:32 A Valid Valid Jump far, absolute indirect,
	# address given in m16:32.
