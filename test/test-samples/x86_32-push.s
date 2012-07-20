	## PUSH r/m16
	push %ax
	pushw 0x31415926
	
	## ## PUSH r/m32
	push %eax
	push 0x31415926
	
	## ## PUSH r16
	push %bp

	## ## PUSH r32
	push %esp
	
	## ## PUSH imm8
	push $0xF1

	## ## PUSH imm16
	push $0x3141
	pushw $0x3141

	## ## PUSH imm32
	push $0x31415926
	pushl $0x31415926
	
	## ## PUSH {CS,SS,DS,ES,FS,GS}
	push %cs
	push %ss
	push %ds
	push %ds
	push %fs
	push %gs

	pushw %cs
	pushw %ss
	pushw %ds
	pushw %ds
	pushw %fs
	pushw %gs

	