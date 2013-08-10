	## PUSH r/m16
	push %ax
	pushw 0x31415926
	
	## ## PUSH r/m32
	# Not supported in 64-bits
	
	## ## PUSH r/m64
	push  %rax
	pushq %rax
	pushq 0x31415926
	
	## ## PUSH r16
	push %bp

	## ## PUSH r32
	# Not supported in 64-bits
	
	## ## PUSH r64
	push  %rbp
	pushq %rbp
	
	## ## PUSH imm8
	push $0xF1

	## ## PUSH imm16
	push $0x3141
	pushw $0x3141

	## ## PUSH imm32
	push $0x31415926

	## ## PUSH imm64
	pushq $0x31415926
	
	## ## PUSH {CS,SS,DS,ES,FS,GS}
	# push %cs (not supported in 64-bits)
	# push %ss (not supported in 64-bits)
	# push %ds (not supported in 64-bits)
	# push %es (not supported in 64-bits)
	push %fs
	push %gs

	# pushw %cs (not supported in 64-bits)
	# pushw %ss (not supported in 64-bits)
	# pushw %ds (not supported in 64-bits)
	# pushw %es (not supported in 64-bits)
	pushw %fs
	pushw %gs

	
