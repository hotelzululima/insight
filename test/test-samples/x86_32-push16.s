	## PUSH r/m16
	push %ax
	data16 push 0x31415926
	
	## PUSH r/m32
	data16 push %eax
	data16 push 0x31415926
	
	## PUSH r16
	push %bp

	## PUSH r32
	data16 push %esp
	
	## PUSH imm8
	data16 push $0x31
	## PUSH imm16
	data16 push $0x3141
	## PUSH imm32
	data16 push $0x31415926
	
	## PUSH {CS,SS,DS,ES,FS,GS}
	data16 push %cs
	data16 push %ss
	data16 push %ds
	data16 push %ds
	data16 push %fs
	data16 push %gs

	