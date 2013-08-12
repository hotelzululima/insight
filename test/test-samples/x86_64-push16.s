	## PUSH r/m16
	push %ax
	data16 push 0x31415926
	
	## PUSH r/m32
	# push %eax # Not valid in 64-bits mode
	
	## PUSH r/m64
	push  %rax
	pushq %rax
	pushq 0x31415926
	
	## PUSH r16
	push %bp

	## PUSH r32
	# push %esp # Not valid in 64-bits mode
	# data16 push %esp # Not valid in 64-bits mode

	## PUSH r64
	push %rsp
	pushq %rsp
	
	## PUSH imm8
	data16 push $0x31
	## PUSH imm16
	data16 push $0x3141
	## PUSH imm32
	# data16 push $0x31415926 # Not valid in 64-bits mode
	## PUSH imm64
	# data16 pushq $0x31415926 # Unveiled a bug in gas
	
	## PUSH {CS,SS,DS,ES,FS,GS}
	# data16 push %cs # Not valid in 64-bits mode
	# data16 push %ss # Not valid in 64-bits mode
	# data16 push %ds # Not valid in 64-bits mode
	# data16 push %ds # Not valid in 64-bits mode
	data16 push %fs
	data16 push %gs

	
