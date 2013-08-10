start:
	mov	func,	%rdi
	mov 	$2,	%rbx
loop:
	callq	0x12345
	sub	$1,	%rbx
	jnz	loop
	callq	*%rdi
	hlt
	.	= 0x19
func:	
	callq	0x12345
	retq
	
