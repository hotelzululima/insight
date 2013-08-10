start:
	mov	$func,	%rdi
	mov 	$100,	%rbx
loop:
	sub	$1,	%rbx
	jnz	loop
	callq	*%rdi
	hlt
	.	= 0x19
func:	
	callq	0x12345
	retq
	
