start:
	mov	$func,	%edi
	mov 	$100,	%ebx
loop:
	sub	$1,	%ebx
	jnz	loop
	call	*%edi
	hlt
	.	= 0x19
func:	
	call	0x12345
	ret
	
