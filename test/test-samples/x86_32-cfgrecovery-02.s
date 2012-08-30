start:
	mov	$func,	%edi
	mov 	$2,	%ebx
loop:
	call	0x12345
	sub	$1,	%ebx
	jnz	loop
	call	*%edi
	hlt
	.	= 0x19
func:	
	call	0x12345
	ret
	