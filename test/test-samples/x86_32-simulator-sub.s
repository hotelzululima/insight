	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"
start:
	mov	$1000, %ax
	sub	$100, %ax
	call 	chk00010	

	dec	%ax		
	call 	chk00000	

	sub 	$0xFC7D, %ax
	call	chk00011
	cmp	$0x706, %ax
	jne 	error

	sub 	$0x707, %ax
	call	chk01011

	dec	%ax
	sub	$0x7FFF, %ax
	call	chk10010

	.include "x86_32-simulator-end.s"

#  oszpc
chk00000:
	jo	error
	js	error
	jz	error
	jp	error
	jc	error
	ret

chk00010:
	jo	error
	js	error
	jz	error
	jnp	error
	jc	error
	ret

chk00011:
	jo	error
	js	error
	jz	error
	jnp	error
	jnc	error
	ret

chk01011:
	jo	error
	jns	error
	jz	error
	jnp	error
	jnc	error
	ret

chk10010:
	jno	error
	js	error
	jz	error
	jnp	error
	jc	error
	ret
	