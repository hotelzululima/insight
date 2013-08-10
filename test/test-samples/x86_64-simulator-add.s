	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"
start:
	mov	$1000, %ax
	add	$100, %ax
	call 	chk00000
	inc	%ax
	call 	chk00010
	add 	$0xFBB3, %ax
	call	chk00111
	add	$0xFFFF, %ax
	call	chk01010
	add	$0x8000, %ax
	call	chk10011

	mov	$0x0000, %ax
	inc	%ax
	inc	%ax
	inc	%ax
	inc	%ax
	inc	%ax
	inc	%ax
	cmp	$0x6, %ax
	jne	error
	dec	%ax
	dec	%ax
	dec	%ax
	dec	%ax
	dec	%ax
	dec	%ax
	cmp	$0x0, %ax
	jne	error

	.include "x86_64-simulator-end.s"

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

chk00111:
	jo	error
	js	error
	jnz	error
	jnp	error
	jnc	error
	ret

chk10011:
	jno	error
	js	error
	jz	error
	jnp	error
	jnc	error
	ret

chk01010:
	jo	error
	jns	error
	jz	error
	jnp	error
	jc	error
	ret
	