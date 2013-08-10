	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"
	
start:
	push	$0x0
	popf
	mov	$0x53, %ah
	sahf
	pushf
	mov	$0xFF, %ah
	sahf
	popf
	lahf
	cmp	$0x53, %ah
	jne 	error

	mov	$0x53, %ah
	sahf
	pushfw
	mov	$0xFF, %ah
	sahf
	popfw
	lahf
	cmp	$0x53, %ah
	jne 	error


	.include "x86_64-simulator-end.s"
