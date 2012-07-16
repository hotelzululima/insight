	.set	EXCEPTION_CHECK, 1
	.include "x86_32-simulator-header.s"

start:	
	movw 	$-3, 0x10
	movw 	$5, 0x12
	mov 	$1, %bx
	bound	%bx, 0x10
	mov 	$6, %bx
	bound	%bx, 0x10	

	.include "x86_32-simulator-end.s"
