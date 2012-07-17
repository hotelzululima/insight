	.include "x86_32-simulator-header.s"

start:		
	mov	$0xFFFF, %ax
	add	$0, %ax
	jo	error	
	into

	.include "x86_32-simulator-end.s"
	