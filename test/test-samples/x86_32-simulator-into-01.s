	.set 	EXCEPTION_CHECK, 1
	.include "x86_32-simulator-header.s"

start:		
	mov	$0x7FFF, %ax
	imul	%ax, %ax
	jno	error	
	into

	.include "x86_32-simulator-end.s"
	