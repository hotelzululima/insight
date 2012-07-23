	.include "x86_32-simulator-header.s"
start:
	mov	$0x12345678, %eax
	xchg	%ah, %al
	cmp	$0x12347856, %eax
	jne 	error
	
	.include "x86_32-simulator-end.s"
