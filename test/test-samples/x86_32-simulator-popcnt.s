	.include "x86_32-simulator-header.s"
	
start:
	mov	$0x12345678, %ebx
	popcnt	%ebx, %eax
	jz	error
	jc	error
	jp	error
	jo	error
	js	error
	cmp	$13, %eax
	jne 	error

	popcnt	%bx, %ax
	jz	error
	jc	error
	jp	error
	jo	error
	js	error
	cmp	$8, %eax
	jne 	error
	
	.include "x86_32-simulator-end.s"
