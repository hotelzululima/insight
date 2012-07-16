	.include "x86_32-simulator-header.s"
start:
	mov $5, %eax
	mov $5, %ebx

	cmp	%ebx, %eax
	je	ok
	jmp	error

	.include "x86_32-simulator-end.s"
