	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"
start:
	mov $1, %ah
	push %ax		# push 2 bytes
	pop %bx			# pop 2 bytes 
	cmp %bx, %ax
	jne error

	.include "x86_64-simulator-end.s"
