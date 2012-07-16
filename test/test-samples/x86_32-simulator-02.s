	# Check CF 
	.include "x86_32-simulator-header.s"
start:
	mov $0xFFFFFFFF, %eax
	add $1, %eax
	jnb error

	je ok
	jmp error

	.include "x86_32-simulator-end.s"
