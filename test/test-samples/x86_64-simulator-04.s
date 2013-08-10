	# Check CF 
	.include "x86_64-simulator-header.s"
start:
	mov $0xFFFFFFFF, %eax
	add $1, %eax
	jnb error

	mov $10, %eax
	adc $9, %eax
	cmp $20, %eax
	je ok
	jmp error

	.include "x86_64-simulator-end.s"
