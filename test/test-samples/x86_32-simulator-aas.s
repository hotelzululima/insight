	.include "x86_32-simulator-header.s"
start:
	mov $0x0B0B, %ax
	add $0, %ax 	# to reset AF flags.
	aas
	jnb error # CF should be 1	
	cmp $0x05, %al
	jne error
	cmp $0x0A, %ah
	jne error

	add $0x0, %eax 	# to reset AF flags.
	mov $0x0B15, %ax
	aas
	jb error	
	cmp $0x05, %al
	jne error
	cmp $0x0B, %ah
	jne error

	.include "x86_32-simulator-end.s"
