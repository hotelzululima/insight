	.include "x86_32-simulator-header.s"
start:
	mov $0x0B0B, %ax
	add $0, %ax	# to reset AF flags.
	aaa
	jnb error # CF should be 1
	cmp $0x01, %al
	jne error
	cmp $0x0C, %ah
	jne error


	add $0x0, %eax 	# to reset AF flags.
	mov $0x0B15, %ax
	aaa
	jb error	
	cmp $0x05, %al
	jne error
	cmp $0x0B, %ah
	jne error

	.include "x86_32-simulator-end.s"
