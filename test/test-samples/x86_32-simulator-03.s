	# Check OF
	.include "x86_32-simulator-header.s"
start:
	mov $0x8A000000, %eax
	add $0x8A000000, %eax
	jo ok
	jmp error

	.include "x86_32-simulator-end.s"
