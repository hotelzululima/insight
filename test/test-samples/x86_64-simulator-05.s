	# Check CF
	.include "x86_64-simulator-header.s"
start:
	mov $0x0, %ebx
	testl %ebx, %ebx
	je ok
	jmp error

	.include "x86_64-simulator-end.s"
