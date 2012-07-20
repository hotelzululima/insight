	.include "x86_32-simulator-header.s"

start:
	movl	$0x12345678, 0x10
	movbe	0x10, %eax
	cmp 	$0x78563412, %eax
	jne 	error

	movl	%eax, 0x10
	cmpl 	$0x12345678, 0x10
	mov	$0, %eax
	movbe	0x10, %ax
	cmp 	$0x1234, %ax
	jne 	error

	movl	$0x12345678, %eax
	movbe	%eax, 0x10
	cmpl 	$0x78563412, 0x10
	jne 	error

	movl	0x10, %eax
	cmp 	$0x12345678, %eax
	movl	$0, 0x10
	movbe	%ax, 0x10
	cmpw 	$0x1234, 0x10
	jne 	error
	
	
	.include "x86_32-simulator-end.s"
