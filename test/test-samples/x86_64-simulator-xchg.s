	.include "x86_64-simulator-header.s"
start:
	mov	$0x12345678, %eax
	xchg	%ah, %al
	cmp	$0x12347856, %eax
	jne 	error

	movl	$0xFEDCBA98, 0x2222
	xchg	0x2222, %ax
	cmp	$0x1234BA98, %eax
	jne 	error
	cmpl 	$0xFEDC7856, 0x2222
	jne	error

	xchg	%eax, 0x2222
	cmp	$0xFEDC7856, %eax
	jne 	error
	cmpl 	$0x1234BA98, 0x2222
	jne	error
	
	.include "x86_64-simulator-end.s"
