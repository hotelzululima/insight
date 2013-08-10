	.include "x86_64-simulator-header.s"
start:
	xor	%eax, %eax
	mov	$0x87,	%al
	cmp	$0x00000087, %eax
	jne	error
	cbw
	cmp	$0x0000FF87, %eax
	jne	error
	cwde
	cmp	$0xFFFFFF87, %eax
	jne	error

	.include "x86_64-simulator-end.s"
