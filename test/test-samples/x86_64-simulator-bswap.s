	.include "x86_64-simulator-header.s"

	mov	$0x12345678, %eax
	mov	%eax, %ebx
	bswap	%eax
	cmp	$0x78563412, %eax
	jne	error
	bswap	%eax
	cmp	%eax, %ebx
	jne	error

	.include "x86_64-simulator-end.s"
	