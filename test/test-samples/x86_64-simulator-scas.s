	.include "x86_64-simulator-header.s"
	
start:
	cld
	movl	$0x12345678, 0x1111
	mov	$0x1111, %edi
	mov	$0x79, %al
	scasb
	jng	error

	mov	$0x1111, %edi
	mov	$0x6678, %ax
	scasw
	jng	error

	scasw
	jng	error

	movl	$0x12345678, 0x1111
	mov	$0x1111, %edi
	mov	$0x79, %al
	addr32 	scasb
	jng	error

	mov	$0x1111, %edi
	mov	$0x6678, %ax
	addr32  scasw
	jng	error

	scasw
	jng	error
	
	.include "x86_64-simulator-end.s"
