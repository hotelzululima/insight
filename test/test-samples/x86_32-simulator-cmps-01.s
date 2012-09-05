	.include "x86_32-simulator-header.s"
start:
	cld
	movl	$0x12345678, 0x11111
	movl	$0x12345678, 0x22222
	mov	$0x11111, %esi
	mov	$0x22222, %edi

	cmpsb
	jne	error
	cmpsb
	jne	error
	cmpsb
	jne	error
	cmpsb
	jne	error

	mov	$0x11111, %esi
	mov	$0x22222, %edi
	cmpsw
	jne	error
	cmpsw
	jne	error

	mov	$0x11111, %esi
	mov	$0x22222, %edi
	cmpsd
	jne	error
	
	.include "x86_32-simulator-end.s"
