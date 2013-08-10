	.include "x86_64-simulator-header.s"
start:
	cld
	movl	$0x12345678, 0x11111
	movl	$0x87654321, 0x22222
	mov	$0x11111, %esi
	mov	$0x22222, %edi

	cmpsb
	je	error
	cmpsb
	je	error
	cmpsb
	je	error
	cmpsb
	je	error

	mov	$0x11111, %esi
	mov	$0x22222, %edi
	cmpsw
	je	error
	cmpsw
	je	error

	mov	$0x11111, %esi
	mov	$0x22222, %edi
	cmpsd
	je	error
	
	.include "x86_64-simulator-end.s"
