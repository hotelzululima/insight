	.include "x86_64-simulator-header.s"
start:
	mov	$0x7700, %ax	
	cwd
	cmp	$0x0000, %dx
	jne	error

	mov	$0x8700, %ax	
	cwd
	cmp	$0xFFFF, %dx
	jne	error

	mov	$0x87000000, %eax
	cdq
	cmp	$0xFFFFFFFF, %edx
	jne	error

	mov	$0x77000000, %eax
	cdq
	cmp	$0x0, %edx
	jne	error
	
	.include "x86_64-simulator-end.s"
