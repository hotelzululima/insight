	.set	USE_STACK, 1	
	.include "x86_32-simulator-header.s"
	
start:
	mov	$0x1, %eax
	mov	$0x2, %ebx
	mov	$0x3, %ecx
	mov	$0x4, %edx
	mov	$0x5, %ebp
	mov	$0x6, %edi
	mov	$0x7, %esi
	pusha
	mov	$0xF1, %eax
	mov	$0xF2, %ebx
	mov	$0xF3, %ecx
	mov	$0xF4, %edx
	mov	$0xF5, %ebp
	mov	$0xF6, %edi
	mov	$0xF7, %esi
	popa
	cmp	$0x1, %eax
	jne	error
	cmp	$0x2, %ebx
	jne	error
	cmp	$0x3, %ecx
	jne	error	
	cmp	$0x4, %edx
	jne	error	
	cmp	$0x5, %ebp
	jne	error	
	cmp	$0x6, %edi
	jne	error	
	cmp	$0x7, %esi
	jne	error	

	.include "x86_32-simulator-end.s"
