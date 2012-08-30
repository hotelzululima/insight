.section .text
.globl main

main:
	movl	0xbbc10300, %eax
	movl	0x05000000, %ecx
	add	%ecx, %eax
	jmp	*-10(%eip)
	add	%ebx, %eax
	ret
