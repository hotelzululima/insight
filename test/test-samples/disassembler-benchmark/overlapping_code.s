.section .text
.globl main

main:
	movl	$0xbbc10300, %eax
	movl	$0x05000000, %ecx
	add	%ecx, %eax
	jmp	*(0x2)
	add	%ebx, %eax
	ret
