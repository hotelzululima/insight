.section .text
.globl main

main:
	jmp	.+0x6
	.long	0xdeadbeef
	mov	(0x2), %eax
	add	$0xa, %eax
