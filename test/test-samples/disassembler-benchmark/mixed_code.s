.section .text
.globl main

main:
	jmp	.+0x4
	.long	0xdeadbeef
	add	$10, (.-0x4)
