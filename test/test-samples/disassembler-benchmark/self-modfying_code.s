.section .data

loop:
	inc	%eax
	cmp	$0xa, %eax
	jne	.+0xb
	movw	$0x9090, (.+0x9)
	jmp	loop
	ret

.section .text
.globl main

main:
	xor	%eax, %eax
	jmp	loop

	
