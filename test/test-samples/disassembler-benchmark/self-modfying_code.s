.section .text
.globl main

main:
	xor	%eax, %eax
loop:
	cmp	$10, %eax
	inc	%eax
	jne	.+0xb
	movw	$0x9090, (.+0x9)
	jmp	loop
	ret

	
