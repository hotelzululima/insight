	mov 12(%esp), %eax
	mov %eax, %ecx
	mov 8(%esp), %ebx
label:  movb $0x33, (%ebx)
	inc %ebx
	dec %ecx
	jnz label
	ret
