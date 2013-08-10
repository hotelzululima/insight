	.include "x86_64-simulator-header.s"

	mov	$0x10, %cx
	mov	$0x0, %ax

loop1:
	inc	%ax
	loop	loop1

	cmp	$0x10, %ax
	jne	error

loop2:
	dec	%ax	
	loopne	loop2

	test    %ax, %ax
	jne	error
	cmp   	$-0x10, %cx
	jne	error

	mov	$0x10, %ecx
	mov	$0x0, %eax

loop3:
	inc	%eax
	loop	loop3

	cmp	$0x10, %eax
	jne	error

loop4:
	dec	%eax	
	loopne	loop4

	test    %eax, %eax
	jne	error
	cmp   	$-0x10, %ecx
	jne	error
	
	.include "x86_64-simulator-end.s"
