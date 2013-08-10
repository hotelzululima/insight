	.include "x86_64-simulator-header.s"
start:
	mov 	$0x12345678, %eax
	mov 	$0x00031415, %ebx
	mov	$0x99990078, %ecx
	
	cmpxchg	%bh, %ch
	je	error
	test	%al, %al
	jne 	error

	cmpxchg	%bx, %cx
	je	error
	cmp	$0x78, %ax
	jne 	error

	.include "x86_64-simulator-end.s"
