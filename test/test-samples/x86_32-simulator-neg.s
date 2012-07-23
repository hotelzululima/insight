	.include "x86_32-simulator-header.s"
start:
	mov	$0x00, %ah
	mov	$0x81, %bh
	mov	%bh, 0x1234

	negb	0x1234
	jnc	error
	sahf
	neg	%bh
	jnc	error
	cmp	$0x7F, %bh
	jne	error
	cmpb	0x1234, %bh
	jne 	error

	mov	$0xFFFF, %bx
	mov	%bx, 0x1234

	negw	0x1234
	jnc	error
	sahf
	neg	%bx
	jnc	error
	cmp	$0x1, %bx
	jne	error
	cmpw	0x1234, %bx
	jne 	error

	mov	$0x12345678, %ebx
	mov	%ebx, 0x1234

	negl	0x1234
	jnc	error
	sahf
	neg	%ebx
	jnc	error
	cmp	$0xEDCBA988, %ebx
	jne	error
	cmp	0x1234, %ebx
	jne 	error

	mov	$0x0, %ebx
	mov	%ebx, 0x1234

	negl	0x1234
	jc	error
	sahf
	neg	%ebx
	jc	error
	cmp	$0x0, %ebx
	jne	error
	cmp	0x1234, %ebx
	jne 	error
	
	.include "x86_32-simulator-end.s"

