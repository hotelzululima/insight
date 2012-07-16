	.include "x86_32-simulator-header.s"
	
	mov 	$0xFFFF, %ax
	bsr 	%ax, %bx
	cmp	$15, %bx
	jne	error

	aam	$2
	bsr 	%ax, %bx
	cmp	$14, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$13, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$12, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$11, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$10, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$9, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$8, %bx
	jne	error

	mov	%ah, %al
	aam	$2
	bsr 	%ax, %bx
	cmp	$0, %bx
	jne	error

	.include "x86_32-simulator-end.s"
	