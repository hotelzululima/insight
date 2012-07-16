	.include "x86_32-simulator-header.s"
	
	mov	$0x0001, %ax
	aad	$2
	bsf	%ax, %bx
	cmp 	$0, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2	
	bsf	%ax, %bx
	cmp 	$1, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	cmp 	$2, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	cmp 	$3, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	cmp 	$4, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2	
	bsf	%ax, %bx
	cmp 	$5, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	cmp 	$6, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	cmp 	$7, %bx
	jne 	error

	mov 	%al, %ah
	mov	$0, %al
	aad	$2
	bsf	%ax, %bx
	jne 	error

	.include "x86_32-simulator-end.s"
	