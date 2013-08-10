	.include "x86_64-simulator-header.s"
start:
	mov	$0xFFFF, %ax
	add	%ax, %ax
	jnb	error		# CF <- 1 due to carry overflow

	clc			# CF <- 0
	jb	error
	cmc			# CF <- not CF
	jnb 	error
	cmc			# CF <- not CF
	jb 	error

	.include "x86_64-simulator-end.s"
