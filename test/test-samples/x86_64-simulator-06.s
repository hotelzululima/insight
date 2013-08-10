	.set	INIT_EFLAGS, 1
	.include "x86_64-simulator-header.s"
start:
	cmp 	$0,	%ah
	jne	error

	.include "x86_64-simulator-end.s"
