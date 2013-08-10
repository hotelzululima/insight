	.include "x86_64-simulator-header.s"
	
start:
	jmpq *ok
	.include "x86_64-simulator-end.s"
