	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"

start:
	push $1 		# push 4 bytes
	pop %eax 		# pop 4 bytes
	
	.include "x86_32-simulator-end.s"
