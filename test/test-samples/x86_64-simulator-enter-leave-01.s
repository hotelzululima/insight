	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"

	enter	$64, $0
	leave
	
	.include "x86_64-simulator-end.s"
	