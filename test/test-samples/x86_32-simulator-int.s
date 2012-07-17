	.set 	EXCEPTION_CHECK, 1
	.include "x86_32-simulator-header.s"

	int	$0x10

	.include "x86_32-simulator-end.s"
	