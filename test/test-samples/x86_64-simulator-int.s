	.set 	EXCEPTION_CHECK, 1
	.include "x86_64-simulator-header.s"

	int	$0x10

	.include "x86_64-simulator-end.s"
	