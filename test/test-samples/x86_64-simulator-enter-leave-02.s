	.set	USE_STACK, 1
	.include "x86_64-simulator-header.s"

	enter	$16, $0
	movl	$0x11111111, 0(%esp)
	movl	$0x22222222, 4(%esp)
	movl	$0x33333333, 8(%esp)
	movl	$0x44444444, 12(%esp)
	enter	$16, $1
	movl	$0x11111111, 0(%esp)
	movl	$0x22222222, 4(%esp)
	movl	$0x33333333, 8(%esp)
	movl	$0x44444444, 12(%esp)
	leave
	leave
	
	.include "x86_64-simulator-end.s"
	