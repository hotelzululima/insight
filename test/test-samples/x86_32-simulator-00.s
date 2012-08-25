	.set	okaddr, 0x1111
	.set	exception_handling_addr, 0x12FA792
	
start:
	movb	$0x0, exception_handling_addr	
	jmp ok
	. = okaddr
ok:
	jmp ok
