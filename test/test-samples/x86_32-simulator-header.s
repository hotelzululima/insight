	.ifndef	EXCEPTION_CHECK
	.set	EXCEPTION_CHECK, 0
	.endif
	.ifndef	USE_STACK
	.set	USE_STACK, 0
	.endif
	
	.set	okaddr,   0x1000
	.set	ok2addr,  0x1111
	.set	erraddr, 0x6666
	.set 	nominal_entrypoint, 0x0011
	.set	exception_entrypoint, 0x0066
	.set	stack_baseaddr, 0xFFFF
	
	.ifgt	EXCEPTION_CHECK
	.set	entrypoint, exception_entrypoint
	.else
	.set	entrypoint, nominal_entrypoint	
	.endif

	.word	entrypoint
	. = entrypoint	
	.ifgt	USE_STACK
initstack:
 	# mandatory to prevent raise of UndefinedValue 	
	mov $stack_baseaddr, %esp
	.endif

	
