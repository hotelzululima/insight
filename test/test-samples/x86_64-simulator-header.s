	.ifndef	EXCEPTION_CHECK
	.set	EXCEPTION_CHECK, 0
	.endif
	.ifndef	USE_STACK
	.set	USE_STACK, 0
	.endif
	.ifndef	INIT_EFLAGS
	.set	INIT_EFLAGS, 0
	.endif
	
	.set	okaddr, 0x1000
	.set	ok2addr, 0x1111
	.set	erraddr, 0x6666
	.set	exception_handling_addr, erraddr+20
	.set	old_exception_handling_addr, 0x12FA792
	.set	stack_baseaddr, 0xFFFF
	
	.ifgt	EXCEPTION_CHECK
	movb	$0x1, old_exception_handling_addr
	.else
	movb	$0x0, old_exception_handling_addr
	.endif

	.ifgt	INIT_EFLAGS
	mov	$0x00, %ah
	sahf
	.endif
	.ifgt	USE_STACK
initstack:
 	# mandatory to prevent raise of UndefinedValue 	
	movq $stack_baseaddr, %rsp
	movq $0x12345678, %rbp
	.endif

	
