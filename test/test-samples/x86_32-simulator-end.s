	jmp	ok
	# keep following lines to ensure address of labels
	. = okaddr
ok:
	.ifgt	USE_STACK
	cmp $stack_baseaddr, %esp	
	jne error
	.endif
	jmp ok2
	. = ok2addr		
ok2:	
	jmp ok2
	. = erraddr	
error:
	jmp error
	. = exception_handling_addr
.excepthdl:	
	.ifgt	EXCEPTION_CHECK
	.byte 0x01
	.else
	.byte 0x00
	.endif
