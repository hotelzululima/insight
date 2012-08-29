	.set 	checkcode, 0x1F2F3F4F
	.set	EXCEPTION_CHECK, 0
	.set	USE_STACK, 0
	.set	INIT_EFLAGS, 0
	.set	okaddr, 0x1000
	.set	ok2addr, 0x1111
	.set	erraddr, 0x6666
	.set	exception_handling_addr, 0x12FA792
	.set	stack_baseaddr, 0xFFFF
	
	.ifgt	EXCEPTION_CHECK
	movb	$0x1, exception_handling_addr
	.else
	movb	$0x0, exception_handling_addr
	.endif

	.ifgt	INIT_EFLAGS
	mov	$0x00, %ah
	sahf
	.endif
	.ifgt	USE_STACK
initstack:
 	# mandatory to prevent raise of UndefinedValue 	
	mov $stack_baseaddr, %esp
	mov $0x12345678, %ebp
	.endif	
start:
	call	function1
	call	*%eax
	cmp	$checkcode, %eax
	jne	error

	.include "x86_32-simulator-end.s"
	
function1:
	call	function2
	ret

function2:
	mov	$function3, %eax
	ret
	
function3:
	mov	$checkcode, %eax
	ret

		