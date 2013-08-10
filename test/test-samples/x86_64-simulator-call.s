	.set	USE_STACK, 1
	.set 	checkcode, 0x1F2F3F4F
	.include "x86_64-simulator-header.s"
	
start:
	mov 	$0xFFFF, %rsp
	callq	function1
	callq	*%rax
	cmp	$checkcode, %rax
	jne	error
	.include "x86_64-simulator-end.s"

function1:
	callq	function2
	retq

function2:
	mov	$function3, %rax
	retq
	
function3:
	mov	$checkcode, %rax
	retq

		
