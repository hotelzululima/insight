	.set	USE_STACK, 1
	.set 	checkcode, 0x1F2F3F4F
	.include "x86_32-simulator-header.s"
	
start:
	mov 	$0xFFFF, %esp
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

		