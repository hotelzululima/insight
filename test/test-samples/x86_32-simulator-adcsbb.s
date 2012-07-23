	.include "x86_32-simulator-header.s"
start:
	mov	$0x01, %ah
	sahf	# set CF flag
	adc	$0xFE, %ah
	jnc	error
	cmp	$0x00, %ah
	jne 	error


	mov	$0x00, %ah
	sahf	# unset CF flag
	sbb	$0x01, %ah
	jnc	error
	cmp	$0xFF, %ah
	jne 	error

	stc
	sbb	$0x00, %ah
	jc	error
	cmp	$0xFE, %ah
	jne 	error
	
	.include "x86_32-simulator-end.s"
