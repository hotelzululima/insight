	.include "x86_32-simulator-header.s"
start:
	mov $0x0001, %ax
	
	aad $2
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# ZF == 0
	js error	# SF == 0
	jnp error	# PF == 1
	cmp $3, %al	# AL == 1
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# ZF == 0
	js error	# SF == 0
	jnp error	# PF == 1
	cmp $9, %al	# AL == 9
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# SF == 0
	js error	# ZF == 0
	jnp error	# PF == 1
	cmp $27, %al	# AL == 27
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $81, %al	# AL == 81
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# ZF == 0
	jns error	# SF == 1
	jnp error	# PF == 1
	cmp $243, %al	# AL == 243
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	mov %al, %ah
	aad $2
	je error 	# ZF == 0
	jns error	# SF == 1
	jp error	# PF == 0
	cmp $217, %al	# AL == 217
	jne error	
	test %ah, %ah	# AH == 0
	jne error 

	.include "x86_32-simulator-end.s"
