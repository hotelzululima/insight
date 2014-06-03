	.include "x86_32-simulator-header.s"
start:
	mov $0xFF, %al
	
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x7F, %ah	# AH == 0x7F
	jne error

	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x3F, %ah	# AH == 0x3F
	jne error

	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x1F, %ah	# AH == 0x1F
	jne error

	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x0F, %ah	# AH == 0xF
	jne error
	
	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x07, %ah	# AH == 0x7
	jne error
	
	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x03, %ah	# AH == 0x3
	jne error
	
	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x01, %ah	# AH == 0x1
	jne error
	
	mov %ah, %al
	aam $2	
	je error 	# ZF == 0
	js error	# SF == 0
	jp error	# PF == 0
	cmp $1, %al	# AL == 1
	jne error	
	cmp $0x00, %ah	# AH == 0x0
	jne error

	.include "x86_32-simulator-end.s"
