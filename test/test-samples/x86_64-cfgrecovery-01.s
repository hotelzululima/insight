start:
	mov	$0x1,	%ax
	mov	$0x2,	%bx
	call	funct1
	call	funct2
	call	funct3
	ret

funct1:
	mov	$0x3,	%ax
	ret

funct2:
	mov	$0x4,	%ax
	ret

funct3:
	call 	funct1
	mov	%bx, %ax
	call 	funct2
	ret
	