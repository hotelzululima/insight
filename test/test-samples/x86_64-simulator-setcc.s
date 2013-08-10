	.include "x86_64-simulator-header.s"
	.set 	Bcc,	0x01
	.set	NAEcc,	Bcc
	.set	NBcc,	0xFE
	.set	AEcc,	NBcc
	.set 	Ecc,	0x40
	.set	Zcc,	Ecc
	.set 	NEcc,	0xBF
	.set	NZcc,	NEcc
	.set	BE1cc,	Bcc
	.set	BE2cc,	Zcc
	.set	NA1cc,	BE1cc
	.set	NA2cc,	BE2cc
	.set	NBEcc,	0xBE
	.set	Acc,	NBEcc
	.set	Scc,	0x80
	.set	NScc,	0x7F
	.set	Pcc,	0x04
	.set	NPcc,	0xFB
	.set	PEcc,	Pcc
	.set	POcc,	NPcc
	
start:
	mov	$Bcc, %ah
	sahf
	mov	$0x0, %bl
	setb	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NAEcc, %ah
	sahf
	mov	$0x0, %bl
	setnae	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NBcc, %ah
	sahf
	mov	$0x0, %bl
	setnb	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$AEcc, %ah
	sahf
	mov	$0x0, %bl
	setae	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$Ecc, %ah
	sahf
	mov	$0x0, %bl
	sete	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$Zcc, %ah
	sahf
	mov	$0x0, %bl
	setz	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NEcc, %ah
	sahf
	mov	$0x0, %bl
	setne	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NZcc, %ah
	sahf
	mov	$0x0, %bl
	setnz	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$BE1cc, %ah
	sahf
	mov	$0x0, %bl
	setbe	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$BE2cc, %ah
	sahf
	mov	$0x0, %bl
	setbe	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NA1cc, %ah
	sahf
	mov	$0x0, %bl
	setna	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NA2cc, %ah
	sahf
	mov	$0x0, %bl
	setna	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NBEcc, %ah
	sahf
	mov	$0x0, %bl
	setnbe	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$Acc, %ah
	sahf
	mov	$0x0, %bl
	seta	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$Scc, %ah
	sahf
	mov	$0x0, %bl
	sets	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NScc, %ah
	sahf
	mov	$0x0, %bl
	setns	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$Pcc, %ah
	sahf
	mov	$0x0, %bl
	setp	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$NPcc, %ah
	sahf
	mov	$0x0, %bl
	setnp	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$PEcc, %ah
	sahf
	mov	$0x0, %bl
	setpe	%bl
	cmp	$0x1, %bl
	jne	error

	mov	$POcc, %ah
	sahf
	mov	$0x0, %bl
	setpo	%bl
	cmp	$0x1, %bl
	jne	error


	
	.include "x86_64-simulator-end.s"
