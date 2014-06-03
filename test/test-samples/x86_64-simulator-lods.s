	.include "x86_64-simulator-header.s"

	.set	string_addr1, 0x9999
	.set	string_addr2, 0xAAAA
	
start:
	cld
	mov	$0x0, %ah
	sahf	# to initialize DF
	movl	$0x12345678, string_addr1
	movl	$0x31415926, string_addr1+4
	movl	$0x27182818, string_addr1+8
	mov	$string_addr1, %esi
	mov	$string_addr2, %edi

	lodsb	
	cmp	$0x78, %al
	jne	error
	stosb
	
	lodsb
	cmp	$0x56, %al
	jne	error
	stosb
	
	lodsb
	cmp	$0x34, %al
	jne	error
	stosb
	
	lodsb
	cmp	$0x12, %al
	jne	error
	stosb	

	lodsw
	cmp	$0x5926, %ax
	jne	error
	stosw
	
	lodsw
	cmp	$0x3141, %ax
	jne	error
	stosw
	
	lodsl
	cmp	$0x27182818, %eax
	jne	error
	stosl

	std	# we read backward this time
	dec	%esi
	xor	%eax, %eax
	
	lodsb	
	cmp	$0x27, %al
	jne	error
	
	lodsb
	cmp	$0x18, %al
	jne	error
	
	lodsb
	cmp	$0x28, %al
	jne	error
	
	lodsb
	cmp	$0x18, %al
	jne	error
	
	dec	%esi	
	lodsw
	cmp	$0x3141, %ax
	jne	error
	
	lodsw
	cmp	$0x5926, %ax
	jne	error

	dec	%esi
	dec	%esi	
	lodsl
	cmp	$0x12345678, %eax
	jne	error
	
	.include "x86_64-simulator-end.s"
