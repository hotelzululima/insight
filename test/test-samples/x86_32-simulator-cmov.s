	.include "x86_32-simulator-header.s"
start:
	mov	$0x31415, %ebx
	mov	$0, %eax
	xor	$1, %eax	# CF <- 0, ZF <- 0
	cmova	%ebx, %eax	# CF = 0 & ZF = 0 ?
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# CF <- 0
	cmovae	%ebx, %eax	# CF == 0 ?
	cmp	$0x31415, %eax
	jne	error

	xor	%eax, %eax	# CF <- 0
	cmc			# CF <- 1
	cmovb	%ebx, %eax	# CF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	xor	$1, %eax	# CF <- 0, ZF <- 0
	cmc			# CF <- 1
	cmovbe	%ebx, %eax   	# CF == 1 or ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# CF <- 0, ZF <- 1
	cmovbe	%ebx, %eax  	# CF == 1 or ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# CF <- 0
	cmc			# CF <- 1
	cmovc	%ebx, %eax	# CF == 1 ?
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# ZF <- 1
	cmove	%ebx, %eax	# ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	inc	%eax
	cmp	%ebx, %eax
	cmovg	%ebx, %eax	# ZF == 0 & SF == OF ?
	cmp	$0x31415, %eax
	jne	error

	inc	%eax
	cmp	%ebx, %eax
	cmovge	%ebx, %eax	# SF == OF ?
	cmp	$0x31415, %eax
	jne	error

	cmp	%eax, %eax
	cmovge	%ebx, %eax	# SF == OF ?
	cmp	$0x31415, %eax
	jne	error

	dec	%eax
	cmp	%ebx, %eax
	cmovl	%ebx, %eax	# SF != OF ?
	cmp	$0x31415, %eax
	jne	error

	dec 	%eax
	cmp	%ebx, %eax
	cmovle	%ebx, %eax	# ZF = 1 or SF != OF ?
	cmp	$0x31415, %eax
	jne	error

	cmp	%eax, %eax
	cmovle	%ebx, %eax	# ZF == 1 or SF != OF ?
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# CF <- 0, ZF <- 1
	cmovna	%ebx, %eax	# CF == 1 || ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	xor	$1, %eax	# CF <- 0, ZF <- 0
	cmc			# CF <- 1
	cmovna	%ebx, %eax	# CF == 1 || ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	xor	%eax, %eax	# CF <- 0
	cmc			# CF <- 1
	cmovnae	%ebx, %eax	# CF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	xor	%eax, %eax	# CF <- 0
	cmovnb	%ebx, %eax	# CF == 0 ?
	cmp	$0x31415, %eax
	jne	error

	xor	$1, %eax	# CF <- 0, ZF <- 0
	cmovnbe	%ebx, %eax	# CF == 0 & ZF == 0
	cmp	$0x31415, %eax
	jne	error
	
	xor	%eax, %eax	# CF <- 0
	cmovnc	%ebx, %eax	# CF == 0 ?
	cmp	$0x31415, %eax
	jne	error

	xor	$1, %eax	# ZF <- 0
	cmovne	%ebx, %eax	# ZF == 0 ?
	cmp	$0x31415, %eax
	jne	error


	cmp	%ebx, %eax
	cmovng %ebx, %eax	# !(%eax > %ebx)
	cmp	$0x31415, %eax
	jne	error

	dec	%eax
	cmp	%ebx, %eax
	cmovng %ebx, %eax	# !(%eax > %ebx)
	cmp	$0x31415, %eax
	jne	error


	dec	%eax
	cmp	%ebx, %eax
	cmovnge %ebx, %eax	# !(%eax >= %ebx)
	cmp	$0x31415, %eax
	jne	error


	cmp	%ebx, %eax
	cmovnl	%ebx, %eax	# !(%eax < %ebx)
	cmp	$0x31415, %eax
	jne	error

	inc	%eax
	cmp	%ebx, %eax
	cmovnl	%ebx, %eax	# !(%eax < %ebx)
	cmp	$0x31415, %eax
	jne	error

	inc 	%eax
	cmp	%ebx, %eax
	cmovnle	 %ebx, %eax	# !(%eax <= %ebx)
	cmp	$0x31415, %eax
	jne	error

	xor	%eax, %eax
	cmovno	 %ebx, %eax	# OF == 0 ?
	cmp	$0x31415, %eax
	jne	error


	xor	$0, %eax
	cmovnp	 %ebx, %eax	# PF == 0 ?
	cmp	$0x31415, %eax
	jne	error

	cmp	$0, %eax
	cmovns	 %ebx, %eax	# SF == 0 ?
	cmp	$0x31415, %eax
	jne	error


	xor	$1, %eax
	cmovnz	 %ebx, %eax	# ZF == 0 ?
	cmp	$0x31415, %eax
	jne	error

	mov	$0x7F, %al
	add	$0x7F, %al
	cmovo	 %ebx, %eax	# OF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	dec	%eax		# remove lsb to get parity
	cmovp	 %ebx, %eax
	cmp	$0x31415, %eax	# PF == 1 ?
	jne	error

	dec	%eax		# remove lsb to get parity	
	cmovpe	 %ebx, %eax	# PF == 1 ?
	cmp	$0x31415, %eax
	jne	error	
	
	and	%eax, %eax
	cmovpo	 %ebx, %eax	# PF == 0 ?
	cmp	$0x31415, %eax
	jne	error


	dec	%eax
	sub	%ebx, %eax
	cmovs	 %ebx, %eax	# SF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	xor	%eax, %eax
	cmovz	 %ebx, %eax	# ZF == 1 ?
	cmp	$0x31415, %eax
	jne	error

	.include "x86_32-simulator-end.s"
