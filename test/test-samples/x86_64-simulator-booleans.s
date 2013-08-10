	.set 	USE_STACK, 1
	.include "x86_64-simulator-header.s"
	.set	Aaddr, 0x1234
	.set	Baddr, 0x4321
	
start:
	# 8 bits tests
	mov	$0x31, %ah
	mov	%ah, Aaddr
	mov	$0x27, %bh
	mov	%bh, Baddr

	and	%ah, %bh
	cmp	$0x21, %bh
	jne	error
	and	%ah, Baddr
	cmpb	%bh, Baddr	
	jne	error
	
	mov	$0x27, %bh
	mov	%bh, Baddr	
	or	%ah, %bh
	cmp	$0x37, %bh
	jne 	error
	or	%ah, Baddr
	cmpb	%bh, Baddr
	jne 	error

	mov	$0x27, %bh
	mov	%bh, Baddr	
	xor	%ah, %bh
	cmp	$0x16, %bh
	jne 	error
	xor	%ah, Baddr
	cmpb	%bh, Baddr
	jne 	error

	mov	$0x27, %bh
	mov	%bh, Baddr
	not	%bh
	cmp	$0xD8, %bh
	jne 	error
	notb	Baddr
	cmpb	%bh, Baddr
	jne 	error

	# 16 bits tests
	mov	$0x3141, %ax
	mov	%ax, Aaddr
	mov	$0x2718, %bx
	mov	%bx, Baddr

	and	%ax, %bx
	cmp	$0x2100, %bx
	jne	error
	and	%ax, Baddr
	cmpw	%bx, Baddr	
	jne	error
	
	mov	$0x2718, %bx
	mov	%bx, Baddr	
	or	%ax, %bx
	cmp	$0x3759, %bx
	jne 	error
	or	%ax, Baddr
	cmpw	%bx, Baddr
	jne 	error

	mov	$0x2718, %bx
	mov	%bx, Baddr	
	xor	%ax, %bx
	cmp	$0x1659, %bx
	jne 	error
	xor	%ax, Baddr
	cmpw	%bx, Baddr
	jne 	error

	mov	$0x2718, %bx
	mov	%bx, Baddr
	not	%bx
	cmp	$0xD8E7, %bx
	jne 	error
	notw	Baddr
	cmpw	%bx, Baddr
	jne 	error

	# 32 bits tests
	mov	$0x31415965, %eax
	mov	%eax, Aaddr
	mov	$0x27182818, %ebx
	mov	%ebx, Baddr

	and	%eax, %ebx
	cmp	$0x21000800, %ebx
	jne	error
	and	%eax, Baddr
	cmpl	%ebx, Baddr	
	jne	error
	
	mov	$0x27182818, %ebx
	mov	%ebx, Baddr	
	or	%eax, %ebx
	cmp	$0x3759797d, %ebx
	jne 	error
	or	%eax, Baddr
	cmpl	%ebx, Baddr
	jne 	error

	mov	$0x27182818, %ebx
	mov	%ebx, Baddr	
	xor	%eax, %ebx
	cmp	$0x1659717d, %ebx
	jne 	error
	xor	%eax, Baddr
	cmpl	%ebx, Baddr
	jne 	error

	mov	$0x27182818, %ebx
	mov	%ebx, Baddr
	not	%ebx
	cmp	$0xd8e7d7e7, %ebx
	jne 	error
	notl	Baddr
	cmpl	%ebx, Baddr
	jne 	error

	# check flags
	mov	$0x00, %ah
	and	$0xFF, %ah
	jnz	error
	jc	error
	jo 	error
	jnp	error
	js	error

	mov	$0x00, %eax
	and	$0xFF, %eax
	jnz	error
	jc	error
	jo	error
	jnp	error
	js	error
	
	mov	$0x87, %ah
	and	$0x11, %ah
	jz	error
	jc	error
	jo	error
	jp	error
	js	error

	mov	$0x85, %ah
	or	$0x11, %ah
	jz	error
	jc	error
	jo	error
	jnp	error
	jns	error
	
	.include "x86_64-simulator-end.s"


