	.include "x86_32-simulator-header.s"

start:
	mov	$0xF4, %ah
	mov	%ah, 0x1234

	mov	$0, %ecx	
	movsbw	0x1234,	%cx
	cmp	$0x0000FFF4, %ecx
	jne	error

	mov	$0, %ecx	
	movsbl	0x1234, %ecx
	cmp	$0xFFFFFFF4, %ecx
	jne	error
	
	mov	%cx, 0x1234
	mov	$0, %ecx	
	movswl	0x1234,	%ecx
	cmp	$0xFFFFFFF4, %ecx
	jne	error

	mov	$0, %ecx	
	movsbw	%ah, %cx
	cmp	$0x0000FFF4, %ecx
	jne	error
	
	mov	$0, %ecx	
	movsbl	%ah, %ecx
	cmp	$0xFFFFFFF4, %ecx
	jne	error

	mov	%cx, %ax
	mov	$0, %ecx	
	movswl	%ax, %ecx
	cmp	$0xFFFFFFF4, %ecx
	jne	error

	mov	$0xF4, %ah
	mov	%ah, 0x1234

	mov	$0, %ecx	
	movzbw	0x1234,	%cx
	cmp	$0x000000F4, %ecx
	jne	error

	mov	$0, %ecx	
	movzbl	0x1234, %ecx
	cmp	$0x000000F4, %ecx
	jne	error
	
	mov	%cx, 0x1234
	mov	$0, %ecx	
	movzwl	0x1234,	%ecx
	cmp	$0x000000F4, %ecx
	jne	error

	mov	$0, %ecx	
	movzbw	%ah, %cx
	cmp	$0x000000F4, %ecx
	jne	error
	
	mov	$0, %ecx	
	movzbl	%ah, %ecx
	cmp	$0x000000F4, %ecx
	jne	error

	mov	%cx, %ax
	mov	$0, %ecx	
	movzwl	%ax, %ecx
	cmp	$0x000000F4, %ecx
	jne	error
	
	.include "x86_32-simulator-end.s"
