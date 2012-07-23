	.include "x86_32-simulator-header.s"

	.set	src_addr, 0x555555
	.set	byte_dst_addr,  0x777777
	.set	word_dst_addr,  0x888888
	.set	dword_dst_addr, 0x999999
	
start:
	stc	#to initialize eflags
	mov	$src_addr, %esi
	mov	$byte_dst_addr, %edi
	movl	$0x12345678, src_addr

	movsb
	cmpb	$0x78, byte_dst_addr
	jne 	error
	movsb
	cmpb	$0x56, byte_dst_addr+1
	jne 	error
	movsb
	cmpb	$0x34, byte_dst_addr+2
	jne 	error
	movsb
	cmpb	$0x12, byte_dst_addr+3
	jne 	error

	mov	$src_addr, %esi
	mov	$word_dst_addr, %edi
	movsw
	cmpw	$0x5678, word_dst_addr
	jne 	error
	movsw
	cmpw	$0x1234, word_dst_addr+2
	jne 	error
	

	mov	$src_addr, %esi
	mov	$dword_dst_addr, %edi
	movsl
	cmpl	$0x12345678, dword_dst_addr
	jne 	error

	.include "x86_32-simulator-end.s"
