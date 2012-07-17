	.include "x86_32-simulator-header.s"

	.set	SF,	0x80
	.set	ZF,	0x40
	.set	AF,	0x10
	.set	PF,	0x02
	.set	CF,	0x01
	
	mov	$0xEF, %ah
	add	$0x31, %ah
	lahf

	
	.include "x86_32-simulator-end.s"
	