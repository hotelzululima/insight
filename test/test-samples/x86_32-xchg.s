	xchg %ax, %cx
	xchg %cx, %ax
	xchg %eax, %ecx
	xchg %ecx, %eax

	xchg 0x1111, %ch
	xchg %ch, 0x1111
	xchg 0x1111, %cx
	xchg %cx, 0x1111
	xchg 0x1111, %ecx
	xchg %ecx, 0x1111

	xchg %bh, %ch
	xchg %ch, %bh
	xchg %bx, %cx
	xchg %cx, %bx
	xchg %ebx, %ecx
	xchg %ecx, %ebx
	