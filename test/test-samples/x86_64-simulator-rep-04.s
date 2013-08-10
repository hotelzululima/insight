	.set	INIT_EFLAGS, 1
	.include "x86_64-simulator-header.s"
	.set	AREA,0x1100
	.set 	AREASIZE, 12
	.set 	DIFFPOS, 3
start:
	cld
	mov	$AREA, %edi
	mov	$0x1234, %ax
	mov	$AREASIZE, %cx

	# fill AREA1
	rep 	stosw

	# change a word somwhere in AREA1
	movw	$0x0AA0, AREA+2 * DIFFPOS

	# compare areas
	mov	$AREASIZE, %cx
	mov	$AREA, %edi
	repe 	scasw
	cmp	$(AREASIZE-DIFFPOS-1), %cx
	jne	error
	
	.include "x86_64-simulator-end.s"
