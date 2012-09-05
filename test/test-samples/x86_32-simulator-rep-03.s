	.set	INIT_EFLAGS, 1
	.include "x86_32-simulator-header.s"
	.set	AREA1,0x1100
	.set	AREA2, 0x2200
	.set 	AREASIZE, 12
	.set 	DIFFPOS, 3
start:
	cld
	mov	$AREA1, %edi
	mov	$0x0, %ax
	mov	$AREASIZE, %cx

	# fill AREA1
l1:
	stosw
	shl	%ax
	inc	%ax
	loop	l1

	# copy AREA1 -> AREA2
	mov	$AREASIZE, %cx
	mov	$AREA1, %esi
	mov	$AREA2, %edi
	rep	movsw

	# change a word somwhere in AREA1
	movw	$0x1234, AREA1+2 * DIFFPOS

	# compare areas
	mov	$AREASIZE, %cx
	mov	$AREA1, %esi
	mov	$AREA2, %edi
	repe 	cmpsw
	cmp	$(AREASIZE-DIFFPOS-1), %cx
	jne	error
	
	.include "x86_32-simulator-end.s"
