start:		
	loop   -127
	loope  0x80
	loopne 0x7F
	loopz  0x80
	loopnz 0x7F
	loop   start
	
	addr32 loop   -127
	addr32 loope  0x8
	addr32 loopne 0x7F
	addr32 loopz  0x8
	addr32 loopnz 0x7F
	addr32 loop   start
	
