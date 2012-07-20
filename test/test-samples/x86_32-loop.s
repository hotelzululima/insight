start:		
	loop -127
	loope 0x80
	loopne 0x7F
	loopz 0x80
	loopnz 0x7F
	loop	start
	
	addr16 loop -127
	addr16 loope 0x8
	addr16 loopne 0x7F
	addr16 loopz 0x8
	addr16 loopnz 0x7F
	