	## NOT r/m8 A Valid Valid Reverse each bit of r/m8.
	not %ah
	notb 0x1234 (%eax)
		
	## F7 /2 NOT r/m16 A Valid Valid Reverse each bit of r/m16.
	not %ax
	notw 0x1234 (%eax)
	
	## F7 /2 NOT r/m32 A Valid Valid Reverse each bit of r/m32.

	not %eax
	notl 0x1234 (%eax)
