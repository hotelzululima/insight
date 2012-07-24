	aaa
	aad	$16
	aam	$16
	aas

	bound	%ebx, (%eax)
	nop	%eax
	clc
	cmc
	cld
	cbw
	cwde
	
	rdtsc

	popf
	popfl

	pushf
	pushfl

	data16 popf
	data16 popfl

	data16 pushf
	data16 pushfl
