	nop	%rax
	clc
	cmc
	cld
	cbw
	cwde
	
	rdtsc

	popf
	popfq

	pushf
	pushfq

	data16 popf
	data16 popfq

	data16 pushf
	data16 pushfq
