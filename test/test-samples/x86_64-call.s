	call 0x1234
	call *0x1234
	call *-1234(%ebx)
	call *0xF012002
	call *%rax

	callq 0x1234
	callq *0x1234
	callq *-1234(%rbx)
	callq *0xF012002
	callq *%rax
