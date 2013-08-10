start:
	cmp  $0, %rax
	jle  lthen
lelse:
	mov  $start+1, %rax
	jmpq *lcont
lhalt:
	retq
    
lthen:
	mov  $l1 + 6, %rax
l1:
	sub  $5, %rax
lcont:
	sub  $1, %rax
	jmpq *%rax
	
