start:
	cmp $0, %eax
	jle lthen
lelse:
	mov $start+1, %eax
	jmp lcont
lhalt:
	ret
    
lthen:
	mov $l1 + 6, %eax
l1:
	sub $5, %eax
lcont:
	sub $1, %eax
	jmp *%eax
	