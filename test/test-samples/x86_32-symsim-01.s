main:
	cmp	$10, %eax
	jle	c1
	jle	c2

end:	
	hlt

c1:
	mov 	$0x1234, %eax
	jmp	end

c2:
	mov 	$0x5678, %eax
	jmp	end

	