start:	
	mov	$end, %ah
	mov 	%ah, %bh
	mov	%ah, %ch
	jmp	*%ecx
	
end:
	jmp end

