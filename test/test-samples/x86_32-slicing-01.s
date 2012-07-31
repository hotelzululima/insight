start:	
	mov $4, %eax
	movl $0, (%ebx)
	mov $10, %edx
	mov $4, %ecx

loop:
	add (%eax), %esi
	pushl (%ecx)
	popl (%edi)
	incl (%edi)
	mov %eax, %ebx
	inc %ebx
	inc %ebp
	mov $2, %ebp
	mov %esi, %esp
	imul $4, %esp, %esp
	add %eax, %esp
	pushl 2 (%ebp)
	popl (%ebp)

end:
	jmp end

