start:	
	mov $4, %rax
	movl $0, (%rbx)
	mov $10, %rdx
	mov $4, %rcx

loop:
	add  (%rax), %rsi
	push (%rcx)
	pop  (%rdi)
	incl (%rdi)
	mov  %rax, %rbx
	inc  %rbx
	inc  %rbp
	mov  $2, %rbp
	mov  %rsi, %rsp
	imul $4, %rsp, %rsp
	add  %rax, %rsp
	push 2 (%rbp)
	pop  (%rbp)

end:
	jmp end

