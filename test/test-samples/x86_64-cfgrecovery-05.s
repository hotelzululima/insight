main:
	pushq  %rbp
	mov    %rsp, %rbp
	sub    $0x8, %rsp
	mov    0x14(%rbp), %rax
	mov    %rax, -0x4(%rbp)
	mov    0x10(%rbp), %rcx
	movsbq (%rcx), %rdx
	mov    %rdx, -0x8(%rbp)
	mov    -0x8(%rbp), %rax
	sub    $0x35, %rax
	mov    %rax, -0x8(%rbp)
	cmpl   $0x5, -0x8(%rbp)
	ja     here
	mov    -0x8(%rbp), %rcx
	movzbq from(%rcx), %rdx
	lea    from(,%rdx,4), %rax
	jmpq   *%rcx
	
here:
	jmpq *here
from:	
	. = 0x1200
	
