	## RECALL  src--> dst

	##  MOV r/m8,r8
	mov %al, %bl
	mov %ah, %bl
	movb 0x72190111, %bl
	movb 0x72190111, %bh
	
	##  MOV r/m16,r16
	mov %ax, %bx
	mov 0x72190111, %bx
	
	##  MOV r/m32,r32
	mov %eax, %ebx
	mov 0x72190111, %ebx
	
	##  MOV r/m64,r64
	mov %rax, %rbx
	mov 0x72190111, %rbx

	##  MOV r8,r/m8
	mov %cl, %bl
	mov %cl, %bh
	mov %ch, %bl
	mov %al, 0x72190111
	
	##  MOV r16,r/m16
	mov %cx, %bx
	mov %ax, 0x72190111
	
	##  MOV r32,r/m32
	mov %ecx, %ebx
	mov %eax, 0x72190111

	##  MOV r64,r/m64
	mov %rcx, %rbx
	mov %rax, 0x72190111

	##  MOV r/m16,Sreg
	mov %ss, %cx
	mov %ss, 0x72190111
	
	##  MOV Sreg,r/m16**
	mov %cx, %ss
	mov 0x72190111, %ss
	
	##  MOV AL,moffs8
	mov 0x89abcedf, %al
	addr32 mov 0x89abcedf, %al

	##  MOV AX,moffs16
	mov 0x89abcedf, %ax
	addr32 mov 0x89abcedf, %ax
	
	##  MOV EAX,moffs32*
	mov 0x89abcedf, %eax
	addr32 mov 0x89abcedf, %eax
	
	##  MOV RAX,moffs64*
	mov 0x89abcedf, %rax

	##  MOV moffs8,AL
	mov %al, 0x89abcedf
	addr32 mov %al, 0x89abcedf

	##  MOV moffs16*,AX
	mov %ax, 0x89abcedf
	addr32 mov %ax, 0x89abcedf

	##  MOV moffs32*,EAX
	mov %eax, 0x89abcedf
	addr32 mov %eax, 0x89abcedf

	##  MOV moffs64*,EAX
	mov %rax, 0x89abcedf

	##  MOV r8, imm8
	mov $0x72, %dl
	
	##  MOV r16, imm16
	mov $0x7219, %dx
	
	##  MOV r32, imm32
	mov $0x72190111, %edx
	
	##  MOV r/m8, imm8
	movb $0x72, 0x72190111
	
	##  MOV r/m16, imm16
	movw $0x7219, 0x72190111
	
	##  MOV r/m32, imm32
	movl $0x72190111, 0x72190111
	
	##  MOV r/m64, imm64
	movq $0x72190111, 0x72190111


	
