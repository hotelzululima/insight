	lods   %ds:(%esi),%al
	lods   %ds:(%esi),%ax
	lods   %ds:(%esi),%eax
	lods   %ds:(%rsi),%rax
	lodsb
	lodsw
	lodsl
	lodsq
	addr32 lods   %ds:(%esi),%al
	addr32 lods   %ds:(%esi),%ax
	addr32 lods   %ds:(%esi),%eax
	addr32 lodsb
	addr32 lodsw
	addr32 lodsl

	stos   %al, %es:(%edi)
	stos   %ax, %es:(%edi)
	stos   %eax, %es:(%edi)
	stos   %rax, %es:(%rdi)
	stosb
	stosw
	stosl
	stosq
	addr32 stos   %al, %es:(%edi)
	addr32 stos   %ax, %es:(%edi)
	addr32 stos   %eax, %es:(%edi)
	addr32 stosb
	addr32 stosw
	addr32 stosl

