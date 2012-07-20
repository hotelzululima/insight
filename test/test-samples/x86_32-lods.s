	lods   %ds:(%esi),%al
	lods   %ds:(%esi),%ax
	lods   %ds:(%esi),%eax
	lodsb
	lodsw
	lodsl
	addr16 lods   %ds:(%si),%al
	addr16 lods   %ds:(%si),%ax
	addr16 lods   %ds:(%si),%eax
	addr16 lodsb
	addr16 lodsw
	addr16 lodsl

	stos   %al, %es:(%edi)
	stos   %ax, %es:(%edi)
	stos   %eax, %es:(%edi)
	stosb
	stosw
	stosl
	addr16 stos   %al, %es:(%di)
	addr16 stos   %ax, %es:(%di)
	addr16 stos   %eax, %es:(%di)
	addr16 stosb
	addr16 stosw
	addr16 stosl

