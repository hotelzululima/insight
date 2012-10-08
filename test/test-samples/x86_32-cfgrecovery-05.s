main:
	push   %ebp
	mov    %esp,%ebp
	sub    $0x8,%esp
	mov    0x14(%ebp),%eax
	mov    %eax,-0x4(%ebp)
	mov    0x10(%ebp),%ecx
	movsbl (%ecx),%edx
	mov    %edx,-0x8(%ebp)
	mov    -0x8(%ebp),%eax
	sub    $0x35,%eax
	mov    %eax,-0x8(%ebp)
	cmpl   $0x5,-0x8(%ebp)
	ja     here
	mov    -0x8(%ebp),%ecx
	movzbl from(%ecx),%edx
	lea	from(,%edx,4), %eax
	jmp    *%ecx
	
here:
	jmp here
from:	
	. = 0x1200
	