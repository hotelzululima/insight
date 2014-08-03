format ELF

;======================================= DATA ==================================

include 'ccall.inc'
 

macro crypt dstart,dsize {
	local a
	repeat dsize
		load a from dstart+%-1
		a = a xor $AA
		store a at dstart+%-1
	end repeat	
}



;======================================= CODE =================================
section '.text'  executable writeable 


public main
extrn printf
extrn system
extrn read
extrn strcmp

msg db	"Enter password:",0xA,0
buffer db 100 dup(0)


main:
	;pwd = Iv6oCb2U


    ccall printf, msg
	ccall read,0,buffer,9
	mov edx,eax
	dec edx
	mov [buffer+eax-1],byte 0

	mov esi,debut_crypt
	mov edi,esi
	mov ecx,to_crypt
decrypt:	
	lodsb		; obfuscation par chiffrement de code
	xor al,0xAA
	stosb
	loop decrypt	


	mov esi,buffer
	mov edi,pwd
	mov ecx,edx
	mov ebx, 0x0015
debut_crypt:	
teste:
	xor eax, eax
	lodsb
	add eax, ebx
	shl eax, 1	
	xor eax, 0x12
	mov bl, al
	scasb
	jnz ko
	loop teste
	jmp ok
pwd db 174, 90, 50, 80, 52, 62, 242, 156, 0		
to_crypt=$-debut_crypt
crypt debut_crypt,$-debut_crypt

ok:
	ccall system,shell
	xor eax,eax
	jmp fin
ko:
	ccall printf,msg2
	xor eax,eax
	inc eax
fin:
	ret


shell db "/bin/sh",0
msg2 db "Wrong password",0xA,0



