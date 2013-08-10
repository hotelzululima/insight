	#
	# Compute GCD(A,B)
	#
	# Compile the file into gcd.x86-32.o.
	#
	# Start the simulator and request to go to address of okaddr (0x1111).
	# This location is reached if the program terminates with %eax = GCD.
	#
	.set    A, 	 1071
	.set	B,	 1029
	.set	GCD,	 21
	
	.set	EXCEPTION_CHECK, 0 	
	.set	USE_STACK, 1
	.include "x86_32-simulator-header.s"
gcd:
	movl	$A,   %eax	# set value of A
	movl	$B,   %ebx	# set value of B
	movl	$GCD, %ecx	# GCD(A,B) = 21 (0x15)
.L8:
	testl	%eax, %eax
	je	.L7
.L10:
	testl	%ebx, %ebx
	je	.L7
	cmpl	%eax, %ebx
	jae	.L3
	subl	%ebx, %eax
	testl	%eax, %eax
	jne	.L10
.L7:
	cmpl	%eax, %ebx
	cmovae	%ebx, %eax
	cmp	%ecx, %eax
	jne	error
	jmp	ok
.L3:
	subl	%eax, %ebx
	jmp	.L8
	.include "x86_32-simulator-end.s"
