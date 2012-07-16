	# set EXCEPTION_CHECK to 1 to indicate that the test-case should
	# terminate into a sink node due to some CPU exception.
	.set	EXCEPTION_CHECK, 0 	

	# set USE_STACK to 1 to initialize %esp register and enable emptyness
	# of the stack at the end of the test-case.
	.set	USE_STACK, 0
	
	.include "x86_32-simulator-header.s"
	
start:
	# here is the test-case code.
	# make a jump to 'okaddr' for nominal behavior
	# make a jump to 'erroraddr' for an unexpected behavior
	# in case of exception checking no jump is necessary.
	
	.include "x86_32-simulator-end.s"
