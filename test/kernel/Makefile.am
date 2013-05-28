## Process this file with automake to produce Makefile.in
include ${top_builddir}/test/Makefile.inc

check_PROGRAMS = \
        kernel_architecture_test 		\
	kernel_expr_parser_test 		\
	kernel_expr_solver_test 		\
	kernel_expression_test			

kernel_architecture_test_SOURCES = architecture_test.cc
kernel_expr_parser_test_SOURCES = expr_parser_test.cc
kernel_expr_solver_test_SOURCES = expr_solver_test.cc
kernel_expression_test_SOURCES = expression_test.cc

maintainer-clean-local:
	rm -fr Makefile.in
