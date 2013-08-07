## Process this file with automake to produce Makefile.in
include ${top_builddir}/test/Makefile.inc

check_PROGRAMS = \
	io_binaryloader_test	\
	io_expr_to_smtlib_test	   		

io_binaryloader_test_SOURCES = binaryloader_test.cc
io_expr_to_smtlib_test_SOURCES = expr_to_smtlib_test.cc

maintainer-clean-local:
	rm -fr $(top_srcdir)/test/io/Makefile.in
