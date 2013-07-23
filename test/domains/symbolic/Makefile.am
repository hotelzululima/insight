## Process this file with automake to produce Makefile.in
include ${top_builddir}/test/Makefile.inc

check_PROGRAMS = \
	symbolic_memory_test  	\
	symbolic_simulator_test       	

symbolic_memory_test_SOURCES = \
	memory_test.cc

symbolic_simulator_test_SOURCES = \
	simulator_test_cases.hh \
        simulator_test.cc

symbolic_simulator_test_CPPFLAGS=${AM_CPPFLAGS} -DINSIGHT_CONFIG_FILE=\"${abs_top_srcdir}/test/domains/symbolic/config\"

maintainer-clean-local:
	rm -fr Makefile.in
