## Process this file with automake to produce Makefile.in
include ${top_builddir}/test/Makefile.inc

check_PROGRAMS = \
	concrete_address_test 	\
	concrete_memory_test  	\
	concrete_value_test   	\
	concrete_simulator_test       	

concrete_address_test_SOURCES = address_test.cc
concrete_memory_test_SOURCES = memory_test.cc
concrete_value_test_SOURCES = value_test.cc
concrete_simulator_test_SOURCES = simulator_test_cases.hh simulator_test.cc

maintainer-clean-local:
	rm -fr Makefile.in
