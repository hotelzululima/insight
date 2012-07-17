## Process this file with automake to produce Makefile.in
AM_CPPFLAGS = -I$(top_srcdir)/src \
              -DTEST_SAMPLES_DIR=\"@TEST_SAMPLES_DIR@/\"

LDADD = $(top_builddir)/src/libinsight.la

SUBDIRS=decoders slicing

AUTOMAKE_OPTIONS=subdir-objects

EXTRA_DIST = test-samples \
             loaders/binary/Kyuafile \
             loaders/Kyuafile \
             interpreters/concrete/Kyuafile \
             interpreters/Kyuafile \
             kernel/Kyuafile \
             slicing/Kyuafile \
             Kyuafile


check_PROGRAMS = \
	interpreters/concrete/concreteaddress_test \
	interpreters/concrete/concretememory_test  \
	interpreters/concrete/concretevalue_test   \
	interpreters/concrete/simulator_test       \
	loaders/binary/binaryloader_test	   \
	kernel/architecture_test 		   \
	kernel/expr_parser_test 		   \
	kernel/formula_test 		   

# Kernel module tests
kernel_architecture_test_SOURCES = \
	kernel/architecture_test.cc

kernel_expr_parser_test_SOURCES = \
	kernel/expr_parser_test.cc

kernel_formula_test_SOURCES = \
	kernel/formula_test.cc

# Loaders module tests
loaders_binary_binaryloader_test_SOURCES = \
	loaders/binary/binaryloader_test.cc

# Interpreters module tests
interpreters_concrete_concreteaddress_test_SOURCES = \
	interpreters/concrete/concreteaddress_test.cc

interpreters_concrete_concretememory_test_SOURCES = \
	interpreters/concrete/concretememory_test.cc

interpreters_concrete_concretevalue_test_SOURCES = \
	interpreters/concrete/concretevalue_test.cc

interpreters_concrete_simulator_test_SOURCES = \
	interpreters/concrete/simulator_test_cases.hh \
	interpreters/concrete/simulator_test.cc

check: all 
	@ kyua test \
             --kyuafile=$(top_srcdir)/test/Kyuafile \
             --build-root=$(top_builddir)/test/ 


MAINTAINERCLEANFILES = \
	Makefile.in
