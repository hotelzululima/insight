## Process this file with automake to produce Makefile.in
AM_CPPFLAGS = -I$(top_srcdir)/src \
              -DTEST_SAMPLES_DIR=\"@TEST_SAMPLES_DIR@/\"

LDADD = $(top_builddir)/src/libinsight.la

SUBDIRS=decoders slicing tools

AUTOMAKE_OPTIONS=subdir-objects

EXTRA_DIST = \
	test-samples 			\
	check-results.sh		\
        io/Kyuafile 			\
        domains/concrete/Kyuafile 	\
        domains/Kyuafile 		\
        kernel/Kyuafile 		\
        slicing/Kyuafile 		\
        Kyuafile


check_PROGRAMS = \
	domains/concrete/concreteaddress_test 	\
	domains/concrete/concretememory_test  	\
	domains/concrete/concretevalue_test   	\
	domains/concrete/simulator_test       	\
	io/binaryloader_test	   		\
	io/expr_to_smtlib_test	   		\
	kernel/architecture_test 		\
	kernel/expr_parser_test 		\
	kernel/expression_test

# Kernel module tests
kernel_architecture_test_SOURCES = \
	kernel/architecture_test.cc

kernel_expr_parser_test_SOURCES = \
	kernel/expr_parser_test.cc

kernel_expression_test_SOURCES = \
	kernel/expression_test.cc

# Io module tests
io_binaryloader_test_SOURCES = \
	io/binaryloader_test.cc

# Io module tests
io_expr_to_smtlib_test_SOURCES = \
	io/expr_to_smtlib_test.cc

# Interpreters module tests
domains_concrete_concreteaddress_test_SOURCES = \
	domains/concrete/concreteaddress_test.cc

domains_concrete_concretememory_test_SOURCES = \
	domains/concrete/concretememory_test.cc

domains_concrete_concretevalue_test_SOURCES = \
	domains/concrete/concretevalue_test.cc

domains_concrete_simulator_test_SOURCES = \
	domains/concrete/simulator_test_cases.hh \
	domains/concrete/simulator_test.cc

check: all kyua-tests

kyua-tests: ${check_PROGRAMS}
	@ kyua test \
             --kyuafile=$(top_srcdir)/test/Kyuafile \
             --build-root=$(top_builddir)/test/ 
