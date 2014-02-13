
bin_PROGRAMS = pynsight

pynsight_SOURCES = pynsight.cc pynsight.hh program.cc 

pynsight_CPPFLAGS = @PYTHON_CFLAGS@ @BINUTILS_CFLAGS@ -I$(top_srcdir)/src
pynsight_CXXFLAGS = -Wno-deprecated -Wno-long-long \
                    -Wno-missing-field-initializers
pynsight_LDFLAGS = @PYTHON_LDFLAGS@ @BINUTILS_LDFLAGS@
pynsight_LDADD = $(top_builddir)/src/libinsight.la

all:

MAINTAINERCLEANFILES = \
	$(top_srcdir)/tools/pynsight/Makefile.in
