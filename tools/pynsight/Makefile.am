
bin_PROGRAMS = pynsight

pynsight_SOURCES = pynsight.cc

pynsight_CPPFLAGS = @PYTHON_CFLAGS@ @BINUTILS_CFLAGS@ -I$(top_srcdir)/src
pynsight_CXXFLAGS = -Wno-deprecated
pynsight_LDFLAGS = @PYTHON_LDFLAGS@ @BINUTILS_LDFLAGS@
pynsight_LDADD = $(top_builddir)/src/libinsight.la

all:

MAINTAINERCLEANFILES = \
	$(top_srcdir)/tools/pynsight/Makefile.in
