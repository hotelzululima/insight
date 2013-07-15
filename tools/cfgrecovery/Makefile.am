## Process this file with automake to produce Makefile.in

bin_PROGRAMS = cfgrecovery

cfgrecovery_SOURCES = \
	cfgrecovery.cc cfgrecovery.hh \
        algorithms.hh algorithms.cc |
        \
        ${dummy}

cfgrecovery_CPPFLAGS = @BINUTILS_CFLAGS@ -I$(top_srcdir)/src
cfgrecovery_CXXFLAGS = -Wno-deprecated
cfgrecovery_LDFLAGS = @BINUTILS_LDFLAGS@
cfgrecovery_LDADD = $(top_builddir)/src/libinsight.la

all:

MAINTAINERCLEANFILES = \
	Makefile.in
