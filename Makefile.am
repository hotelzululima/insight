## Process this file with automake to produce Makefile.in
SUBDIRS = . src doc tools

if WITH_ATF
SUBDIRS += test 
endif

ACLOCAL_AMFLAGS = -I autotools-files/m4
CLEANFILES=.z3-trace

.PHONY:	doc check

doc:
	(cd doc && $(MAKE))

distclean-local:
	rm -fr lib bin 

maintainer-clean-local:
	rm -fr $(top_srcdir)/Makefile.in \
	       $(top_srcdir)/aclocal.m4  \
	       $(top_srcdir)/autotools-files/

EXTRA_DIST =      \
        AUTHORS   \
        COPYING   \
        ChangeLog \
        NEWS      \
        README
