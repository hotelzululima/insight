## Process this file with automake to produce Makefile.in
if WITH_ATF
SUBDIRS = . src doc test
else
SUBDIRS = . src doc
endif

ACLOCAL_AMFLAGS = -I autotools-files/m4

.PHONY:	doc check

doc:
	(cd doc && $(MAKE))

distclean-local:
	rm -fr lib bin

EXTRA_DIST =      \
        AUTHORS   \
        COPYING   \
        ChangeLog \
        NEWS      \
        README

MAINTAINERCLEANFILES = \
	Makefile.in    \
	aclocal.m4     \
	compile        \
	config.guess   \
	config.sub     \
	depcomp        \
	install-sh     \
	ltmain.sh      \
	missing        \
	ylwrap

maintainer-clean-local:
	-rm -fr m4 autotools-files
