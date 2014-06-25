MANDIR=${builddir}/../../manuals
TEXI2DVI = texi2dvi
TEXI2DVIFLAGS = --build=clean -I ${srcdir} -I ${builddir} -I ${MANDIR} -p

IIITUTO_FILES = iii-tutorial.texi the-crackme.texi macros.texi \
                introduction.texi index.texi basic-features.texi \
                titlepage.texi appendices.texi advanced-features.texi

# Rules and targets
all: docs

docs: tutorials

tutorials: iii-tutorial.pdf

iii-tutorial.pdf: iii-tutorial.texi ${IIITUTO_FILES}
	${TEXI2DVI} ${TEXI2DVIFLAGS} -o $@ $<
	@ which -s activate-preview.sh && activate-preview.sh || exit 0

clean-local:
	@rm -fr *~

distclean-local:
	rm -fr *.pdf

maintainer-clean-local:
	rm -fr Makefile.in
