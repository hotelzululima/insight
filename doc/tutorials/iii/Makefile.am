MANDIR=${builddir}/../../manuals
TEXI2DVI = texi2dvi
TEXI2DVIFLAGS = --clean -I ${srcdir} -I ${builddir} -I ${MANDIR} -p

IIITUTO_FILES = iii-tutorial.texi the-crackme.texi macros.texi \
                introduction.texi index.texi basic-features.texi \
                titlepage.texi appendices.texi advanced-features.texi \
                view_asm_01.png view_mc_01.png references.texi \
                demo/demo-setup-1.py \
                demo/demo-setup-2.py \
                demo/demo-setup-3.py \
		demo/stub_libc_start_main.s \
                demo/stub_printf.s \
                demo/stub_read.s \
                demo/meta/ccall.inc \
                demo/meta/crackme.asm

EXTRA_DIST = ${IIITUTO_FILES}

# Rules and targets
all: 

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

