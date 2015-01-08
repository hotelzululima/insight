MANDIR = ${srcdir}/manuals
TEXI2DVI = texi2dvi
TEXI2DVIFLAGS = --build=clean -I ${MANDIR} -I ${builddir}/manuals -p
SUBDIRS=tutorials

.PHONY:	manuals api

# Rules and targets
all:

docs: manuals api

api: doxygen/doxygen.cfg
	@(cd doxygen && (doxygen doxygen.cfg || \
	echo "error: 'doxygen' is needed to build the API documentation"))

manuals: insight-user-manual.pdf insight-dev-manual.pdf \
         iii-tutorial.pdf

insight-user-manual.pdf: $(MANDIR)/insight-user-manual.texi
	${TEXI2DVI} ${TEXI2DVIFLAGS} -o $@ $<

insight-dev-manual.pdf: $(MANDIR)/insight-dev-manual.texi
	${TEXI2DVI} ${TEXI2DVIFLAGS} -o $@ $<

clean-local:
	@rm -fr *~
	@(cd $(MANDIR) && \
	 rm -fr *~ *.aux *.cp *.cps *.fn *.ky *.kys *.log *.pg *.toc *.tp *.vr)

distclean-local:
	rm -fr api/ *.pdf

maintainer-clean-local:
	rm -fr $(top_srcdir)/doc/Makefile.in
