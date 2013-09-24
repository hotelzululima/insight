
MANDIR=manuals

.PHONY:	manuals api

# Rules and targets
all:

docs: manuals api

api: doxygen/doxygen.cfg
	@(cd doxygen && (doxygen doxygen.cfg || \
	echo "error: 'doxygen' is needed to build the API documentation"))

manuals: insight-user-manual.pdf insight-dev-manual.pdf

insight-user-manual.pdf: $(MANDIR)/insight-user-manual.texi
	@(cd $(MANDIR) && texi2dvi -p -o ../$@ ../$<)

insight-dev-manual.pdf: $(MANDIR)/insight-dev-manual.texi
	@(cd $(MANDIR) && texi2dvi -p -o ../$@ ../$<)

clean-local:
	@rm -fr *~
	@(cd $(MANDIR) && \
	 rm -fr *~ *.aux *.cp *.cps *.fn *.ky *.kys *.log *.pg *.toc *.tp *.vr)

distclean-local:
	rm -fr api/ *.pdf

maintainer-clean-local:
	rm -fr $(top_srcdir)/doc/Makefile.in
