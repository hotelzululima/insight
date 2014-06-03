PYNSIGHT_PKGNAME=insight
PYNSIGHT_HOME=$(DESTDIR)${pkgdatadir}/pynsight/
PYNSIGHT_DESTDIR=${PYNSIGHT_HOME}/${PYNSIGHT_PKGNAME}
PYNSIGHT_SCRIPT_FILES=__init__.py utils.py debugger.py iii.py xdot.py

bin_PROGRAMS = pynsight
bin_SCRIPTS = iii

EXTRA_DIST = ${PYNSIGHT_SCRIPT_FILES} ${bin_SCRIPTS}

pynsight_SOURCES = pynsight.cc pynsight.hh program.cc io.cc error.cc \
                   gengen.cc gengen.hh simulator.cc config.cc \
                   microcode.cc

pynsight_CPPFLAGS = @PYTHON_CPPFLAGS@ @BINUTILS_CFLAGS@ -I$(top_srcdir)/src \
                    -DPYNSIGHT_HOME="\"${PYNSIGHT_HOME}\"" \
                    -DPYNSIGHT_PACKAGE="\"${PYNSIGHT_PKGNAME}\""

pynsight_CXXFLAGS = -Wno-deprecated -Wno-long-long \
                    -Wno-missing-field-initializers
pynsight_LDFLAGS = @PYTHON_LDFLAGS@ @BINUTILS_LDFLAGS@
pynsight_LDADD = $(top_builddir)/src/libinsight.la

all:

MAINTAINERCLEANFILES = \
	$(top_srcdir)/tools/pynsight/Makefile.in

install-data-hook:
	@ echo Installing Pynsight scripts into ${PYNSIGHT_DESTDIR}
	@ ${MKDIR_P} ${PYNSIGHT_DESTDIR} && \
           for file in ${PYNSIGHT_SCRIPT_FILES}; do \
             ${INSTALL_DATA} ${srcdir}/$$file ${PYNSIGHT_DESTDIR}; \
           done

uninstall-hook:
	@ echo Removing files from ${PYNSIGHT_DESTDIR}
	@ if test -d ${PYNSIGHT_DESTDIR}; then \
          cd ${PYNSIGHT_DESTDIR}; rm -f ${PYNSIGHT_SCRIPT_FILES}; \
        fi
