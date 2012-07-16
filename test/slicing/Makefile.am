## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${srcdir}/check-results.sh

TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

LOG_COMPILER=${SHELL} ${CHECKRESULTS}

CLEANFILES=${TESTS} ${TMPFILES} ${BUILT_SOURCES}

MAINTAINERCLEANFILES = Makefile.in

check_PROGRAMS = slicer

slicer_SOURCES = slicer.cc
slicer_CPPFLAGS = -I$(top_srcdir)/src
slicer_CXXFLAGS = -Wno-deprecated
slicer_LDFLAGS = @BINUTILS_LDFLAGS@
slicer_LDADD = $(top_builddir)/src/libinsight.la

TEST_SLICER = ${builddir}/slicer

BASE_TESTS = \
	x86_32-slicing-01.memres \
	x86_32-gcd.memres 

if WITH_VALGRIND
BASE_TESTS += \
	x86_32-slicing-01.memres \
	x86_32-gcd.memres 
endif

TESTS = \
 ${BASE_TESTS} \
 \
 check-diff

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=yes
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}


%.res : %.spec.sh ${TEST_SAMPLES_DIR}/%.bin ${TEST_SLICER}
	 @ source $<; \
          ${TEST_SLICER} ${TEST_SAMPLES_DIR}/`basename $< .spec.sh`.bin \
           $${SLICING_MAX_STEPS} $${SLICING_ADDR} $${SLICING_LVALUE} > $@ 2>&1

%.memres : %.spec.sh ${TEST_SAMPLES_DIR}/%.bin ${TEST_SLICER}
	 @ source $<; ${MEMCHECK} \
          ${TEST_SLICER} ${TEST_SAMPLES_DIR}/`basename $< .spec.sh`.bin \
           $${SLICING_MAX_STEPS} $${SLICING_ADDR} $${SLICING_LVALUE} > $@ 2>&1

check-diff : ${BASE_TESTS}
	@ for t in ${BASE_TESTS}; do \
          TNAME=`basename $${t} .res`; \
          if test "$${t}" = "$${TNAME}.res"; then \
            diff -q "$${TNAME}.res" "$${TNAME}.memres" > check-diff; \
          fi; \
        done

.SECONDARY:


save: ${TESTS}
	@ for T in ${TESTS}; do \
            REF="${srcdir}/$$(basename $${T}).result"; \
            cp -f $${T} $${REF}; \
          done



