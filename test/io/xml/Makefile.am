## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

CFGRECOVERY=${top_builddir}/tools/cfgrecovery/cfgrecovery
CFGRECOVERY_CONFIG=${top_builddir}/test/cfgrecovery.cfg
CFGRECOVERYFLAGS=-c ${CFGRECOVERY_CONFIG} -d symbolic -f mc-xml

CHECK_RESULTS=${srcdir}/check-results.sh
EXTRA_DIST = check-results.sh

check_PROGRAMS = xml-tester

xml_tester_SOURCES = xml-tester.cc
xml_tester_CPPFLAGS = -I$(top_srcdir)/src
xml_tester_CXXFLAGS = -Wno-deprecated
xml_tester_LDFLAGS = @BINUTILS_LDFLAGS@
xml_tester_LDADD = $(top_builddir)/src/libinsight.la

XML_TESTER=${builddir}/xml-tester

BASE_TESTS = \
 x86_32-simulator-00.res x86_32-simulator-01.res \
 x86_32-simulator-02.res x86_32-simulator-03.res \
 x86_32-simulator-04.res x86_32-simulator-05.res \
 x86_32-simulator-06.res x86_32-simulator-CF.res \
 x86_32-simulator-aaa.res x86_32-simulator-aad.res \
 x86_32-simulator-aam.res x86_32-simulator-aas.res \
 x86_32-simulator-adcsbb.res x86_32-simulator-add.res \
 x86_32-simulator-booleans.res x86_32-simulator-bound.res \
 x86_32-simulator-bsf.res x86_32-simulator-bsr.res \
 x86_32-simulator-bswap.res x86_32-simulator-bt-01.res \
 x86_32-simulator-bt-02.res x86_32-simulator-btc.res \
 x86_32-simulator-btr.res x86_32-simulator-bts.res \
 x86_32-simulator-call-noinit.res x86_32-simulator-call.res \
 x86_32-simulator-cbw.res x86_32-simulator-cmov.res \
 x86_32-simulator-cmps-01.res x86_32-simulator-cmps-02.res \
 x86_32-simulator-cmpxchg.res x86_32-simulator-cwdcdq.res \
 x86_32-simulator-daadas.res x86_32-simulator-div.res \
 x86_32-simulator-enter-leave-01.res x86_32-simulator-enter-leave-02.res \
 x86_32-simulator-idiv.res x86_32-simulator-imul-01.res \
 x86_32-simulator-imul-02.res x86_32-simulator-imul-03.res \
 x86_32-simulator-int.res x86_32-simulator-int3.res \
 x86_32-simulator-into-01.res x86_32-simulator-into-02.res \
 x86_32-simulator-lods.res x86_32-simulator-loop.res \
 x86_32-simulator-lsahf.res x86_32-simulator-movbe.res \
 x86_32-simulator-movs.res x86_32-simulator-movsxz.res \
 x86_32-simulator-mul.res x86_32-simulator-neg.res \
 x86_32-simulator-popcnt.res x86_32-simulator-pushapopa.res \
 x86_32-simulator-pushfpopf.res x86_32-simulator-pushpop-01.res \
 x86_32-simulator-pushpop-02.res x86_32-simulator-pushpop-03.res \
 x86_32-simulator-pushpop-04.res x86_32-simulator-pushpop-05.res \
 x86_32-simulator-pushpop-06.res x86_32-simulator-rep-01.res \
 x86_32-simulator-rep-02.res x86_32-simulator-rep-03.res \
 x86_32-simulator-rep-04.res x86_32-simulator-rotate-01.res \
 x86_32-simulator-rotate-02.res x86_32-simulator-rotate-03.res \
 x86_32-simulator-rotate-04.res x86_32-simulator-scas.res \
 x86_32-simulator-setcc.res x86_32-simulator-shift-01.res \
 x86_32-simulator-shift-02.res x86_32-simulator-shift-03.res \
 x86_32-simulator-shift-04.res x86_32-simulator-sub.res \
 x86_32-simulator-xadd.res x86_32-simulator-xchg.res

XMLFILES = ${BASE_TESTS:%.res=%.mc.xml}

if WITH_VALGRIND
BASE_TESTS += \
 x86_32-simulator-00.memres x86_32-simulator-01.memres \
 x86_32-simulator-02.memres x86_32-simulator-03.memres \
 x86_32-simulator-04.memres x86_32-simulator-05.memres \
 x86_32-simulator-06.memres x86_32-simulator-CF.memres \
 x86_32-simulator-aaa.memres x86_32-simulator-aad.memres \
 x86_32-simulator-aam.memres x86_32-simulator-aas.memres \
 x86_32-simulator-adcsbb.memres x86_32-simulator-add.memres \
 x86_32-simulator-booleans.memres x86_32-simulator-bound.memres \
 x86_32-simulator-bsf.memres x86_32-simulator-bsr.memres \
 x86_32-simulator-bswap.memres x86_32-simulator-bt-01.memres \
 x86_32-simulator-bt-02.memres x86_32-simulator-btc.memres \
 x86_32-simulator-btr.memres x86_32-simulator-bts.memres \
 x86_32-simulator-call-noinit.memres x86_32-simulator-call.memres \
 x86_32-simulator-cbw.memres x86_32-simulator-cmov.memres \
 x86_32-simulator-cmps-01.memres x86_32-simulator-cmps-02.memres \
 x86_32-simulator-cmpxchg.memres x86_32-simulator-cwdcdq.memres \
 x86_32-simulator-daadas.memres x86_32-simulator-div.memres \
 x86_32-simulator-enter-leave-01.memres x86_32-simulator-enter-leave-02.memres \
 x86_32-simulator-idiv.memres x86_32-simulator-imul-01.memres \
 x86_32-simulator-imul-02.memres x86_32-simulator-imul-03.memres \
 x86_32-simulator-int.memres x86_32-simulator-int3.memres \
 x86_32-simulator-into-01.memres x86_32-simulator-into-02.memres \
 x86_32-simulator-lods.memres x86_32-simulator-loop.memres \
 x86_32-simulator-lsahf.memres x86_32-simulator-movbe.memres \
 x86_32-simulator-movs.memres x86_32-simulator-movsxz.memres \
 x86_32-simulator-mul.memres x86_32-simulator-neg.memres \
 x86_32-simulator-popcnt.memres x86_32-simulator-pushapopa.memres \
 x86_32-simulator-pushfpopf.memres x86_32-simulator-pushpop-01.memres \
 x86_32-simulator-pushpop-02.memres x86_32-simulator-pushpop-03.memres \
 x86_32-simulator-pushpop-04.memres x86_32-simulator-pushpop-05.memres \
 x86_32-simulator-pushpop-06.memres x86_32-simulator-rep-01.memres \
 x86_32-simulator-rep-02.memres x86_32-simulator-rep-03.memres \
 x86_32-simulator-rep-04.memres x86_32-simulator-rotate-01.memres \
 x86_32-simulator-rotate-02.memres x86_32-simulator-rotate-03.memres \
 x86_32-simulator-rotate-04.memres x86_32-simulator-scas.memres \
 x86_32-simulator-setcc.memres x86_32-simulator-shift-01.memres \
 x86_32-simulator-shift-02.memres x86_32-simulator-shift-03.memres \
 x86_32-simulator-shift-04.memres x86_32-simulator-sub.memres \
 x86_32-simulator-xadd.memres x86_32-simulator-xchg.memres

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=yes
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}
endif

TESTS = ${BASE_TESTS} check-diff

CLEANFILES = ${XMLFILES} ${TESTS} .z3-trace

LOG_COMPILER=${SHELL} -x ${CHECK_RESULTS}

maintainer-clean-local:
	rm -fr $(top_srcdir)/test/io/xml/Makefile.in

#
# GENERATION OF TEST RESULTS
#

x86_32-%.res : x86_32-%.mc.xml ${XML_TESTER}
	@ ${XML_TESTER} x86_32 $< > $@

x86_32-%.memres : x86_32-%.mc.xml ${XML_TESTER}
	@ ${MEMCHECK} ${XML_TESTER} x86_32 $< > $@ 2>&1

check-diff : ${BASE_TESTS}
	@ > check-diff
if WITH_VALGRIND
	@ for t in ${BASE_TESTS}; do \
          TNAME=`basename $${t} .res`; \
          if test "$${t}" = "$${TNAME}.res"; then \
            diff -q "$${TNAME}.res" "$${TNAME}.memres" >> check-diff; \
          fi; \
        done
else
	@ echo WARNING: Valgrind not used >&2
endif

#
# GENERATION OF XML FILES ACCORDING TO SAMPLES BINARY FILES
#
.SECONDARY: # keep generated files

x86_32-%.mc.xml : ${TEST_SAMPLES_DIR}/x86_32-%.bin check-cfgrecovery \
								$(CFGRECOVERY)
	@ echo "Generate $@"
	@ ${CFGRECOVERY} ${CFGRECOVERYFLAGS} -b elf32-i386 -o x86_32-$*.mc.xml $<

check-cfgrecovery :
	@ test -x $(CFGRECOVERY) || \
          (echo "cfgrecovery has not been compiled" 1>&2; exit 1)

