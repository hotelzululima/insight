## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${srcdir}/check-results.sh

TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

LOG_COMPILER=${SHELL} ${CHECKRESULTS}

CLEANFILES=${TESTS} ${TMPFILES} ${BUILT_SOURCES}

check_PROGRAMS = test-decoder

test_decoder_SOURCES = test-decoder.cc
test_decoder_CPPFLAGS = -I$(top_srcdir)/src
test_decoder_CXXFLAGS = -Wno-deprecated
test_decoder_LDFLAGS = @BINUTILS_LDFLAGS@
test_decoder_LDADD = $(top_builddir)/src/libinsight.la

TEST_DECODER = ${builddir}/test-decoder

X86_32_TESTS = \
	x86_32-aaa.res \
	x86_32-aad.res \
	x86_32-aam.res \
	x86_32-aas.res \
	x86_32-and.res \
        \
        x86_32-bound.res \
        x86_32-bsf.res \
        x86_32-bsr.res \
        x86_32-bswap.res \
        x86_32-bt.res \
        x86_32-btc.res \
        x86_32-btr.res \
        x86_32-bts.res \
        \
	x86_32-call.res \
	x86_32-cmp.res \
	x86_32-cmps.res \
	x86_32-cmpxchg.res \
	\
	x86_32-daadas.res \
	x86_32-div.res \
        \
        x86_32-enter-leave.res \
        \
	x86_32-idiv.res \
	x86_32-imul.res \
	x86_32-int.res \
	\
	x86_32-jcc.res \
	x86_32-jmp.res \
        \
        x86_32-lsahf.res \
	x86_32-lea.res \
	x86_32-lods.res \
	x86_32-loop.res \
        \
	x86_32-mov.res \
	x86_32-movbe.res \
	x86_32-movs.res \
	x86_32-movsxz.res \
	x86_32-mul.res \
        \
	x86_32-neg.res \
	x86_32-nop.res \
	x86_32-not.res \
	x86_32-or.res \
        \
	x86_32-popcnt.res \
	x86_32-pop.res \
	x86_32-pop16.res \
	x86_32-popa.res \
	x86_32-popa16.res \
	x86_32-push.res \
	x86_32-pusha.res \
	x86_32-push16.res \
        \
	x86_32-rotate.res \
        \
	x86_32-scas.res \
	x86_32-shift.res \
	x86_32-sbb.res \
	x86_32-setcc.res \
        \
	x86_32-xadd.res \
	x86_32-xchg.res \
	x86_32-xor.res \
        \
        ${dummy}

if WITH_VALGRIND
X86_32_TESTS += \
	x86_32-aaa.memres \
	x86_32-aad.memres \
	x86_32-aam.memres \
	x86_32-aas.memres \
	x86_32-and.memres \
        \
        x86_32-bound.memres \
        x86_32-bsf.memres \
        x86_32-bsr.memres \
        x86_32-bswap.memres \
        x86_32-bt.memres \
        x86_32-btc.memres \
        x86_32-btr.memres \
        x86_32-bts.memres \
        \
        x86_32-call.memres \
	x86_32-cmp.memres \
	x86_32-cmps.memres \
	x86_32-cmpxchg.memres \
        \
	x86_32-daadas.memres \
	x86_32-div.memres \
        \
        x86_32-enter-leave.memres \
        \
	x86_32-idiv.memres \
	x86_32-imul.memres \
	x86_32-int.memres \
	\
	x86_32-jcc.memres \
	x86_32-jmp.memres \
        \
        x86_32-lsahf.memres \
	x86_32-lea.memres \
	x86_32-lods.memres \
	x86_32-loop.memres \
        \
	x86_32-mov.memres \
	x86_32-movbe.memres \
	x86_32-movs.memres \
	x86_32-movsxz.memres \
	x86_32-mul.memres \
        \
	x86_32-neg.memres \
	x86_32-nop.memres \
	x86_32-not.memres \
	x86_32-or.memres \
        \
	x86_32-popcnt.memres \
	x86_32-pop.memres \
	x86_32-pop16.memres \
	x86_32-popa.memres \
	x86_32-popa16.memres \
	x86_32-push.memres \
	x86_32-pusha.memres \
	x86_32-push16.memres \
        \
	x86_32-rotate.memres \
        \
	x86_32-scas.memres \
	x86_32-shift.memres \
	x86_32-sbb.memres \
	x86_32-setcc.memres \
        \
	x86_32-xadd.memres \
	x86_32-xchg.memres \
	x86_32-xor.memres \
        \
        ${dummy}
endif

BASE_TESTS = ${X86_32_TESTS}


TESTS = \
	${BASE_TESTS} \
	 check-diff

EXTRA_DIST=${TESTS:%=%.result} ${CHECKRESULTS}

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=yes
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}


%.res : ${TEST_SAMPLES_DIR}/%.bin ${TEST_DECODER}
	 @${TEST_DECODER} $< > $@ 2>&1

%.memres : ${TEST_SAMPLES_DIR}/%.bin ${TEST_DECODER}
	 @${MEMCHECK} ${TEST_DECODER} $< > $@ 2>&1

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

.SECONDARY:


save: ${TESTS}
	@ for T in ${TESTS}; do \
            REF="${srcdir}/$$(basename $${T}).result"; \
            cp -f $${T} $${REF}; \
          done




