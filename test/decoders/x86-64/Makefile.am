## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${top_srcdir}/test/check-results.sh

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

x86_64_TESTS = \
	x86_64-and.res \
        \
        x86_64-bsf.res \
        x86_64-bsr.res \
        x86_64-bswap.res \
        x86_64-bt.res \
        x86_64-btc.res \
        x86_64-btr.res \
        x86_64-bts.res \
        \
	x86_64-call.res \
	x86_64-cmp.res \
	x86_64-cmps.res \
	x86_64-cmpxchg.res \
	\
	x86_64-div.res \
        \
        x86_64-enter-leave.res \
        \
	x86_64-idiv.res \
	x86_64-imul.res \
	x86_64-int.res \
	\
	x86_64-jcc.res \
	x86_64-jmp.res \
        \
        x86_64-lsahf.res \
	x86_64-lea.res \
	x86_64-lods.res \
	x86_64-loop.res \
        \
	x86_64-mov.res \
	x86_64-movbe.res \
	x86_64-movs.res \
	x86_64-movsxz.res \
	x86_64-mul.res \
        \
	x86_64-neg.res \
	x86_64-nop.res \
	x86_64-not.res \
	x86_64-or.res \
        \
	x86_64-popcnt.res \
	x86_64-pop.res \
	x86_64-pop16.res \
	x86_64-push.res \
	x86_64-push16.res \
        \
	x86_64-ret.res \
	x86_64-rotate.res \
        \
	x86_64-scas.res \
	x86_64-shift.res \
	x86_64-sbb.res \
	x86_64-setcc.res \
        \
	x86_64-xadd.res \
	x86_64-xchg.res \
	x86_64-xor.res \
        \
        ${dummy}

if WITH_VALGRIND
x86_64_TESTS += \
	x86_64-and.memres \
        \
        x86_64-bsf.memres \
        x86_64-bsr.memres \
        x86_64-bswap.memres \
        x86_64-bt.memres \
        x86_64-btc.memres \
        x86_64-btr.memres \
        x86_64-bts.memres \
        \
        x86_64-call.memres \
	x86_64-cmp.memres \
	x86_64-cmps.memres \
	x86_64-cmpxchg.memres \
        \
	x86_64-div.memres \
        \
        x86_64-enter-leave.memres \
        \
	x86_64-idiv.memres \
	x86_64-imul.memres \
	x86_64-int.memres \
	\
	x86_64-jcc.memres \
	x86_64-jmp.memres \
        \
        x86_64-lsahf.memres \
	x86_64-lea.memres \
	x86_64-lods.memres \
	x86_64-loop.memres \
        \
	x86_64-mov.memres \
	x86_64-movbe.memres \
	x86_64-movs.memres \
	x86_64-movsxz.memres \
	x86_64-mul.memres \
        \
	x86_64-neg.memres \
	x86_64-nop.memres \
	x86_64-not.memres \
	x86_64-or.memres \
        \
	x86_64-popcnt.memres \
	x86_64-pop.memres \
	x86_64-pop16.memres \
	x86_64-push.memres \
	x86_64-push16.memres \
        \
	x86_64-ret.memres \
	x86_64-rotate.memres \
        \
	x86_64-scas.memres \
	x86_64-shift.memres \
	x86_64-sbb.memres \
	x86_64-setcc.memres \
        \
	x86_64-xadd.memres \
	x86_64-xchg.memres \
	x86_64-xor.memres \
        \
        ${dummy}
endif

BASE_TESTS = ${x86_64_TESTS}


TESTS = \
	${BASE_TESTS} \
	 check-diff

EXTRA_DIST=${TESTS:%=%.result}

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

maintainer-clean-local:
	rm -fr $(top_srcdir)/test/decoders/x86-64/Makefile.in
