## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${top_srcdir}/test/check-results.sh

TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

LOG_COMPILER=${SHELL} ${CHECKRESULTS}

CLEANFILES=${TESTS} ${TMPFILES} ${BUILT_SOURCES}

CFGRECOVERY = ${top_builddir}/tools/cfgrecovery/cfgrecovery
CFGR_LSW_FLAGS = -d linear
CFGR_RT_FLAGS = -d recursive

X86_32_RT_TESTS = \
	x86_32-cfgrecovery-01.rt.res \
        \
	x86_32-simulator-01.rt.res \
	x86_32-simulator-02.rt.res \
	x86_32-simulator-03.rt.res \
	x86_32-simulator-04.rt.res \
	x86_32-simulator-05.rt.res \
	\
	x86_32-simulator-aaa.rt.res \
	x86_32-simulator-aad.rt.res \
	x86_32-simulator-aam.rt.res \
	x86_32-simulator-aas.rt.res \
	x86_32-simulator-add.rt.res \
	x86_32-simulator-adcsbb.rt.res \
	\
	x86_32-simulator-booleans.rt.res \
	x86_32-simulator-bound.rt.res \
	x86_32-simulator-bsf.rt.res \
	x86_32-simulator-bsr.rt.res \
	x86_32-simulator-bswap.rt.res \
	x86_32-simulator-bt-01.rt.res \
	x86_32-simulator-bt-02.rt.res \
	x86_32-simulator-btc.rt.res \
	x86_32-simulator-btr.rt.res \
	x86_32-simulator-bts.rt.res \
	\
	x86_32-simulator-CF.rt.res \
	x86_32-simulator-call.rt.res \
	x86_32-simulator-cbw.rt.res \
	x86_32-simulator-cmov.rt.res \
	x86_32-simulator-cmps-01.rt.res \
	x86_32-simulator-cmps-02.rt.res \
	x86_32-simulator-cmpxchg.rt.res \
	x86_32-simulator-cwdcdq.rt.res \
	\
	x86_32-simulator-daadas.rt.res \
	x86_32-simulator-div.rt.res \
	\
	x86_32-simulator-enter-leave-01.rt.res \
	x86_32-simulator-enter-leave-02.rt.res \
	\
	x86_32-simulator-idiv.rt.res \
	x86_32-simulator-imul-01.rt.res \
	x86_32-simulator-imul-02.rt.res \
	x86_32-simulator-imul-03.rt.res \
	x86_32-simulator-int.rt.res \
	x86_32-simulator-int3.rt.res \
	x86_32-simulator-into-01.rt.res \
	x86_32-simulator-into-02.rt.res \
	\
	x86_32-simulator-lsahf.rt.res \
	x86_32-simulator-lods.rt.res \
	x86_32-simulator-loop.rt.res \
	\
	x86_32-simulator-movbe.rt.res \
	x86_32-simulator-movs.rt.res \
	x86_32-simulator-movsxz.rt.res \
	x86_32-simulator-mul.rt.res \
	\
	x86_32-simulator-neg.rt.res \
	\
	x86_32-simulator-popcnt.rt.res \
	x86_32-simulator-pushpop-01.rt.res \
	x86_32-simulator-pushpop-02.rt.res \
	x86_32-simulator-pushpop-03.rt.res \
	x86_32-simulator-pushpop-04.rt.res \
	x86_32-simulator-pushpop-05.rt.res \
	x86_32-simulator-pushpop-06.rt.res \
	x86_32-simulator-pushfpopf.rt.res \
	x86_32-simulator-pushapopa.rt.res \
	\
	x86_32-simulator-rep-01.rt.res \
	x86_32-simulator-rep-02.rt.res \
	x86_32-simulator-rep-03.rt.res \
	x86_32-simulator-rep-04.rt.res \
	\
	x86_32-simulator-rotate-01.rt.res \
	x86_32-simulator-rotate-02.rt.res \
	x86_32-simulator-rotate-03.rt.res \
	x86_32-simulator-rotate-04.rt.res \
	\
	x86_32-simulator-shift-01.rt.res \
	x86_32-simulator-shift-02.rt.res \
	x86_32-simulator-shift-03.rt.res \
	x86_32-simulator-shift-04.rt.res \
	\
	x86_32-simulator-scas.rt.res \
	x86_32-simulator-sub.rt.res \
	x86_32-simulator-setcc.rt.res \
	\
	x86_32-simulator-xadd.rt.res \
	x86_32-simulator-xchg.rt.res \
	\
	x86_32-gcd.rt.res \
        \
        ${dummy}

X86_32_LSW_TESTS = \
	x86_32-aaa.lsw.res \
	x86_32-aad.lsw.res \
	x86_32-aam.lsw.res \
	x86_32-aas.lsw.res \
	x86_32-and.lsw.res \
        \
        x86_32-bound.lsw.res \
        x86_32-bsf.lsw.res \
        x86_32-bsr.lsw.res \
        x86_32-bswap.lsw.res \
        x86_32-bt.lsw.res \
        x86_32-btc.lsw.res \
        x86_32-btr.lsw.res \
        x86_32-bts.lsw.res \
        \
	x86_32-call.lsw.res \
	x86_32-cmp.lsw.res \
	x86_32-cmps.lsw.res \
	x86_32-cmpxchg.lsw.res \
	\
	x86_32-daadas.lsw.res \
	x86_32-div.lsw.res \
        \
        x86_32-enter-leave.lsw.res \
        \
	x86_32-idiv.lsw.res \
	x86_32-imul.lsw.res \
	x86_32-int.lsw.res \
	\
	x86_32-jcc.lsw.res \
	x86_32-jmp.lsw.res \
        \
        x86_32-lsahf.lsw.res \
	x86_32-lea.lsw.res \
	x86_32-lods.lsw.res \
	x86_32-loop.lsw.res \
        \
	x86_32-mov.lsw.res \
	x86_32-movbe.lsw.res \
	x86_32-movs.lsw.res \
	x86_32-movsxz.lsw.res \
	x86_32-mul.lsw.res \
        \
	x86_32-neg.lsw.res \
	x86_32-nop.lsw.res \
	x86_32-not.lsw.res \
	x86_32-or.lsw.res \
        \
	x86_32-popcnt.lsw.res \
	x86_32-pop.lsw.res \
	x86_32-pop16.lsw.res \
	x86_32-popa.lsw.res \
	x86_32-popa16.lsw.res \
	x86_32-push.lsw.res \
	x86_32-pusha.lsw.res \
	x86_32-push16.lsw.res \
        \
	x86_32-rotate.lsw.res \
        \
	x86_32-scas.lsw.res \
	x86_32-shift.lsw.res \
	x86_32-sbb.lsw.res \
	x86_32-setcc.lsw.res \
        \
	x86_32-xadd.lsw.res \
	x86_32-xchg.lsw.res \
	x86_32-xor.lsw.res \
        \
	x86_32-cfgrecovery-01.lsw.res \
        \
        ${dummy}

if WITH_VALGRIND
X86_32_RT_TESTS += \
	x86_32-cfgrecovery-01.rt.memres \
        \
	x86_32-simulator-01.rt.memres \
	x86_32-simulator-02.rt.memres \
	x86_32-simulator-03.rt.memres \
	x86_32-simulator-04.rt.memres \
	x86_32-simulator-05.rt.memres \
	\
	x86_32-simulator-aaa.rt.memres \
	x86_32-simulator-aad.rt.memres \
	x86_32-simulator-aam.rt.memres \
	x86_32-simulator-aas.rt.memres \
	x86_32-simulator-add.rt.memres \
	x86_32-simulator-adcsbb.rt.memres \
	\
	x86_32-simulator-booleans.rt.memres \
	x86_32-simulator-bound.rt.memres \
	x86_32-simulator-bsf.rt.memres \
	x86_32-simulator-bsr.rt.memres \
	x86_32-simulator-bswap.rt.memres \
	x86_32-simulator-bt-01.rt.memres \
	x86_32-simulator-bt-02.rt.memres \
	x86_32-simulator-btc.rt.memres \
	x86_32-simulator-btr.rt.memres \
	x86_32-simulator-bts.rt.memres \
	\
	x86_32-simulator-CF.rt.memres \
	x86_32-simulator-call.rt.memres \
	x86_32-simulator-cbw.rt.memres \
	x86_32-simulator-cmov.rt.memres \
	x86_32-simulator-cmps-01.rt.memres \
	x86_32-simulator-cmps-02.rt.memres \
	x86_32-simulator-cmpxchg.rt.memres \
	x86_32-simulator-cwdcdq.rt.memres \
	\
	x86_32-simulator-daadas.rt.memres \
	x86_32-simulator-div.rt.memres \
	\
	x86_32-simulator-enter-leave-01.rt.memres \
	x86_32-simulator-enter-leave-02.rt.memres \
	\
	x86_32-simulator-idiv.rt.memres \
	x86_32-simulator-imul-01.rt.memres \
	x86_32-simulator-imul-02.rt.memres \
	x86_32-simulator-imul-03.rt.memres \
	x86_32-simulator-int.rt.memres \
	x86_32-simulator-int3.rt.memres \
	x86_32-simulator-into-01.rt.memres \
	x86_32-simulator-into-02.rt.memres \
	\
	x86_32-simulator-lsahf.rt.memres \
	x86_32-simulator-lods.rt.memres \
	x86_32-simulator-loop.rt.memres \
	\
	x86_32-simulator-movbe.rt.memres \
	x86_32-simulator-movs.rt.memres \
	x86_32-simulator-movsxz.rt.memres \
	x86_32-simulator-mul.rt.memres \
	\
	x86_32-simulator-neg.rt.memres \
	\
	x86_32-simulator-popcnt.rt.memres \
	x86_32-simulator-pushpop-01.rt.memres \
	x86_32-simulator-pushpop-02.rt.memres \
	x86_32-simulator-pushpop-03.rt.memres \
	x86_32-simulator-pushpop-04.rt.memres \
	x86_32-simulator-pushpop-05.rt.memres \
	x86_32-simulator-pushpop-06.rt.memres \
	x86_32-simulator-pushfpopf.rt.memres \
	x86_32-simulator-pushapopa.rt.memres \
	\
	x86_32-simulator-rep-01.rt.memres \
	x86_32-simulator-rep-02.rt.memres \
	x86_32-simulator-rep-03.rt.memres \
	x86_32-simulator-rep-04.rt.memres \
	\
	x86_32-simulator-rotate-01.rt.memres \
	x86_32-simulator-rotate-02.rt.memres \
	x86_32-simulator-rotate-03.rt.memres \
	x86_32-simulator-rotate-04.rt.memres \
	\
	x86_32-simulator-shift-01.rt.memres \
	x86_32-simulator-shift-02.rt.memres \
	x86_32-simulator-shift-03.rt.memres \
	x86_32-simulator-shift-04.rt.memres \
	\
	x86_32-simulator-scas.rt.memres \
	x86_32-simulator-sub.rt.memres \
	x86_32-simulator-setcc.rt.memres \
	\
	x86_32-simulator-xadd.rt.memres \
	x86_32-simulator-xchg.rt.memres \
	\
	x86_32-gcd.rt.memres \
        \
        ${dummy}

X86_32_LSW_TESTS += \
	x86_32-aaa.lsw.memres \
	x86_32-aad.lsw.memres \
	x86_32-aam.lsw.memres \
	x86_32-aas.lsw.memres \
	x86_32-and.lsw.memres \
        \
        x86_32-bound.lsw.memres \
        x86_32-bsf.lsw.memres \
        x86_32-bsr.lsw.memres \
        x86_32-bswap.lsw.memres \
        x86_32-bt.lsw.memres \
        x86_32-btc.lsw.memres \
        x86_32-btr.lsw.memres \
        x86_32-bts.lsw.memres \
        \
        x86_32-call.lsw.memres \
	x86_32-cmp.lsw.memres \
	x86_32-cmps.lsw.memres \
	x86_32-cmpxchg.lsw.memres \
        \
	x86_32-daadas.lsw.memres \
	x86_32-div.lsw.memres \
        \
        x86_32-enter-leave.lsw.memres \
        \
	x86_32-idiv.lsw.memres \
	x86_32-imul.lsw.memres \
	x86_32-int.lsw.memres \
	\
	x86_32-jcc.lsw.memres \
	x86_32-jmp.lsw.memres \
        \
        x86_32-lsahf.lsw.memres \
	x86_32-lea.lsw.memres \
	x86_32-lods.lsw.memres \
	x86_32-loop.lsw.memres \
        \
	x86_32-mov.lsw.memres \
	x86_32-movbe.lsw.memres \
	x86_32-movs.lsw.memres \
	x86_32-movsxz.lsw.memres \
	x86_32-mul.lsw.memres \
        \
	x86_32-neg.lsw.memres \
	x86_32-nop.lsw.memres \
	x86_32-not.lsw.memres \
	x86_32-or.lsw.memres \
        \
	x86_32-popcnt.lsw.memres \
	x86_32-pop.lsw.memres \
	x86_32-pop16.lsw.memres \
	x86_32-popa.lsw.memres \
	x86_32-popa16.lsw.memres \
	x86_32-push.lsw.memres \
	x86_32-pusha.lsw.memres \
	x86_32-push16.lsw.memres \
        \
	x86_32-rotate.lsw.memres \
        \
	x86_32-scas.lsw.memres \
	x86_32-shift.lsw.memres \
	x86_32-sbb.lsw.memres \
	x86_32-setcc.lsw.memres \
        \
	x86_32-xadd.lsw.memres \
	x86_32-xchg.lsw.memres \
	x86_32-xor.lsw.memres \
        \
	x86_32-cfgrecovery-01.lsw.res \
        \
        ${dummy}
endif

BASE_TESTS = ${X86_32_RT_TESTS} ${X86_32_LSW_TESTS} 


TESTS = \
	${BASE_TESTS} \
	 check-diff

EXTRA_DIST=${TESTS:%=%.result}

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=yes
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}


%.lsw.res : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${CFGRECOVERY} ${CFGR_LSW_FLAGS}  $< > $@ 2>&1

%.rt.res : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${CFGRECOVERY} ${CFGR_RT_FLAGS}  $< > $@ 2>&1

%.lsw.memres : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${MEMCHECK} ${CFGRECOVERY} ${CFGR_LSW_FLAGS} $< > $@ 2>&1

%.rt.memres : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${MEMCHECK} ${CFGRECOVERY} ${CFGR_RT_FLAGS} $< > $@ 2>&1

check-diff : ${BASE_TESTS}
	@ > check-diff
if WITH_VALGRIND
	@ for t in ${BASE_TESTS}; do \
          TNAME=`basename $${t} .res`; \
          if test "$${t}" = "$${TNAME}.lsw.res"; then \
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




