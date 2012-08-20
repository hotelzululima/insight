## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${top_srcdir}/test/check-results.sh

TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

LOG_COMPILER=${SHELL} ${CHECKRESULTS}

CLEANFILES=${TESTS} ${TMPFILES} ${BUILT_SOURCES}

CFGRECOVERY = ${top_builddir}/tools/cfgrecovery/cfgrecovery
CFGR_FLD_FLAGS = -d flood
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

X86_32_FLD_TESTS = \
	x86_32-aaa.fld.res \
	x86_32-aad.fld.res \
	x86_32-aam.fld.res \
	x86_32-aas.fld.res \
	x86_32-and.fld.res \
        \
        x86_32-bound.fld.res \
        x86_32-bsf.fld.res \
        x86_32-bsr.fld.res \
        x86_32-bswap.fld.res \
        x86_32-bt.fld.res \
        x86_32-btc.fld.res \
        x86_32-btr.fld.res \
        x86_32-bts.fld.res \
        \
	x86_32-call.fld.res \
	x86_32-cmp.fld.res \
	x86_32-cmps.fld.res \
	x86_32-cmpxchg.fld.res \
	\
	x86_32-daadas.fld.res \
	x86_32-div.fld.res \
        \
        x86_32-enter-leave.fld.res \
        \
	x86_32-idiv.fld.res \
	x86_32-imul.fld.res \
	x86_32-int.fld.res \
	\
	x86_32-jcc.fld.res \
	x86_32-jmp.fld.res \
        \
        x86_32-lsahf.fld.res \
	x86_32-lea.fld.res \
	x86_32-lods.fld.res \
	x86_32-loop.fld.res \
        \
	x86_32-mov.fld.res \
	x86_32-movbe.fld.res \
	x86_32-movs.fld.res \
	x86_32-movsxz.fld.res \
	x86_32-mul.fld.res \
        \
	x86_32-neg.fld.res \
	x86_32-nop.fld.res \
	x86_32-not.fld.res \
	x86_32-or.fld.res \
        \
	x86_32-popcnt.fld.res \
	x86_32-pop.fld.res \
	x86_32-pop16.fld.res \
	x86_32-popa.fld.res \
	x86_32-popa16.fld.res \
	x86_32-push.fld.res \
	x86_32-pusha.fld.res \
	x86_32-push16.fld.res \
        \
	x86_32-rotate.fld.res \
        \
	x86_32-scas.fld.res \
	x86_32-shift.fld.res \
	x86_32-sbb.fld.res \
	x86_32-setcc.fld.res \
        \
	x86_32-xadd.fld.res \
	x86_32-xchg.fld.res \
	x86_32-xor.fld.res \
        \
	x86_32-cfgrecovery-01.fld.res \
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

X86_32_FLD_TESTS += \
	x86_32-aaa.fld.memres \
	x86_32-aad.fld.memres \
	x86_32-aam.fld.memres \
	x86_32-aas.fld.memres \
	x86_32-and.fld.memres \
        \
        x86_32-bound.fld.memres \
        x86_32-bsf.fld.memres \
        x86_32-bsr.fld.memres \
        x86_32-bswap.fld.memres \
        x86_32-bt.fld.memres \
        x86_32-btc.fld.memres \
        x86_32-btr.fld.memres \
        x86_32-bts.fld.memres \
        \
        x86_32-call.fld.memres \
	x86_32-cmp.fld.memres \
	x86_32-cmps.fld.memres \
	x86_32-cmpxchg.fld.memres \
        \
	x86_32-daadas.fld.memres \
	x86_32-div.fld.memres \
        \
        x86_32-enter-leave.fld.memres \
        \
	x86_32-idiv.fld.memres \
	x86_32-imul.fld.memres \
	x86_32-int.fld.memres \
	\
	x86_32-jcc.fld.memres \
	x86_32-jmp.fld.memres \
        \
        x86_32-lsahf.fld.memres \
	x86_32-lea.fld.memres \
	x86_32-lods.fld.memres \
	x86_32-loop.fld.memres \
        \
	x86_32-mov.fld.memres \
	x86_32-movbe.fld.memres \
	x86_32-movs.fld.memres \
	x86_32-movsxz.fld.memres \
	x86_32-mul.fld.memres \
        \
	x86_32-neg.fld.memres \
	x86_32-nop.fld.memres \
	x86_32-not.fld.memres \
	x86_32-or.fld.memres \
        \
	x86_32-popcnt.fld.memres \
	x86_32-pop.fld.memres \
	x86_32-pop16.fld.memres \
	x86_32-popa.fld.memres \
	x86_32-popa16.fld.memres \
	x86_32-push.fld.memres \
	x86_32-pusha.fld.memres \
	x86_32-push16.fld.memres \
        \
	x86_32-rotate.fld.memres \
        \
	x86_32-scas.fld.memres \
	x86_32-shift.fld.memres \
	x86_32-sbb.fld.memres \
	x86_32-setcc.fld.memres \
        \
	x86_32-xadd.fld.memres \
	x86_32-xchg.fld.memres \
	x86_32-xor.fld.memres \
        \
	x86_32-cfgrecovery-01.fld.res \
        \
        ${dummy}
endif

BASE_TESTS = ${X86_32_RT_TESTS} ${X86_32_FLD_TESTS} 


TESTS = \
	${BASE_TESTS} \
	 check-diff

EXTRA_DIST=${TESTS:%=%.result}

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=yes
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}


%.fld.res : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${CFGRECOVERY} ${CFGR_FLD_FLAGS}  $< > $@ 2>&1

%.rt.res : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${CFGRECOVERY} ${CFGR_RT_FLAGS}  $< > $@ 2>&1

%.fld.memres : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${MEMCHECK} ${CFGRECOVERY} ${CFGR_FLD_FLAGS} $< > $@ 2>&1

%.rt.memres : ${TEST_SAMPLES_DIR}/%.bin ${CFGRECOVERY}
	 @${MEMCHECK} ${CFGRECOVERY} ${CFGR_RT_FLAGS} $< > $@ 2>&1

check-diff : ${BASE_TESTS}
	@ > check-diff
if WITH_VALGRIND
	@ for t in ${BASE_TESTS}; do \
          TNAME=`basename $${t} .res`; \
          if test "$${t}" = "$${TNAME}.fld.res"; then \
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




