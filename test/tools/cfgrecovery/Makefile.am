## Process this file with automake to produce Makefile.in
AUTOMAKE_OPTIONS=parallel-tests
CHECKRESULTS=${top_srcdir}/test/check-results.sh

TEST_SAMPLES_DIR=@TEST_SAMPLES_DIR@

LOG_COMPILER=${SHELL} ${CHECKRESULTS}

CLEANFILES=${TESTS} ${TMPFILES} ${BUILT_SOURCES}

CFGRECOVERY = ${top_builddir}/tools/cfgrecovery/cfgrecovery
CFGR_COMMON_FLAGS = -D -c ${builddir}/config.cfg -f mc
CFGR_FLD_FLAGS = ${CFGR_COMMON_FLAGS} -d flood
CFGR_LSW_FLAGS = ${CFGR_COMMON_FLAGS} -d linear
CFGR_RT_FLAGS = ${CFGR_COMMON_FLAGS} -d recursive
CFGR_SCONC_FLAGS = ${CFGR_COMMON_FLAGS} -d sim=concrete
CFGR_SSYMB_FLAGS = ${CFGR_COMMON_FLAGS} -d sim=symbolic

if HAVE_SOLVER
X86_32_SYM_TESTS = \
	x86_32-cfgrecovery-01.sym.res \
        \
	x86_32-simulator-01.sym.res \
	x86_32-simulator-02.sym.res \
	x86_32-simulator-03.sym.res \
	x86_32-simulator-04.sym.res \
	x86_32-simulator-05.sym.res \
	\
	x86_32-simulator-aaa.sym.res \
	x86_32-simulator-aad.sym.res \
	x86_32-simulator-aam.sym.res \
	x86_32-simulator-aas.sym.res \
	x86_32-simulator-add.sym.res \
	x86_32-simulator-adcsbb.sym.res \
	\
	x86_32-simulator-booleans.sym.res \
	x86_32-simulator-bound.sym.res \
	x86_32-simulator-bsf.sym.res \
	x86_32-simulator-bsr.sym.res \
	x86_32-simulator-bswap.sym.res \
	x86_32-simulator-bt-01.sym.res \
	x86_32-simulator-bt-02.sym.res \
	x86_32-simulator-btc.sym.res \
	x86_32-simulator-btr.sym.res \
	x86_32-simulator-bts.sym.res \
	\
	x86_32-simulator-CF.sym.res \
	x86_32-simulator-call.sym.res \
	x86_32-simulator-cbw.sym.res \
	x86_32-simulator-cmov.sym.res \
	x86_32-simulator-cmps-01.sym.res \
	x86_32-simulator-cmps-02.sym.res \
	x86_32-simulator-cmpxchg.sym.res \
	x86_32-simulator-cwdcdq.sym.res \
	\
	x86_32-simulator-daadas.sym.res \
	x86_32-simulator-div.sym.res \
	\
	x86_32-simulator-enter-leave-01.sym.res \
	x86_32-simulator-enter-leave-02.sym.res \
	\
	x86_32-simulator-idiv.sym.res \
	x86_32-simulator-imul-01.sym.res \
	x86_32-simulator-imul-02.sym.res \
	x86_32-simulator-imul-03.sym.res \
	x86_32-simulator-int.sym.res \
	x86_32-simulator-int3.sym.res \
	x86_32-simulator-into-01.sym.res \
	x86_32-simulator-into-02.sym.res \
	\
	x86_32-simulator-lsahf.sym.res \
	x86_32-simulator-lods.sym.res \
	x86_32-simulator-loop.sym.res \
	\
	x86_32-simulator-movbe.sym.res \
	x86_32-simulator-movs.sym.res \
	x86_32-simulator-movsxz.sym.res \
	x86_32-simulator-mul.sym.res \
	\
	x86_32-simulator-neg.sym.res \
	\
	x86_32-simulator-popcnt.sym.res \
	x86_32-simulator-pushpop-01.sym.res \
	x86_32-simulator-pushpop-02.sym.res \
	x86_32-simulator-pushpop-03.sym.res \
	x86_32-simulator-pushpop-04.sym.res \
	x86_32-simulator-pushpop-05.sym.res \
	x86_32-simulator-pushpop-06.sym.res \
	x86_32-simulator-pushfpopf.sym.res \
	x86_32-simulator-pushapopa.sym.res \
	\
	x86_32-simulator-rep-01.sym.res \
	x86_32-simulator-rep-02.sym.res \
	x86_32-simulator-rep-03.sym.res \
	x86_32-simulator-rep-04.sym.res \
	\
	x86_32-simulator-rotate-01.sym.res \
	x86_32-simulator-rotate-02.sym.res \
	x86_32-simulator-rotate-03.sym.res \
	x86_32-simulator-rotate-04.sym.res \
	\
	x86_32-simulator-shift-01.sym.res \
	x86_32-simulator-shift-02.sym.res \
	x86_32-simulator-shift-03.sym.res \
	x86_32-simulator-shift-04.sym.res \
	\
	x86_32-simulator-scas.sym.res \
	x86_32-simulator-sub.sym.res \
	x86_32-simulator-setcc.sym.res \
	\
	x86_32-simulator-xadd.sym.res \
	x86_32-simulator-xchg.sym.res \
	\
	x86_32-gcd.sym.res \
        \
        ${dummy}
endif

X86_32_SC_TESTS = \
	x86_32-cfgrecovery-01.sc.res \
        \
	x86_32-simulator-01.sc.res \
	x86_32-simulator-02.sc.res \
	x86_32-simulator-03.sc.res \
	x86_32-simulator-04.sc.res \
	x86_32-simulator-05.sc.res \
	\
	x86_32-simulator-aaa.sc.res \
	x86_32-simulator-aad.sc.res \
	x86_32-simulator-aam.sc.res \
	x86_32-simulator-aas.sc.res \
	x86_32-simulator-add.sc.res \
	x86_32-simulator-adcsbb.sc.res \
	\
	x86_32-simulator-booleans.sc.res \
	x86_32-simulator-bound.sc.res \
	x86_32-simulator-bsf.sc.res \
	x86_32-simulator-bsr.sc.res \
	x86_32-simulator-bswap.sc.res \
	x86_32-simulator-bt-01.sc.res \
	x86_32-simulator-bt-02.sc.res \
	x86_32-simulator-btc.sc.res \
	x86_32-simulator-btr.sc.res \
	x86_32-simulator-bts.sc.res \
	\
	x86_32-simulator-CF.sc.res \
	x86_32-simulator-call.sc.res \
	x86_32-simulator-cbw.sc.res \
	x86_32-simulator-cmov.sc.res \
	x86_32-simulator-cmps-01.sc.res \
	x86_32-simulator-cmps-02.sc.res \
	x86_32-simulator-cmpxchg.sc.res \
	x86_32-simulator-cwdcdq.sc.res \
	\
	x86_32-simulator-daadas.sc.res \
	x86_32-simulator-div.sc.res \
	\
	x86_32-simulator-enter-leave-01.sc.res \
	x86_32-simulator-enter-leave-02.sc.res \
	\
	x86_32-simulator-idiv.sc.res \
	x86_32-simulator-imul-01.sc.res \
	x86_32-simulator-imul-02.sc.res \
	x86_32-simulator-imul-03.sc.res \
	x86_32-simulator-int.sc.res \
	x86_32-simulator-int3.sc.res \
	x86_32-simulator-into-01.sc.res \
	x86_32-simulator-into-02.sc.res \
	\
	x86_32-simulator-lsahf.sc.res \
	x86_32-simulator-lods.sc.res \
	x86_32-simulator-loop.sc.res \
	\
	x86_32-simulator-movbe.sc.res \
	x86_32-simulator-movs.sc.res \
	x86_32-simulator-movsxz.sc.res \
	x86_32-simulator-mul.sc.res \
	\
	x86_32-simulator-neg.sc.res \
	\
	x86_32-simulator-popcnt.sc.res \
	x86_32-simulator-pushpop-01.sc.res \
	x86_32-simulator-pushpop-02.sc.res \
	x86_32-simulator-pushpop-03.sc.res \
	x86_32-simulator-pushpop-04.sc.res \
	x86_32-simulator-pushpop-05.sc.res \
	x86_32-simulator-pushpop-06.sc.res \
	x86_32-simulator-pushfpopf.sc.res \
	x86_32-simulator-pushapopa.sc.res \
	\
	x86_32-simulator-rep-01.sc.res \
	x86_32-simulator-rep-02.sc.res \
	x86_32-simulator-rep-03.sc.res \
	x86_32-simulator-rep-04.sc.res \
	\
	x86_32-simulator-rotate-01.sc.res \
	x86_32-simulator-rotate-02.sc.res \
	x86_32-simulator-rotate-03.sc.res \
	x86_32-simulator-rotate-04.sc.res \
	\
	x86_32-simulator-shift-01.sc.res \
	x86_32-simulator-shift-02.sc.res \
	x86_32-simulator-shift-03.sc.res \
	x86_32-simulator-shift-04.sc.res \
	\
	x86_32-simulator-scas.sc.res \
	x86_32-simulator-sub.sc.res \
	x86_32-simulator-setcc.sc.res \
	\
	x86_32-simulator-xadd.sc.res \
	x86_32-simulator-xchg.sc.res \
	\
	x86_32-gcd.sc.res \
        \
        ${dummy}

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
if  HAVE_SOLVER
X86_32_SYM_TESTS += \
	x86_32-cfgrecovery-01.sym.memres \
        \
	x86_32-simulator-01.sym.memres \
	x86_32-simulator-02.sym.memres \
	x86_32-simulator-03.sym.memres \
	x86_32-simulator-04.sym.memres \
	x86_32-simulator-05.sym.memres \
	\
	x86_32-simulator-aaa.sym.memres \
	x86_32-simulator-aad.sym.memres \
	x86_32-simulator-aam.sym.memres \
	x86_32-simulator-aas.sym.memres \
	x86_32-simulator-add.sym.memres \
	x86_32-simulator-adcsbb.sym.memres \
	\
	x86_32-simulator-booleans.sym.memres \
	x86_32-simulator-bound.sym.memres \
	x86_32-simulator-bsf.sym.memres \
	x86_32-simulator-bsr.sym.memres \
	x86_32-simulator-bswap.sym.memres \
	x86_32-simulator-bt-01.sym.memres \
	x86_32-simulator-bt-02.sym.memres \
	x86_32-simulator-btc.sym.memres \
	x86_32-simulator-btr.sym.memres \
	x86_32-simulator-bts.sym.memres \
	\
	x86_32-simulator-CF.sym.memres \
	x86_32-simulator-call.sym.memres \
	x86_32-simulator-cbw.sym.memres \
	x86_32-simulator-cmov.sym.memres \
	x86_32-simulator-cmps-01.sym.memres \
	x86_32-simulator-cmps-02.sym.memres \
	x86_32-simulator-cmpxchg.sym.memres \
	x86_32-simulator-cwdcdq.sym.memres \
	\
	x86_32-simulator-daadas.sym.memres \
	x86_32-simulator-div.sym.memres \
	\
	x86_32-simulator-enter-leave-01.sym.memres \
	x86_32-simulator-enter-leave-02.sym.memres \
	\
	x86_32-simulator-idiv.sym.memres \
	x86_32-simulator-imul-01.sym.memres \
	x86_32-simulator-imul-02.sym.memres \
	x86_32-simulator-imul-03.sym.memres \
	x86_32-simulator-int.sym.memres \
	x86_32-simulator-int3.sym.memres \
	x86_32-simulator-into-01.sym.memres \
	x86_32-simulator-into-02.sym.memres \
	\
	x86_32-simulator-lsahf.sym.memres \
	x86_32-simulator-lods.sym.memres \
	x86_32-simulator-loop.sym.memres \
	\
	x86_32-simulator-movbe.sym.memres \
	x86_32-simulator-movs.sym.memres \
	x86_32-simulator-movsxz.sym.memres \
	x86_32-simulator-mul.sym.memres \
	\
	x86_32-simulator-neg.sym.memres \
	\
	x86_32-simulator-popcnt.sym.memres \
	x86_32-simulator-pushpop-01.sym.memres \
	x86_32-simulator-pushpop-02.sym.memres \
	x86_32-simulator-pushpop-03.sym.memres \
	x86_32-simulator-pushpop-04.sym.memres \
	x86_32-simulator-pushpop-05.sym.memres \
	x86_32-simulator-pushpop-06.sym.memres \
	x86_32-simulator-pushfpopf.sym.memres \
	x86_32-simulator-pushapopa.sym.memres \
	\
	x86_32-simulator-rep-01.sym.memres \
	x86_32-simulator-rep-02.sym.memres \
	x86_32-simulator-rep-03.sym.memres \
	x86_32-simulator-rep-04.sym.memres \
	\
	x86_32-simulator-rotate-01.sym.memres \
	x86_32-simulator-rotate-02.sym.memres \
	x86_32-simulator-rotate-03.sym.memres \
	x86_32-simulator-rotate-04.sym.memres \
	\
	x86_32-simulator-shift-01.sym.memres \
	x86_32-simulator-shift-02.sym.memres \
	x86_32-simulator-shift-03.sym.memres \
	x86_32-simulator-shift-04.sym.memres \
	\
	x86_32-simulator-scas.sym.memres \
	x86_32-simulator-sub.sym.memres \
	x86_32-simulator-setcc.sym.memres \
	\
	x86_32-simulator-xadd.sym.memres \
	x86_32-simulator-xchg.sym.memres \
	\
	x86_32-gcd.sym.memres \
        \
        ${dummy}
endif # HAVE_SOLVER

X86_32_SC_TESTS += \
	x86_32-cfgrecovery-01.sc.memres \
        \
	x86_32-simulator-01.sc.memres \
	x86_32-simulator-02.sc.memres \
	x86_32-simulator-03.sc.memres \
	x86_32-simulator-04.sc.memres \
	x86_32-simulator-05.sc.memres \
	\
	x86_32-simulator-aaa.sc.memres \
	x86_32-simulator-aad.sc.memres \
	x86_32-simulator-aam.sc.memres \
	x86_32-simulator-aas.sc.memres \
	x86_32-simulator-add.sc.memres \
	x86_32-simulator-adcsbb.sc.memres \
	\
	x86_32-simulator-booleans.sc.memres \
	x86_32-simulator-bound.sc.memres \
	x86_32-simulator-bsf.sc.memres \
	x86_32-simulator-bsr.sc.memres \
	x86_32-simulator-bswap.sc.memres \
	x86_32-simulator-bt-01.sc.memres \
	x86_32-simulator-bt-02.sc.memres \
	x86_32-simulator-btc.sc.memres \
	x86_32-simulator-btr.sc.memres \
	x86_32-simulator-bts.sc.memres \
	\
	x86_32-simulator-CF.sc.memres \
	x86_32-simulator-call.sc.memres \
	x86_32-simulator-cbw.sc.memres \
	x86_32-simulator-cmov.sc.memres \
	x86_32-simulator-cmps-01.sc.memres \
	x86_32-simulator-cmps-02.sc.memres \
	x86_32-simulator-cmpxchg.sc.memres \
	x86_32-simulator-cwdcdq.sc.memres \
	\
	x86_32-simulator-daadas.sc.memres \
	x86_32-simulator-div.sc.memres \
	\
	x86_32-simulator-enter-leave-01.sc.memres \
	x86_32-simulator-enter-leave-02.sc.memres \
	\
	x86_32-simulator-idiv.sc.memres \
	x86_32-simulator-imul-01.sc.memres \
	x86_32-simulator-imul-02.sc.memres \
	x86_32-simulator-imul-03.sc.memres \
	x86_32-simulator-int.sc.memres \
	x86_32-simulator-int3.sc.memres \
	x86_32-simulator-into-01.sc.memres \
	x86_32-simulator-into-02.sc.memres \
	\
	x86_32-simulator-lsahf.sc.memres \
	x86_32-simulator-lods.sc.memres \
	x86_32-simulator-loop.sc.memres \
	\
	x86_32-simulator-movbe.sc.memres \
	x86_32-simulator-movs.sc.memres \
	x86_32-simulator-movsxz.sc.memres \
	x86_32-simulator-mul.sc.memres \
	\
	x86_32-simulator-neg.sc.memres \
	\
	x86_32-simulator-popcnt.sc.memres \
	x86_32-simulator-pushpop-01.sc.memres \
	x86_32-simulator-pushpop-02.sc.memres \
	x86_32-simulator-pushpop-03.sc.memres \
	x86_32-simulator-pushpop-04.sc.memres \
	x86_32-simulator-pushpop-05.sc.memres \
	x86_32-simulator-pushpop-06.sc.memres \
	x86_32-simulator-pushfpopf.sc.memres \
	x86_32-simulator-pushapopa.sc.memres \
	\
	x86_32-simulator-rep-01.sc.memres \
	x86_32-simulator-rep-02.sc.memres \
	x86_32-simulator-rep-03.sc.memres \
	x86_32-simulator-rep-04.sc.memres \
	\
	x86_32-simulator-rotate-01.sc.memres \
	x86_32-simulator-rotate-02.sc.memres \
	x86_32-simulator-rotate-03.sc.memres \
	x86_32-simulator-rotate-04.sc.memres \
	\
	x86_32-simulator-shift-01.sc.memres \
	x86_32-simulator-shift-02.sc.memres \
	x86_32-simulator-shift-03.sc.memres \
	x86_32-simulator-shift-04.sc.memres \
	\
	x86_32-simulator-scas.sc.memres \
	x86_32-simulator-sub.sc.memres \
	x86_32-simulator-setcc.sc.memres \
	\
	x86_32-simulator-xadd.sc.memres \
	x86_32-simulator-xchg.sc.memres \
	\
	x86_32-gcd.sc.memres \
        \
        ${dummy}

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
	x86_32-cfgrecovery-01.fld.memres \
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
	x86_32-cfgrecovery-01.lsw.memres \
        \
        ${dummy}
endif

BASE_TESTS = ${X86_32_SYM_TESTS} \
             ${X86_32_SC_TESTS} \
             ${X86_32_RT_TESTS} \
             ${X86_32_FLD_TESTS} \
             ${X86_32_LSW_TESTS}

#BASE_TESTS = ${X86_32_FLD_TESTS} ${X86_32_LSW_TESTS}


TESTS = \
	${BASE_TESTS} \
	 check-diff

EXTRA_DIST=${TESTS:%=%.result}

MEMCHECK_FLAGS=-q --num-callers=20 --leak-check=full
MEMCHECK=${LIBTOOL} --mode=execute valgrind --tool=memcheck ${MEMCHECK_FLAGS}


x86_32-%.sc.res : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${CFGRECOVERY} ${CFGR_SCONC_FLAGS} -b elf32-i386 $< > $@ 2>&1

x86_32-%.sym.res : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${CFGRECOVERY} ${CFGR_SSYMB_FLAGS} -b elf32-i386  $< > $@ 2>&1

x86_32-%.fld.res : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${CFGRECOVERY} ${CFGR_FLD_FLAGS} -b elf32-i386  $< > $@ 2>&1

x86_32-%.lsw.res : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${CFGRECOVERY} ${CFGR_LSW_FLAGS} -b elf32-i386  $< > $@ 2>&1

x86_32-%.rt.res : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${CFGRECOVERY} ${CFGR_RT_FLAGS} -b elf32-i386  $< > $@ 2>&1

x86_32-%.fld.memres : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${MEMCHECK} ${CFGRECOVERY} ${CFGR_FLD_FLAGS} -b elf32-i386 $< > $@ 2>&1

x86_32-%.lsw.memres : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${MEMCHECK} ${CFGRECOVERY} ${CFGR_LSW_FLAGS} -b elf32-i386 $< > $@ 2>&1

x86_32-%.rt.memres : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${MEMCHECK} ${CFGRECOVERY} ${CFGR_RT_FLAGS} -b elf32-i386 $< > $@ 2>&1

x86_32-%.sym.memres : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${MEMCHECK} ${CFGRECOVERY} ${CFGR_SSYMB_FLAGS} -b elf32-i386 $< > $@ 2>&1

x86_32-%.sc.memres : ${TEST_SAMPLES_DIR}/x86_32-%.bin ${CFGRECOVERY}
	@echo "generate $@"
	@${MEMCHECK} ${CFGRECOVERY} ${CFGR_SCONC_FLAGS} -b elf32-i386 $< > $@ 2>&1

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

maintainer-clean-local:
	rm -fr $(top_srcdir)/test/tools/cfgrecovery/Makefile.in
