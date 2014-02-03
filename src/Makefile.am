## Process this file with automake to produce Makefile.in
AM_CPPFLAGS = @BINUTILS_CFLAGS@
AM_LDFLAGS = @BINUTILS_LDFLAGS@

AUTOMAKE_OPTIONS=subdir-objects

CLEANFILES=
BUILT_SOURCES= 

all:

## analyses module
analyses_sources = \
        analyses/cfgrecovery/AlgorithmFactory.hh \
        analyses/cfgrecovery/AlgorithmFactory.cc \
        \
        analyses/cfgrecovery/AbstractContext.hh \
        analyses/cfgrecovery/AbstractContext.cc \
        analyses/cfgrecovery/AbstractDomainContext.hh \
        analyses/cfgrecovery/AbstractDomainContext.ii \
        analyses/cfgrecovery/AbstractDomainStepper.hh \
        analyses/cfgrecovery/AbstractDomainStepper.ii \
        analyses/cfgrecovery/AbstractMemoryTraversal.hh \
        analyses/cfgrecovery/AbstractMemoryTraversal.ii \
        analyses/cfgrecovery/AbstractProgramPoint.hh \
        analyses/cfgrecovery/AbstractProgramPoint.ii \
        analyses/cfgrecovery/AbstractState.hh \
        analyses/cfgrecovery/AbstractState.ii \
        analyses/cfgrecovery/AbstractStateSpace.hh \
        analyses/cfgrecovery/AbstractStepper.hh \
        analyses/cfgrecovery/DomainSimulator.hh \
        analyses/cfgrecovery/DummyStateSpace.hh \
        analyses/cfgrecovery/FloodTraversal.hh \
        analyses/cfgrecovery/FloodTraversalStepper.cc \
        analyses/cfgrecovery/LinearSweep.hh \
        analyses/cfgrecovery/LinearSweepStepper.cc \
        analyses/cfgrecovery/MicrocodeAddressProgramPoint.cc \
        analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh \
        analyses/cfgrecovery/NullContext.cc \
        analyses/cfgrecovery/NullContext.hh \
        analyses/cfgrecovery/RecursiveTraversal.hh \
        analyses/cfgrecovery/RecursiveTraversalContext.cc \
        analyses/cfgrecovery/RecursiveTraversalStepper.cc \
        analyses/cfgrecovery/SingleContextStateSpace.hh \
        analyses/cfgrecovery/SingleContextStateSpace.ii \
        \
	analyses/microcode_exec.hh	\
	analyses/microcode_exec.ii	\
	analyses/Wp.cc			\
	analyses/Wp.hh			\
	analyses/slicing/Slicing.hh	\
	analyses/slicing/Slicing.cc

## utils module
utils_source = \
        utils/ConfigTable.hh	\
        utils/ConfigTable.cc	\
        utils/graph.hh		\
        utils/graph.ii		\
	utils/logs.cc		\
	utils/logs.hh		\
	utils/Object.cc		\
	utils/Object.hh		\
	utils/bv-manip.hh	\
	utils/infrastructure.hh	\
	utils/map-helpers.hh	\
	utils/Option.hh		\
	utils/path.hh		\
	utils/path.ii		\
	utils/tools.cc		\
	utils/tools.hh

## kernel module
kernel_source = \
	kernel/Address.cc 		\
	kernel/Address.hh 		\
	kernel/Annotable.cc 		\
	kernel/Annotable.hh 		\
	kernel/Annotation.hh 		\
	kernel/Architecture.cc 		\
	kernel/Architecture.hh 	  	\
	kernel/Architecture_ARM.cc    	\
	kernel/Architecture_ARM.hh    	\
	kernel/Architecture_SPARC.cc    \
	kernel/Architecture_SPARC.hh    \
	kernel/Architecture_X86_32.cc 	\
	kernel/Architecture_X86_32.hh 	\
	kernel/Architecture_X86_64.cc 	\
	kernel/Architecture_X86_64.hh 	\
	kernel/Expressions.cc	 	\
	kernel/Expressions.hh	 	\
	kernel/insight.cc	 	\
	kernel/insight.hh	 	\
	kernel/Memory.hh 		\
	kernel/Memory.ii 		\
	kernel/RegisterMap.hh 		\
	kernel/RegisterMap.ii 		\
	kernel/Value.cc 		\
	kernel/Value.hh 		\
	kernel/annotations/AbstractAnnotation.hh	\
	kernel/annotations/ListAnnotation.hh	\
	kernel/annotations/SolvedJmpAnnotation.hh	\
	kernel/annotations/SolvedJmpAnnotation.cc	\
	kernel/annotations/NextInstAnnotation.cc     \
	kernel/annotations/NextInstAnnotation.hh	\
	kernel/annotations/AsmAnnotation.hh	\
	kernel/annotations/AsmAnnotation.cc     \
	kernel/annotations/StringAnnotation.hh	\
	kernel/annotations/BooleanAnnotation.hh \
	kernel/annotations/CallRetAnnotation.hh \
	kernel/annotations/CallRetAnnotation.cc \
	kernel/annotations/GenericAnnotation.hh \
	kernel/annotations/ExprAnnotation.cc 	\
	kernel/annotations/ExprAnnotation.hh 	\
	kernel/expressions/FunctionRewritingRule.hh \
	kernel/expressions/FunctionRewritingRule.cc \
	kernel/expressions/BottomUpRewritePatternRule.hh 	\
	kernel/expressions/BottomUpRewritePatternRule.cc 	\
	kernel/expressions/BottomUpApplyVisitor.hh \
	kernel/expressions/BottomUpApplyVisitor.cc \
	kernel/expressions/ConditionalSet.cc 	\
	kernel/expressions/ConditionalSet.hh	\
	kernel/expressions/exprutils.hh		\
	kernel/expressions/exprutils.cc		\
	kernel/expressions/exprutils.ii		\
	kernel/expressions/ExprVisitor.hh	\
	kernel/expressions/ExprRewritingFunctions.hh	\
	kernel/expressions/ExprRewritingFunctions.cc	\
	kernel/expressions/ExprRewritingRule.hh	\
	kernel/expressions/ExprRewritingRule.cc	\
	kernel/expressions/ExprReplaceSubtermRule.hh	\
	kernel/expressions/ExprReplaceSubtermRule.cc	\
	kernel/expressions/ExprSolver.hh	\
	kernel/expressions/ExprSolver.cc	\
	kernel/expressions/ExprProcessSolver.hh	\
	kernel/expressions/ExprProcessSolver.cc	\
	kernel/expressions/ExprMathsatSolver.hh	\
	kernel/expressions/ExprMathsatSolver.cc	\
	kernel/expressions/Operators.cc   	\
	kernel/expressions/Operators.def  	\
	kernel/expressions/Operators.hh   	\
	kernel/expressions/PatternMatching.cc 	\
	kernel/expressions/PatternMatching.hh 	\
	kernel/Microcode.cc			\
	kernel/Microcode.hh			\
	kernel/microcode/MicrocodeAddress.cc	\
	kernel/microcode/MicrocodeAddress.hh	\
	kernel/microcode/MicrocodeArchitecture.cc	\
	kernel/microcode/MicrocodeArchitecture.hh	\
	kernel/microcode/MicrocodeNode.cc	\
	kernel/microcode/MicrocodeNode.hh	\
	kernel/microcode/MicrocodeStatements.cc	\
	kernel/microcode/MicrocodeStatements.hh	\
	kernel/microcode/MicrocodeStore.hh	\
	kernel/SymbolTable.cc 	 		\
	kernel/SymbolTable.hh


BUILT_SOURCES+= \
	${kernel_built_sources}

kernel_cleanfiles = \
	${kernel_built_sources}


## domains module
domains_source = \
        domains/symbolic/SymbolicStepper.hh \
        domains/symbolic/SymbolicStepper.cc \
        domains/symbolic/SymbolicValue.hh \
        domains/symbolic/SymbolicValue.cc \
        domains/symbolic/SymbolicMemory.hh \
        domains/symbolic/SymbolicMemory.cc \
        domains/symbolic/SymbolicExprSemantics.hh \
        domains/symbolic/SymbolicExprSemantics.cc \
        domains/symbolic/SymbolicContext.hh \
        domains/symbolic/SymbolicContext.cc \
        \
	domains/ExprSemantics.hh                   \
	domains/ExprSemantics.ii                   \
	domains/common/ConcreteAddressMemory.hh    \
	domains/common/ConcreteAddressMemory.ii    \
	domains/common/ConcreteProgramPoint.cc     \
	domains/common/ConcreteProgramPoint.hh     \
        \
	domains/concrete/ConcreteContext.hh        \
	domains/concrete/ConcreteContext.cc        \
	domains/concrete/ConcreteStepper.hh        \
	domains/concrete/ConcreteStepper.cc        \
	domains/concrete/ConcreteAddress.cc        \
	domains/concrete/ConcreteAddress.hh        \
	domains/concrete/ConcreteExprSemantics.cc  \
	domains/concrete/ConcreteExprSemantics.hh  \
	domains/concrete/ConcreteMemory.cc         \
	domains/concrete/ConcreteMemory.hh         \
	domains/concrete/ConcreteValue.cc          \
	domains/concrete/ConcreteValue.hh          \
        \
	domains/interval/interval_context.cc       \
	domains/interval/interval_context.hh       \
	domains/interval/IntervalExprSemantics.cc  \
	domains/interval/IntervalExprSemantics.hh  \
	domains/interval/IntervalAddress.hh        \
	domains/interval/IntervalAddress.cc        \
	domains/interval/IntervalMemory.cc         \
	domains/interval/IntervalMemory.hh         \
	domains/interval/IntervalValue.cc          \
	domains/interval/IntervalValue.hh          \
	domains/sets/SetsValue.hh                  \
	domains/sets/SetsValue.cc                  \
	domains/sets/SetsAddress.hh                \
	domains/sets/SetsAddress.cc                \
	domains/sets/SetsMemory.hh                 \
	domains/sets/SetsMemory.cc                 \
	domains/sets/SetsExprSemantics.hh          \
	domains/sets/SetsExprSemantics.cc          \
	domains/sets/SetsContext.hh                \
	domains/sets/SetsContext.cc

## io module
io_sources = \
	io/binary/BinaryLoader.cc 		\
	io/binary/BinaryLoader.hh 		\
	io/binary/BinutilsBinaryLoader.cc	\
	io/binary/BinutilsBinaryLoader.hh 	\
	io/binary/StubFactory.hh 		\
	io/binary/BinutilsStubFactory.hh 	\
	io/binary/BinutilsStubFactory.cc 	\
	io/binary/ELF_x86_32_StubFactory.cc 	\
        \
        io/expressions/expr-writer.hh		\
        io/expressions/expr-writer.cc		\
        io/expressions/smtlib-writer.hh		\
        io/expressions/smtlib-writer.cc		\
	io/expressions/expr-parser.hh 		\
	io/expressions/ExprLexer.hh 		\
	io/expressions/ExprLexer.ll		\
	io/expressions/ExprParser.yy 		\
	io/microcode/asm-writer.cc      	\
	io/microcode/asm-writer.hh      	\
	io/microcode/dot-writer.cc      	\
	io/microcode/dot-writer.hh      	\
	io/microcode/MicrocodeLoader.cc 	\
	io/microcode/MicrocodeLoader.hh 	\
	io/microcode/xml_microcode_parser.cc	\
	io/microcode/xml_microcode_parser.hh 	\
	io/microcode/MicrocodeWriter.cc		\
	io/microcode/MicrocodeWriter.hh		\
	io/microcode/xml_microcode_generator.cc	\
	io/microcode/xml_microcode_generator.hh	\
	io/microcode/xml_annotations.hh  	\
	io/process/ProcessLoader.cc 	 	\
	io/process/ProcessLoader.hh

io_built_sources = \
	io/expressions/stack.hh 	\
	io/expressions/location.hh	\
	io/expressions/position.hh	\
	io/expressions/ExprLexer.cc 	\
	io/expressions/ExprParser.hh  	\
	io/expressions/ExprParser.cc 

io/expressions/stack.hh		\
io/expressions/location.hh	\
io/expressions/position.hh	\
io/expressions/ExprParser.hh 	\
io/expressions/ExprParser.cc:	\
io/expressions/ExprParser.yy
	$(YACC) --output=io/expressions/ExprParser.cc \
		${srcdir}/io/expressions/ExprParser.yy

io/expressions/ExprLexer.hh \
io/expressions/ExprLexer.cc :		\
       io/expressions/ExprLexer.ll	\
       io/expressions/ExprParser.hh
	$(LEX) --outfile=io/expressions/ExprLexer.cc \
		${srcdir}/io/expressions/ExprLexer.ll

BUILT_SOURCES+= \
	${io_built_sources}

io_cleanfiles = \
	${io_built_sources}

## decoder module
arm_decoder= \
	decoders/binutils/arm/arm_decoder.hh	\
	decoders/binutils/arm/arm_decoder.cc	\
        decoders/binutils/arm/arm_parser.yy	\
        decoders/binutils/arm/arm_scanner.ll	\
	decoders/binutils/arm/arm_translate.hh  \
	decoders/binutils/arm/arm_translate.cc  \
	decoders/binutils/arm/arm_translation_functions.hh \
	decoders/binutils/arm/arm_A_instr.cc	\
	decoders/binutils/arm/arm_B_instr.cc	\
	decoders/binutils/arm/arm_C_instr.cc	\
	decoders/binutils/arm/arm_E_instr.cc	\
	decoders/binutils/arm/arm_L_instr.cc	\
	decoders/binutils/arm/arm_M_instr.cc	\
	decoders/binutils/arm/arm_N_instr.cc	\
	decoders/binutils/arm/arm_P_instr.cc	\
	decoders/binutils/arm/arm_R_instr.cc	\
	decoders/binutils/arm/arm_S_instr.cc	\
	decoders/binutils/arm/arm_O_instr.cc	\
	decoders/binutils/arm/arm_U_instr.cc

BUILT_SOURCES+= \
	decoders/binutils/arm/stack.hh 	      	\
	decoders/binutils/arm/location.hh       \
	decoders/binutils/arm/position.hh       \
	decoders/binutils/arm/arm_scanner.hh 	\
	decoders/binutils/arm/arm_scanner.cc 	\
	decoders/binutils/arm/arm_parser.hh  	\
	decoders/binutils/arm/arm_parser.cc

sparc_decoder= \
	decoders/binutils/sparc/sparc_cc.def \
	decoders/binutils/sparc/sparc_decoder.hh \
	decoders/binutils/sparc/sparc_decoder.cc \
        \
	decoders/binutils/sparc/sparc_instr_arithmetics.cc \
	decoders/binutils/sparc/sparc_instr_bits.cc \
	decoders/binutils/sparc/sparc_instr_boolean.cc \
	decoders/binutils/sparc/sparc_instr_call.cc \
	decoders/binutils/sparc/sparc_instr_interrupts.cc \
	decoders/binutils/sparc/sparc_instr_jump.cc \
	decoders/binutils/sparc/sparc_instr_load_store.cc \
	decoders/binutils/sparc/sparc_instr_loops.cc \
	decoders/binutils/sparc/sparc_instr_misc.cc \
	decoders/binutils/sparc/sparc_instr_mov.cc \
	decoders/binutils/sparc/sparc_instr_prefixes.cc \
	decoders/binutils/sparc/sparc_instr_shift.cc \
	decoders/binutils/sparc/sparc_instr_stack.cc \
	decoders/binutils/sparc/sparc_instr_strings.cc \
        \
	decoders/binutils/sparc/sparc_translate.cc  \
	decoders/binutils/sparc/sparc_translate.hh  \
	decoders/binutils/sparc/sparc_translation_functions.hh \
        decoders/binutils/sparc/sparc_parser.yy  \
        decoders/binutils/sparc/sparc_scanner.ll 

BUILT_SOURCES+= \
	decoders/binutils/sparc/stack.hh 	      	\
	decoders/binutils/sparc/location.hh       	\
	decoders/binutils/sparc/position.hh       	\
	decoders/binutils/sparc/sparc_scanner.hh 	\
	decoders/binutils/sparc/sparc_scanner.cc 	\
	decoders/binutils/sparc/sparc_parser.hh  	\
	decoders/binutils/sparc/sparc_parser.cc 

x86_decoder= \
	decoders/binutils/x86/x86_32_decoder.hh \
	decoders/binutils/x86/x86_32_decoder.cc \
	decoders/binutils/x86/x86_64_decoder.hh \
	decoders/binutils/x86/x86_64_decoder.cc \
        \
	decoders/binutils/x86/x86_cc.def \
	decoders/binutils/x86/x86_instr_arithmetics.cc \
	decoders/binutils/x86/x86_instr_bits.cc \
	decoders/binutils/x86/x86_instr_boolean.cc \
	decoders/binutils/x86/x86_instr_call.cc \
	decoders/binutils/x86/x86_instr_interrupts.cc \
	decoders/binutils/x86/x86_instr_jump.cc \
	decoders/binutils/x86/x86_instr_load_store.cc \
	decoders/binutils/x86/x86_instr_loops.cc \
	decoders/binutils/x86/x86_instr_misc.cc \
	decoders/binutils/x86/x86_instr_mov.cc \
	decoders/binutils/x86/x86_instr_prefixes.cc \
	decoders/binutils/x86/x86_instr_shift.cc \
	decoders/binutils/x86/x86_instr_stack.cc \
	decoders/binutils/x86/x86_instr_strings.cc \
        \
	decoders/binutils/x86/x86_translate.cc  \
	decoders/binutils/x86/x86_translate.hh  \
	decoders/binutils/x86/x86_translation_functions.hh \
        decoders/binutils/x86/x86_parser.yy  \
        decoders/binutils/x86/x86_scanner.ll 

BUILT_SOURCES+= \
	decoders/binutils/x86/stack.hh 	      	\
	decoders/binutils/x86/location.hh       \
	decoders/binutils/x86/position.hh       \
	decoders/binutils/x86/x86_scanner.hh \
	decoders/binutils/x86/x86_scanner.cc \
	decoders/binutils/x86/x86_parser.hh  \
	decoders/binutils/x86/x86_parser.cc 

decoders_sources = \
	decoders/Decoder.hh        \
	decoders/Decoder.cc        \
	decoders/DecoderFactory.hh \
	decoders/DecoderFactory.cc \
	decoders/binutils/BinutilsDecoder.hh \
	decoders/binutils/BinutilsDecoder.cc \
        ${arm_decoder}	  \
        ${sparc_decoder}  \
        ${x86_decoder}


decoders/binutils/arm/stack.hh	    \
decoders/binutils/arm/location.hh   \
decoders/binutils/arm/position.hh   \
decoders/binutils/arm/arm_parser.hh \
decoders/binutils/arm/arm_parser.cc:\
  decoders/binutils/arm/arm_parser.yy
	$(YACC) --output=decoders/binutils/arm/arm_parser.cc \
		${srcdir}/decoders/binutils/arm/arm_parser.yy

decoders/binutils/arm/arm_scanner.hh 	\
decoders/binutils/arm/arm_scanner.cc : 	\
       decoders/binutils/arm/arm_scanner.ll	\
       decoders/binutils/arm/arm_parser.hh
	$(LEX) --outfile=decoders/binutils/arm/arm_scanner.cc \
	       --header-file=decoders/binutils/arm/arm_scanner.hh \
		${srcdir}/decoders/binutils/arm/arm_scanner.ll

decoders/binutils/sparc/stack.hh	\
decoders/binutils/sparc/location.hh 	\
decoders/binutils/sparc/position.hh 	\
decoders/binutils/sparc/sparc_parser.hh \
decoders/binutils/sparc/sparc_parser.cc:\
  decoders/binutils/sparc/sparc_parser.yy
	$(YACC) --output=decoders/binutils/sparc/sparc_parser.cc \
		${srcdir}/decoders/binutils/sparc/sparc_parser.yy

decoders/binutils/sparc/sparc_scanner.hh 	\
decoders/binutils/sparc/sparc_scanner.cc : 	\
       decoders/binutils/sparc/sparc_scanner.ll	\
       decoders/binutils/sparc/sparc_parser.hh
	$(LEX) --outfile=decoders/binutils/sparc/sparc_scanner.cc \
	       --header-file=decoders/binutils/sparc/sparc_scanner.hh \
		${srcdir}/decoders/binutils/sparc/sparc_scanner.ll

decoders/binutils/x86/stack.hh		\
decoders/binutils/x86/location.hh 	\
decoders/binutils/x86/position.hh 	\
decoders/binutils/x86/x86_parser.hh 	\
decoders/binutils/x86/x86_parser.cc:	\
  decoders/binutils/x86/x86_parser.yy
	$(YACC) --output=decoders/binutils/x86/x86_parser.cc \
		${srcdir}/decoders/binutils/x86/x86_parser.yy

decoders/binutils/x86/x86_scanner.hh 	\
decoders/binutils/x86/x86_scanner.cc : 	\
       decoders/binutils/x86/x86_scanner.ll 	\
       decoders/binutils/x86/x86_parser.hh
	$(LEX) --outfile=decoders/binutils/x86/x86_scanner.cc \
	       --header-file=decoders/binutils/x86/x86_scanner.hh \
		${srcdir}/decoders/binutils/x86/x86_scanner.ll


## libinsight
##############
lib_LTLIBRARIES = libinsight.la

libinsight_la_SOURCES =  \
	$(kernel_source) 	\
	$(analyses_sources) 	\
	$(decoders_sources) 	\
	$(domains_source) 	\
	$(io_sources) 		\
	$(utils_source)

libinsight_la_CPPFLAGS = @BINUTILS_CFLAGS@
libinsight_la_CXXFLAGS = @BINUTILS_CFLAGS@ -Wno-deprecated
libinsight_la_LDFLAGS  = @BINUTILS_LDFLAGS@

CLEANFILES +=

DISTCLEANFILES = ${BUILT_SOURCES}

MAINTAINERCLEANFILES = \
	compile.log

maintainer-clean-local:
	rm -fr $(top_srcdir)/src/Makefile.in \
	       $(top_srcdir)/src/config.h.in
