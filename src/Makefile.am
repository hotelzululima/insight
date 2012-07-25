## Process this file with automake to produce Makefile.in
AM_CPPFLAGS = @BINUTILS_CFLAGS@
AM_LDFLAGS = @BINUTILS_LDFLAGS@

AUTOMAKE_OPTIONS=subdir-objects

CLEANFILES=
BUILT_SOURCES= 

all:

## analyses module
analyses_sources = \
	analyses/microcode_exec.hh	\
	analyses/microcode_exec.ii	\
	analyses/Wp.cc			\
	analyses/Wp.hh			\
	analyses/slicing/Slicing.hh	\
	analyses/slicing/Slicing.cc

## utils module
utils_source = \
        utils/graph.hh         \
        utils/graph.ii         \
	utils/Log.cc		\
	utils/Log.hh		\
	utils/Object.cc		\
	utils/Object.hh		\
	utils/bv-manip.hh	\
	utils/infrastructure.hh	\
	utils/map-helpers.hh	\
	utils/option.hh		\
	utils/path.hh		\
	utils/path.ii		\
	utils/tools.cc		\
	utils/tools.hh

## kernel module
kernel_source = \
	kernel/Address.cc 		\
	kernel/Address.hh 		\
	kernel/Annotation.cc 		\
	kernel/Annotation.hh 		\
	kernel/Architecture.cc 		\
	kernel/Architecture.hh 	  	\
	kernel/Architecture_ARM.cc    	\
	kernel/Architecture_ARM.hh    	\
	kernel/Architecture_X86_32.cc 	\
	kernel/Architecture_X86_32.hh 	\
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
	kernel/expressions/ConditionalSet.cc 	\
	kernel/expressions/ConditionalSet.hh	\
	kernel/expressions/ExprLexer.hh 	\
	kernel/expressions/ExprLexer.ll		\
	kernel/expressions/ExprParser.yy 	\
	kernel/expressions/Formula.cc     	\
	kernel/expressions/Formula.hh     	\
	kernel/expressions/FormulaAnnotation.cc \
	kernel/expressions/FormulaAnnotation.hh \
	kernel/expressions/FormulaVisitor.hh	\
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
	kernel/microcode/MicrocodeStore.hh	

kernel_built_sources = \
	kernel/expressions/stack.hh 	      	\
	kernel/expressions/location.hh		\
	kernel/expressions/position.hh		\
	kernel/expressions/ExprLexer.cc 	\
	kernel/expressions/ExprParser.hh  	\
	kernel/expressions/ExprParser.cc 

kernel/expressions/stack.hh		\
kernel/expressions/location.hh		\
kernel/expressions/position.hh		\
kernel/expressions/ExprParser.hh 	\
kernel/expressions/ExprParser.cc:	\
kernel/expressions/ExprParser.yy
	$(YACC) --output=kernel/expressions/ExprParser.cc \
		${srcdir}/kernel/expressions/ExprParser.yy

kernel/expressions/ExprLexer.hh \
kernel/expressions/ExprLexer.cc : \
       kernel/expressions/ExprLexer.ll \
       kernel/expressions/ExprParser.hh
	$(LEX) --outfile=kernel/expressions/ExprLexer.cc \
		${srcdir}/kernel/expressions/ExprLexer.ll

BUILT_SOURCES+= \
	${kernel_built_sources}

kernel_cleanfiles = \
	${kernel_built_sources}


## domains module
domains_source = \
	domains/ExprSemantics.hh                   \
	domains/ExprSemantics.ii                   \
	domains/common/ConcreteAddressMemory.hh    \
	domains/common/ConcreteAddressMemory.ii    \
	domains/common/ConcreteProgramPoint.cc     \
	domains/common/ConcreteProgramPoint.hh     \
	domains/concrete/ConcreteAddress.cc        \
	domains/concrete/ConcreteAddress.hh        \
	domains/concrete/ConcreteExprSemantics.cc  \
	domains/concrete/ConcreteExprSemantics.hh  \
	domains/concrete/ConcreteMemory.cc         \
	domains/concrete/ConcreteMemory.hh         \
	domains/concrete/ConcreteValue.cc          \
	domains/concrete/ConcreteValue.hh          \
	domains/concrete/concrete_context.cc       \
	domains/concrete/concrete_context.hh       \
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

## loaders module
loaders_sources = \
	loaders/LoaderFactory.cc 			\
	loaders/LoaderFactory.hh 			\
	loaders/binary/BinaryLoader.cc 			\
	loaders/binary/BinaryLoader.hh 			\
	loaders/binary/BinutilsBinaryLoader.cc 		\
	loaders/binary/BinutilsBinaryLoader.hh 		\
	loaders/microcode/MicrocodeLoader.cc 		\
	loaders/microcode/MicrocodeLoader.hh 		\
	loaders/microcode/xml_microcode_generator.cc	\
	loaders/microcode/xml_microcode_generator.hh 	\
	loaders/microcode/xml_microcode_parser.cc	\
	loaders/microcode/xml_microcode_parser.hh 	\
	loaders/process/ProcessLoader.cc 		\
	loaders/process/ProcessLoader.hh


## decoder module
x86_32_decoder= \
	decoders/binutils/x86-32/x86_32_cc.def \
	decoders/binutils/x86-32/x86_32_interrupts.cc \
	decoders/binutils/x86-32/x86_32_load_store.cc \
	decoders/binutils/x86-32/x86_32_prefixes.cc \
	decoders/binutils/x86-32/x86_32_strings.cc  \
	decoders/binutils/x86-32/x86_32_bits.cc \
	decoders/binutils/x86-32/x86_32_misc_instructions.cc \
        decoders/binutils/x86-32/x86_32_stack_instructions.cc  \
	decoders/binutils/x86-32/x86_32_operators_mov.cc \
	decoders/binutils/x86-32/x86_32_operators_arithmetics.cc \
	decoders/binutils/x86-32/x86_32_operators_boolean.cc     \
	decoders/binutils/x86-32/x86_32_operators_jump.cc        \
	decoders/binutils/x86-32/x86_32_operators_loops.cc       \
	decoders/binutils/x86-32/x86_32_operators_shift.cc       \
        decoders/binutils/x86-32/x86_32_operators_proc_call.cc  \
	decoders/binutils/x86-32/x86_32_decoder.hh \
	decoders/binutils/x86-32/x86_32_decoder.cc \
	decoders/binutils/x86-32/x86_32_decoder.hh \
	decoders/binutils/x86-32/x86_32_translate.cc  \
	decoders/binutils/x86-32/x86_32_translate.hh  \
	decoders/binutils/x86-32/x86_32_translation_functions.hh \
        decoders/binutils/x86-32/x86_32_parser.yy  \
        decoders/binutils/x86-32/x86_32_scanner.ll 

BUILT_SOURCES+= \
	decoders/binutils/x86-32/stack.hh 	      	\
	decoders/binutils/x86-32/location.hh       	\
	decoders/binutils/x86-32/position.hh       	\
	decoders/binutils/x86-32/x86_32_scanner.hh 	\
	decoders/binutils/x86-32/x86_32_scanner.cc 	\
	decoders/binutils/x86-32/x86_32_parser.hh  	\
	decoders/binutils/x86-32/x86_32_parser.cc 

arm_decoder= \
	decoders/binutils/arm/arm_decoder.hh \
	decoders/binutils/arm/arm_decoder.cc \
        decoders/binutils/arm/arm_parser.yy  \
        decoders/binutils/arm/arm_scanner.ll \
	decoders/binutils/arm/arm_translate.hh  \
	decoders/binutils/arm/arm_translate.cc  \
	decoders/binutils/arm/arm_translation_functions.hh \
	decoders/binutils/arm/arm_A_instr.cc	\
	decoders/binutils/arm/arm_B_instr.cc	\
	decoders/binutils/arm/arm_C_instr.cc	\
	decoders/binutils/arm/arm_E_instr.cc	\
	decoders/binutils/arm/arm_L_instr.cc	\
	decoders/binutils/arm/arm_M_instr.cc	\
	decoders/binutils/arm/arm_N_instr.cc \
	decoders/binutils/arm/arm_P_instr.cc \
	decoders/binutils/arm/arm_R_instr.cc \
	decoders/binutils/arm/arm_S_instr.cc \
	decoders/binutils/arm/arm_O_instr.cc	\
	decoders/binutils/arm/arm_U_instr.cc

BUILT_SOURCES+= \
	decoders/binutils/arm/stack.hh 	      	\
	decoders/binutils/arm/location.hh       	\
	decoders/binutils/arm/position.hh       	\
	decoders/binutils/arm/arm_scanner.hh 	\
	decoders/binutils/arm/arm_scanner.cc 	\
	decoders/binutils/arm/arm_parser.hh  	\
	decoders/binutils/arm/arm_parser.cc 

decoders_sources = \
	decoders/Decoder.hh        \
	decoders/Decoder.cc        \
	decoders/DecoderFactory.hh \
	decoders/DecoderFactory.cc \
	decoders/binutils/BinutilsDecoder.hh \
	decoders/binutils/BinutilsDecoder.cc \
        ${x86_32_decoder} \
        ${arm_decoder}


decoders/binutils/x86-32/stack.hh		\
decoders/binutils/x86-32/location.hh 	\
decoders/binutils/x86-32/position.hh 	\
decoders/binutils/x86-32/x86_32_parser.hh 	\
decoders/binutils/x86-32/x86_32_parser.cc:	\
  decoders/binutils/x86-32/x86_32_parser.yy
	$(YACC) --output=decoders/binutils/x86-32/x86_32_parser.cc \
		${srcdir}/decoders/binutils/x86-32/x86_32_parser.yy

decoders/binutils/x86-32/x86_32_scanner.hh 	\
decoders/binutils/x86-32/x86_32_scanner.cc : \
       decoders/binutils/x86-32/x86_32_scanner.ll \
       decoders/binutils/x86-32/x86_32_parser.hh
	$(LEX) --outfile=decoders/binutils/x86-32/x86_32_scanner.cc \
	       --header-file=decoders/binutils/x86-32/x86_32_scanner.hh \
		${srcdir}/decoders/binutils/x86-32/x86_32_scanner.ll

decoders/binutils/arm/stack.hh	\
decoders/binutils/arm/location.hh 	\
decoders/binutils/arm/position.hh 	\
decoders/binutils/arm/arm_parser.hh 	\
decoders/binutils/arm/arm_parser.cc:	\
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


## libinsight
##############
lib_LTLIBRARIES = libinsight.la

libinsight_la_SOURCES =  \
	$(analyses_sources) 	\
	$(decoders_sources) 	\
	$(domains_source) 	\
	$(kernel_source) 	\
	$(loaders_sources) 	\
	$(utils_source)

libinsight_la_CPPFLAGS = @BINUTILS_CFLAGS@
libinsight_la_CXXFLAGS = @BINUTILS_CFLAGS@ -Wno-deprecated
libinsight_la_LDFLAGS  = @BINUTILS_LDFLAGS@

CLEANFILES +=

DISTCLEANFILES = ${BUILT_SOURCES}

MAINTAINERCLEANFILES = \
	compile.log
