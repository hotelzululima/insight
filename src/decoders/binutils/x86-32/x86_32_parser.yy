%code requires {		  /*  -*- C++ -*- */
/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <map>
#include <string>
#include <stack>

#include <kernel/Microcode.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>

/* TODO: Parser state should be defined once for all at a higher
 * level. Not here. Indeed, every architecture parser will have the
 * same kind of internal state anyway, so its definition should be
 * shared by all the parsers. */
namespace x86_32 {
  typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;
  struct parser_data
  {
    typedef enum {
#define X86_32_CC(id,f) X86_32_CC_ ## id,
#include "decoders/binutils/x86-32/x86_32_cc.def"
#undef X86_32_CC
      NB_CC
    } condition_code_t;
    
    parser_data (MicrocodeArchitecture *arch, Microcode *out, 
		 const std::string &inst, address_t start, 
		 address_t next);
    ~parser_data();

    LValue *get_flag (const char *flagname) const;
    LValue *get_tmp_register (const char *id, int size) const;
    LValue *get_register (const char *regname) const;
    bool is_segment_register (const Expr *expr); 

    Expr *get_memory_reference (Expr *section, int disp, Expr *bis) const;

    bool has_prefix;
    std::string instruction;
    MicrocodeAddress start_ma;
    MicrocodeAddress next_ma;
    Microcode *mc;
    bool lock;
    bool data16;
    bool data_size;
    bool addr16;
    bool addr_size;
    const char *data_segment;
    const char *code_segment;
    const char *stack_segment;
    MicrocodeArchitecture *arch;
    Expr *condition_codes[NB_CC];
    std::tr1::unordered_set<const RegisterDesc *, 
			    RegisterDesc::Hash> segment_registers;
  };
}
}

 /* Bison specific options */
%skeleton "lalr1.cc"
%language "c++"
%require "2.4"
%defines
%define namespace "x86_32"

 /* Initial rule is named 'start' */
%start start

 /* Parsing context */
%parse-param { parser_data &data }
/*%lex-param   { parser_data &data }*/

%locations
%initial-action
{
  /* Initialize the initial location */
  @$.begin.filename = @$.end.filename = &data.instruction;
};

%debug
%error-verbose

 /* Symbols */
%union
{
  long         intValue;
  std::string *stringValue;
  class Expr  *expr;
};

%code {
using namespace std;
using namespace x86_32;

#include "decoders/binutils/x86-32/x86_32_translate.hh"

#undef yylex
#define yylex x86_32_lex

#define YY_DECL					\
 x86_32::parser::token_type			\
   yylex(x86_32::parser::semantic_type* yylval,	\
	 x86_32::parser::location_type* yylloc)

 YY_DECL;

#include "x86_32_scanner.hh"

#define push_mc(data) do { (data).mc.push (new Microcode ()); } while (0)

}

%token TOK_LPAR TOK_RPAR
%token TOK_COMMA TOK_COLON
%token TOK_PLUS TOK_MINUS TOK_STAR TOK_DOLLAR
%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token                TOK_EOL        "end of line (EOL)"

%token <stringValue>  TOK_REGISTER   "register (REGISTER)"

%token <intValue>     TOK_INTEGER    "integer value (INTEGER)"

%token  TOK_CS               "CS"
%token  TOK_FS               "FS"
%token  TOK_SS               "SS"
%token  TOK_DS               "DS"
%token  TOK_ES               "ES"
%token  TOK_GS               "GS"
%token  TOK_DATA32           "DATA32"
%token  TOK_DATA16           "DATA16"
%token  TOK_ADDR16           "ADDR16"
%token  TOK_ADDR32           "ADDR32"
%token  TOK_AAA              "AAA"
%token  TOK_AAD              "AAD"
%token  TOK_AAM              "AAM"
%token  TOK_AAS              "AAS"
%token  TOK_ADC              "ADC"
%token  TOK_ADCB             "ADCB"
%token  TOK_ADCW             "ADCW"
%token  TOK_ADCL             "ADCL"
%token  TOK_ADD              "ADD"
%token  TOK_ADDB             "ADDB"
%token  TOK_ADDW             "ADDW"
%token  TOK_ADDL             "ADDL"
%token  TOK_ADDPD            "ADDPD"
%token  TOK_ADDPS            "ADDPS"
%token  TOK_ADDSD            "ADDSD"
%token  TOK_ADDSS            "ADDSS"
%token  TOK_ADDSUBPD         "ADDSUBPD"
%token  TOK_ADDSUBPS         "ADDSUBPS"
%token  TOK_AESDEC           "AESDEC"
%token  TOK_AESDECLAST       "AESDECLAST"
%token  TOK_AESENC           "AESENC"
%token  TOK_AESENCLAST       "AESENCLAST"
%token  TOK_AESIMC           "AESIMC"
%token  TOK_AESKEYGENASSIST  "AESKEYGENASSIST"
%token  TOK_AND              "AND"
%token  TOK_ANDB             "ANDB"
%token  TOK_ANDW             "ANDW"
%token  TOK_ANDL             "ANDL"
%token  TOK_ANDPD            "ANDPD"
%token  TOK_ANDPS            "ANDPS"
%token  TOK_ANDNPD           "ANDNPD"
%token  TOK_ANDNPS           "ANDNPS"
%token  TOK_ARPL             "ARPL"
%token  TOK_BLENDPD          "BLENDPD"
%token  TOK_BLENDPS          "BLENDPS"
%token  TOK_BLENDVPD         "BLENDVPD"
%token  TOK_BLENDVPS         "BLENDVPS"
%token  TOK_BOUND            "BOUND"
%token  TOK_BSF              "BSF"
%token  TOK_BSR              "BSR"
%token  TOK_BSWAP            "BSWAP"
%token  TOK_BT               "BT"
%token  TOK_BTW              "BTW"
%token  TOK_BTL              "BTL"

%token  TOK_BTC              "BTC"
%token  TOK_BTCW             "BTCW"
%token  TOK_BTCL             "BTCL"

%token  TOK_BTR              "BTR"
%token  TOK_BTRW             "BTRW"
%token  TOK_BTRL             "BTRL"

%token  TOK_BTS              "BTS"
%token  TOK_BTSW             "BTSW"
%token  TOK_BTSL             "BTSL"
%token  TOK_CALL             "CALL"
%token  TOK_CBW              "CBW"
%token  TOK_CBTW             "CBTW"
%token  TOK_CWDE             "CWDE"
%token  TOK_CWTL             "CWTL"
%token  TOK_CDQE             "CDQE"
%token  TOK_CLC              "CLC"
%token  TOK_CLD              "CLD"
%token  TOK_CLFLUSH          "CLFLUSH"
%token  TOK_CLI              "CLI"
%token  TOK_CLTS             "CLTS"
%token  TOK_CMC              "CMC"
%token  TOK_CMOVA            "CMOVA"
%token  TOK_CMOVAE           "CMOVAE"
%token  TOK_CMOVB            "CMOVB"
%token  TOK_CMOVBE           "CMOVBE"
%token  TOK_CMOVC            "CMOVC"
%token  TOK_CMOVE            "CMOVE"
%token  TOK_CMOVG            "CMOVG"
%token  TOK_CMOVGE           "CMOVGE"
%token  TOK_CMOVL            "CMOVL"
%token  TOK_CMOVLE           "CMOVLE"
%token  TOK_CMOVNA           "CMOVNA"
%token  TOK_CMOVNAE          "CMOVNAE"
%token  TOK_CMOVNB           "CMOVNB"
%token  TOK_CMOVNBE          "CMOVNBE"
%token  TOK_CMOVNC           "CMOVNC"
%token  TOK_CMOVNE           "CMOVNE"
%token  TOK_CMOVNG           "CMOVNG"
%token  TOK_CMOVNGE          "CMOVNGE"
%token  TOK_CMOVNL           "CMOVNL"
%token  TOK_CMOVNLE          "CMOVNLE"
%token  TOK_CMOVNO           "CMOVNO"
%token  TOK_CMOVNP           "CMOVNP"
%token  TOK_CMOVNS           "CMOVNS"
%token  TOK_CMOVNZ           "CMOVNZ"
%token  TOK_CMOVO            "CMOVO"
%token  TOK_CMOVP            "CMOVP"
%token  TOK_CMOVPE           "CMOVPE"
%token  TOK_CMOVPO           "CMOVPO"
%token  TOK_CMOVS            "CMOVS"
%token  TOK_CMOVZ            "CMOVZ"
%token  TOK_CMP              "CMP"
%token  TOK_CMPB             "CMPB"
%token  TOK_CMPL             "CMPL"
%token  TOK_CMPW             "CMPW"
%token  TOK_CMPPD            "CMPPD"
%token  TOK_CMPPS            "CMPPS"
%token  TOK_CMPSB            "CMPSB"
%token  TOK_CMPSW            "CMPSW"
%token  TOK_CMPSD            "CMPSD"
%token  TOK_CMPSQ            "CMPSQ"
%token  TOK_CMPSS            "CMPSS"
%token  TOK_CMPXCHG          "CMPXCHG"
%token  TOK_CMPXCHG8B        "CMPXCHG8B"
%token  TOK_CMPXCHG16B       "CMPXCHG16B"
%token  TOK_COMISD           "COMISD"
%token  TOK_COMISS           "COMISS"
%token  TOK_CPUID            "CPUID"
%token  TOK_CRC32            "CRC32"
%token  TOK_CVTDQ2PD         "CVTDQ2PD"
%token  TOK_CVTDQ2PS         "CVTDQ2PS"
%token  TOK_CVTPD2DQ         "CVTPD2DQ"
%token  TOK_CVTPD2PI         "CVTPD2PI"
%token  TOK_CVTPD2PS         "CVTPD2PS"
%token  TOK_CVTPI2PD         "CVTPI2PD"
%token  TOK_CVTPI2PS         "CVTPI2PS"
%token  TOK_CVTPS2DQ         "CVTPS2DQ"
%token  TOK_CVTPS2PD         "CVTPS2PD"
%token  TOK_CVTPS2PI         "CVTPS2PI"
%token  TOK_CVTSD2SI         "CVTSD2SI"
%token  TOK_CVTSD2SS         "CVTSD2SS"
%token  TOK_CVTSI2SD         "CVTSI2SD"
%token  TOK_CVTSI2SS         "CVTSI2SS"
%token  TOK_CVTSS2SD         "CVTSS2SD"
%token  TOK_CVTSS2SI         "CVTSS2SI"
%token  TOK_CVTTPD2DQ        "CVTTPD2DQ"
%token  TOK_CVTTPD2PI        "CVTTPD2PI"
%token  TOK_CVTTPS2DQ        "CVTTPS2DQ"
%token  TOK_CVTTPS2PI        "CVTTPS2PI"
%token  TOK_CVTTSD2SI        "CVTTSD2SI"
%token  TOK_CVTTSS2SI        "CVTTSS2SI"
%token  TOK_CWD              "CWD"
%token  TOK_CDQ              "CDQ"
%token  TOK_CQO              "CQO"
%token  TOK_DAA              "DAA"
%token  TOK_DAS              "DAS"
%token  TOK_DEC              "DEC"
%token  TOK_DECB             "DECB"
%token  TOK_DECW             "DECW"
%token  TOK_DECL             "DECL"
%token  TOK_DIV              "DIV"
%token  TOK_DIVB             "DIVB"
%token  TOK_DIVL             "DIVL"
%token  TOK_DIVW             "DIVW"
%token  TOK_DIVPD            "DIVPD"
%token  TOK_DIVPS            "DIVPS"
%token  TOK_DIVSD            "DIVSD"
%token  TOK_DIVSS            "DIVSS"
%token  TOK_DPPD             "DPPD"
%token  TOK_DPPS             "DPPS"
%token  TOK_EMMS             "EMMS"
%token  TOK_ENTER            "ENTER"
%token  TOK_ENTERW           "ENTERW"
%token  TOK_ENTERL           "ENTERL"
%token  TOK_EXTRACTPS        "EXTRACTPS"
%token  TOK_F2XM1            "F2XM1"
%token  TOK_FABS             "FABS"
%token  TOK_FADD             "FADD"
%token  TOK_FADDB            "FADDB"
%token  TOK_FADDW            "FADDW"
%token  TOK_FADDL            "FADDL"
%token  TOK_FADDS            "FADDS"
%token  TOK_FADDP            "FADDP"
%token  TOK_FIADD            "FIADD"
%token  TOK_FBLD             "FBLD"
%token  TOK_FBSTP            "FBSTP"
%token  TOK_FCHS             "FCHS"
%token  TOK_FCLEX            "FCLEX"
%token  TOK_FNCLEX           "FNCLEX"
%token  TOK_FCMOVB           "FCMOVB"
%token  TOK_FCMOVE           "FCMOVE"
%token  TOK_FCMOVBE          "FCMOVBE"
%token  TOK_FCMOVU           "FCMOVU"
%token  TOK_FCMOVNB          "FCMOVNB"
%token  TOK_FCMOVNE          "FCMOVNE"
%token  TOK_FCMOVNBE         "FCMOVNBE"
%token  TOK_FCMOVNU          "FCMOVNU"
%token  TOK_FCOM             "FCOM"
%token  TOK_FCOMP            "FCOMP"
%token  TOK_FCOMPP           "FCOMPP"
%token  TOK_FCOMI            "FCOMI"
%token  TOK_FCOMIP           "FCOMIP"
%token  TOK_FUCOMI           "FUCOMI"
%token  TOK_FUCOMIP          "FUCOMIP"
%token  TOK_FCOS             "FCOS"
%token  TOK_FDECSTP          "FDECSTP"
%token  TOK_FDIV             "FDIV"
%token  TOK_FDIVB            "FDIVB"
%token  TOK_FDIVW            "FDIVW"
%token  TOK_FDIVL            "FDIVL"
%token  TOK_FDIVS            "FDIVS"
%token  TOK_FDIVP            "FDIVP"
%token  TOK_FIDIV            "FIDIV"
%token  TOK_FDIVR            "FDIVR"
%token  TOK_FDIVRL           "FDIVRL"
%token  TOK_FDIVRS           "FDIVRS"
%token  TOK_FDIVRP           "FDIVRP"
%token  TOK_FIDIVR           "FIDIVR"
%token  TOK_FFREE            "FFREE"
%token  TOK_FICOM            "FICOM"
%token  TOK_FICOMP           "FICOMP"
%token  TOK_FILD             "FILD"
%token  TOK_FILDl            "FILDl"
%token  TOK_FILDLL           "FILDLL"
%token  TOK_FINCSTP          "FINCSTP"
%token  TOK_FINIT            "FINIT"
%token  TOK_FNINIT           "FNINIT"
%token  TOK_FIST             "FIST"
%token  TOK_FISTL            "FISTL"
%token  TOK_FISTP            "FISTP"
%token  TOK_FISTPL           "FISTPL"
%token  TOK_FISTPLL          "FISTPLL"
%token  TOK_FISTTP           "FISTTP"
%token  TOK_FLD              "FLD"
%token  TOK_FLDL             "FLDL"
%token  TOK_FLDT             "FLDT"
%token  TOK_FLDS             "FLDS"
%token  TOK_FLD1             "FLD1"
%token  TOK_FLDL2T           "FLDL2T"
%token  TOK_FLDL2E           "FLDL2E"
%token  TOK_FLDPI            "FLDPI"
%token  TOK_FLDLG2           "FLDLG2"
%token  TOK_FLDLN2           "FLDLN2"
%token  TOK_FLDZ             "FLDZ"
%token  TOK_FLDCW            "FLDCW"
%token  TOK_FLDENV           "FLDENV"
%token  TOK_FMUL             "FMUL"
%token  TOK_FMULL            "FMULL"
%token  TOK_FMULS            "FMULS"
%token  TOK_FMULP            "FMULP"
%token  TOK_FIMUL            "FIMUL"
%token  TOK_FNOP             "FNOP"
%token  TOK_FPATAN           "FPATAN"
%token  TOK_FPREM            "FPREM"
%token  TOK_FPREM1           "FPREM1"
%token  TOK_FPTAN            "FPTAN"
%token  TOK_FRNDINT          "FRNDINT"
%token  TOK_FRSTOR           "FRSTOR"
%token  TOK_FSAVE            "FSAVE"
%token  TOK_FNSAVE           "FNSAVE"
%token  TOK_FSCALE           "FSCALE"
%token  TOK_FSIN             "FSIN"
%token  TOK_FSINCOS          "FSINCOS"
%token  TOK_FSQRT            "FSQRT"
%token  TOK_FST              "FST"
%token  TOK_FSTS             "FSTS"
%token  TOK_FSTB             "FSTB"
%token  TOK_FSTW             "FSTW"
%token  TOK_FSTL             "FSTL"
%token  TOK_FSTP             "FSTP"
%token  TOK_FSTPS            "FSTPS"
%token  TOK_FSTPT            "FSTPT"
%token  TOK_FSTPL            "FSTPL"
%token  TOK_FSTCW            "FSTCW"
%token  TOK_FNSTCW           "FNSTCW"
%token  TOK_FSTENV           "FSTENV"
%token  TOK_FNSTENV          "FNSTENV"
%token  TOK_FSTSW            "FSTSW"
%token  TOK_FNSTSW           "FNSTSW"
%token  TOK_FSUB             "FSUB"
%token  TOK_FSUBB            "FSUBB"
%token  TOK_FSUBW            "FSUBW"
%token  TOK_FSUBL            "FSUBL"
%token  TOK_FSUBS            "FSUBS"
%token  TOK_FSUBP            "FSUBP"
%token  TOK_FISUB            "FISUB"
%token  TOK_FSUBR            "FSUBR"
%token  TOK_FSUBRP           "FSUBRP"
%token  TOK_FISUBR           "FISUBR"
%token  TOK_FTST             "FTST"
%token  TOK_FUCOM            "FUCOM"
%token  TOK_FUCOMP           "FUCOMP"
%token  TOK_FUCOMPP          "FUCOMPP"
%token  TOK_FXAM             "FXAM"
%token  TOK_FXCH             "FXCH"
%token  TOK_FXRSTOR          "FXRSTOR"
%token  TOK_FXSAVE           "FXSAVE"
%token  TOK_FXTRACT          "FXTRACT"
%token  TOK_FYL2X            "FYL2X"
%token  TOK_FYL2XP1          "FYL2XP1"
%token  TOK_HADDPD           "HADDPD"
%token  TOK_HADDPS           "HADDPS"
%token  TOK_HLT              "HLT"
%token  TOK_HSUBPD           "HSUBPD"
%token  TOK_HSUBPS           "HSUBPS"
%token  TOK_IDIV             "IDIV"
%token  TOK_IDIVB            "IDIVB"
%token  TOK_IDIVW            "IDIVW"
%token  TOK_IDIVL            "IDIVL"
%token  TOK_IMUL             "IMUL"
%token  TOK_IMULB            "IMULB"
%token  TOK_IMULW            "IMULW"
%token  TOK_IMULL            "IMULL"
%token  TOK_IN               "IN"
%token  TOK_INC              "INC"
%token  TOK_INCB             "INCB"
%token  TOK_INCW             "INCW"
%token  TOK_INCL             "INCL"
%token  TOK_INSB             "INSB"
%token  TOK_INSW             "INSW"
%token  TOK_INSL             "INSL"
%token  TOK_INSD             "INSD"
%token  TOK_INSERTPS         "INSERTPS"
%token  TOK_INT              "INT"
%token  TOK_INTO             "INTO"
%token  TOK_INT3             "INT3"
%token  TOK_INVD             "INVD"
%token  TOK_INVLPG           "INVLPG"
%token  TOK_IRET             "IRET"
%token  TOK_IRETD            "IRETD"
%token  TOK_IRETQ            "IRETQ"
%token  TOK_JA               "JA"
%token  TOK_JAE              "JAE"
%token  TOK_JB               "JB"
%token  TOK_JBE              "JBE"
%token  TOK_JC               "JC"
%token  TOK_JCXZ             "JCXZ"
%token  TOK_JECXZ            "JECXZ"
%token  TOK_JRCXZ            "JRCXZ"
%token  TOK_JE               "JE"
%token  TOK_JG               "JG"
%token  TOK_JGE              "JGE"
%token  TOK_JL               "JL"
%token  TOK_JLE              "JLE"
%token  TOK_JNA              "JNA"
%token  TOK_JNAE             "JNAE"
%token  TOK_JNB              "JNB"
%token  TOK_JNBE             "JNBE"
%token  TOK_JNC              "JNC"
%token  TOK_JNE              "JNE"
%token  TOK_JNG              "JNG"
%token  TOK_JNGE             "JNGE"
%token  TOK_JNL              "JNL"
%token  TOK_JNLE             "JNLE"
%token  TOK_JNO              "JNO"
%token  TOK_JNP              "JNP"
%token  TOK_JNS              "JNS"
%token  TOK_JNZ              "JNZ"
%token  TOK_JO               "JO"
%token  TOK_JP               "JP"
%token  TOK_JPE              "JPE"
%token  TOK_JPO              "JPO"
%token  TOK_JS               "JS"
%token  TOK_JZ               "JZ"
%token  TOK_JMP              "JMP"
%token  TOK_JMPW             "JMPW"
%token  TOK_LAHF             "LAHF"
%token  TOK_LAR              "LAR"
%token  TOK_LDDQU            "LDDQU"
%token  TOK_LDMXCSR          "LDMXCSR"
%token  TOK_LDS              "LDS"
%token  TOK_LES              "LES"
%token  TOK_LFS              "LFS"
%token  TOK_LGS              "LGS"
%token  TOK_LSS              "LSS"
%token  TOK_LEA              "LEA"
%token  TOK_LEAVE            "LEAVE"
%token  TOK_LEAVEW           "LEAVEW"
%token  TOK_LEAVEL           "LEAVEL"
%token  TOK_LFENCE           "LFENCE"
%token  TOK_LGDT             "LGDT"
%token  TOK_LIDT             "LIDT"
%token  TOK_LLDT             "LLDT"
%token  TOK_LMSW             "LMSW"
%token  TOK_LOCK             "LOCK"
%token  TOK_LODS             "LODS"
%token  TOK_LOOP             "LOOP"
%token  TOK_LOOPE            "LOOPE"
%token  TOK_LOOPNE           "LOOPNE"
%token  TOK_LOOPW            "LOOPW"
%token  TOK_LOOPEW           "LOOPEW"
%token  TOK_LOOPNEW          "LOOPNEW"
%token  TOK_LSL              "LSL"
%token  TOK_LTR              "LTR"
%token  TOK_MASKMOVDQU       "MASKMOVDQU"
%token  TOK_MASKMOVQ         "MASKMOVQ"
%token  TOK_MAXPD            "MAXPD"
%token  TOK_MAXPS            "MAXPS"
%token  TOK_MAXSD            "MAXSD"
%token  TOK_MAXSS            "MAXSS"
%token  TOK_MFENCE           "MFENCE"
%token  TOK_MINPD            "MINPD"
%token  TOK_MINPS            "MINPS"
%token  TOK_MINSD            "MINSD"
%token  TOK_MINSS            "MINSS"
%token  TOK_MONITOR          "MONITOR"
%token  TOK_MOV              "MOV"
%token  TOK_MOVB             "MOVB"
%token  TOK_MOVW             "MOVW"
%token  TOK_MOVL             "MOVL"
%token  TOK_MOVAPD           "MOVAPD"
%token  TOK_MOVAPS           "MOVAPS"
%token  TOK_MOVBE            "MOVBE"
%token  TOK_MOVD             "MOVD"
%token  TOK_MOVQ             "MOVQ"
%token  TOK_MOVDDUP          "MOVDDUP"
%token  TOK_MOVDQA           "MOVDQA"
%token  TOK_MOVDQU           "MOVDQU"
%token  TOK_MOVDQ2Q          "MOVDQ2Q"
%token  TOK_MOVHLPS          "MOVHLPS"
%token  TOK_MOVHPD           "MOVHPD"
%token  TOK_MOVHPS           "MOVHPS"
%token  TOK_MOVLHPS          "MOVLHPS"
%token  TOK_MOVLPD           "MOVLPD"
%token  TOK_MOVLPS           "MOVLPS"
%token  TOK_MOVMSKPD         "MOVMSKPD"
%token  TOK_MOVMSKPS         "MOVMSKPS"
%token  TOK_MOVNTDQA         "MOVNTDQA"
%token  TOK_MOVNTDQ          "MOVNTDQ"
%token  TOK_MOVNTI           "MOVNTI"
%token  TOK_MOVNTPD          "MOVNTPD"
%token  TOK_MOVNTPS          "MOVNTPS"
%token  TOK_MOVNTQ           "MOVNTQ"
%token  TOK_MOVQ2DQ          "MOVQ2DQ"
%token  TOK_MOVSB            "MOVSB"
%token  TOK_MOVSW            "MOVSW"
%token  TOK_MOVSL            "MOVSL"

%token  TOK_MOVSBW           "MOVSBW"
%token  TOK_MOVSBL           "MOVSBL"
%token  TOK_MOVSWL           "MOVSWL"

%token  TOK_MOVSHDUP         "MOVSHDUP"
%token  TOK_MOVSLDUP         "MOVSLDUP"
%token  TOK_MOVSS            "MOVSS"

%token  TOK_MOVSXD           "MOVSXD"
%token  TOK_MOVUPD           "MOVUPD"
%token  TOK_MOVUPS           "MOVUPS"

%token  TOK_MOVZBL           "MOVZBL"
%token  TOK_MOVZBW           "MOVZBW"
%token  TOK_MOVZWL           "MOVZWL"

%token  TOK_MPSADBW          "MPSADBW"
%token  TOK_MUL              "MUL"
%token  TOK_MULB             "MULB"
%token  TOK_MULW             "MULW"
%token  TOK_MULL             "MULL"
%token  TOK_MULPD            "MULPD"
%token  TOK_MULPS            "MULPS"
%token  TOK_MULSD            "MULSD"
%token  TOK_MULSS            "MULSS"
%token  TOK_MWAIT            "MWAIT"
%token  TOK_NEG              "NEG"
%token  TOK_NEGB             "NEGB"
%token  TOK_NEGW             "NEGW"
%token  TOK_NEGL             "NEGL"
%token  TOK_NOP              "NOP"
%token  TOK_NOPB             "NOPB"
%token  TOK_NOPW             "NOPW"
%token  TOK_NOPL             "NOPL"
%token  TOK_NOT              "NOT"
%token  TOK_NOTB             "NOTB"
%token  TOK_NOTW             "NOTW"
%token  TOK_NOTL             "NOTL"
%token  TOK_OR               "OR"
%token  TOK_ORB              "ORB"
%token  TOK_ORW              "ORW"
%token  TOK_ORL              "ORL"
%token  TOK_ORPD             "ORPD"
%token  TOK_ORPS             "ORPS"
%token  TOK_OUT              "OUT"
%token  TOK_OUTSB            "OUTSB"
%token  TOK_OUTSW            "OUTSW"
%token  TOK_OUTSL            "OUTSL"
%token  TOK_OUTSD            "OUTSD"
%token  TOK_PABSB            "PABSB"
%token  TOK_PABSW            "PABSW"
%token  TOK_PABSD            "PABSD"
%token  TOK_PACKSSWB         "PACKSSWB"
%token  TOK_PACKSSDW         "PACKSSDW"
%token  TOK_PACKUSDW         "PACKUSDW"
%token  TOK_PACKUSWB         "PACKUSWB"
%token  TOK_PADDB            "PADDB"
%token  TOK_PADDW            "PADDW"
%token  TOK_PADDD            "PADDD"
%token  TOK_PADDQ            "PADDQ"
%token  TOK_PADDSB           "PADDSB"
%token  TOK_PADDSW           "PADDSW"
%token  TOK_PADDUSB          "PADDUSB"
%token  TOK_PADDUSW          "PADDUSW"
%token  TOK_PALIGNR          "PALIGNR"
%token  TOK_PAND             "PAND"
%token  TOK_PANDN            "PANDN"
%token  TOK_PAUSE            "PAUSE"
%token  TOK_PAVGB            "PAVGB"
%token  TOK_PAVGW            "PAVGW"
%token  TOK_PBLENDVB         "PBLENDVB"
%token  TOK_PBLENDW          "PBLENDW"
%token  TOK_PCLMULQDQ        "PCLMULQDQ"
%token  TOK_PCMPEQB          "PCMPEQB"
%token  TOK_PCMPEQW          "PCMPEQW"
%token  TOK_PCMPEQD          "PCMPEQD"
%token  TOK_PCMPEQQ          "PCMPEQQ"
%token  TOK_PCMPESTRI        "PCMPESTRI"
%token  TOK_PCMPESTRM        "PCMPESTRM"
%token  TOK_PCMPGTB          "PCMPGTB"
%token  TOK_PCMPGTW          "PCMPGTW"
%token  TOK_PCMPGTD          "PCMPGTD"
%token  TOK_PCMPGTQ          "PCMPGTQ"
%token  TOK_PCMPISTRI        "PCMPISTRI"
%token  TOK_PCMPISTRM        "PCMPISTRM"
%token  TOK_PEXTRB           "PEXTRB"
%token  TOK_PEXTRD           "PEXTRD"
%token  TOK_PEXTRQ           "PEXTRQ"
%token  TOK_PEXTRW           "PEXTRW"
%token  TOK_PHADDW           "PHADDW"
%token  TOK_PHADDD           "PHADDD"
%token  TOK_PHADDSW          "PHADDSW"
%token  TOK_PHMINPOSUW       "PHMINPOSUW"
%token  TOK_PHSUBW           "PHSUBW"
%token  TOK_PHSUBD           "PHSUBD"
%token  TOK_PHSUBSW          "PHSUBSW"
%token  TOK_PINSRB           "PINSRB"
%token  TOK_PINSRD           "PINSRD"
%token  TOK_PINSRQ           "PINSRQ"
%token  TOK_PINSRW           "PINSRW"
%token  TOK_PMADDUBSW        "PMADDUBSW"
%token  TOK_PMADDWD          "PMADDWD"
%token  TOK_PMAXSB           "PMAXSB"
%token  TOK_PMAXSD           "PMAXSD"
%token  TOK_PMAXSW           "PMAXSW"
%token  TOK_PMAXUB           "PMAXUB"
%token  TOK_PMAXUD           "PMAXUD"
%token  TOK_PMAXUW           "PMAXUW"
%token  TOK_PMINSB           "PMINSB"
%token  TOK_PMINSD           "PMINSD"
%token  TOK_PMINSW           "PMINSW"
%token  TOK_PMINUB           "PMINUB"
%token  TOK_PMINUD           "PMINUD"
%token  TOK_PMINUW           "PMINUW"
%token  TOK_PMOVMSKB         "PMOVMSKB"
%token  TOK_PMOVSX           "PMOVSX"
%token  TOK_PMOVZX           "PMOVZX"
%token  TOK_PMULDQ           "PMULDQ"
%token  TOK_PMULHRSW         "PMULHRSW"
%token  TOK_PMULHUW          "PMULHUW"
%token  TOK_PMULHW           "PMULHW"
%token  TOK_PMULLD           "PMULLD"
%token  TOK_PMULLW           "PMULLW"
%token  TOK_PMULUDQ          "PMULUDQ"
%token  TOK_POP              "POP"
%token  TOK_POPW             "POPW"
%token  TOK_POPL             "POPL"
%token  TOK_POPA             "POPA"
%token  TOK_POPAW            "POPAW"
%token  TOK_POPAL            "POPAL"
%token  TOK_POPAD            "POPAD"
%token  TOK_POPCNT           "POPCNT"
%token  TOK_POPF             "POPF"
%token  TOK_POPFW            "POPFW"
%token  TOK_POPFQ            "POPFQ"
%token  TOK_POR              "POR"
%token  TOK_PREFETCHT0       "PREFETCHT0"
%token  TOK_PREFETCHT1       "PREFETCHT1"
%token  TOK_PREFETCHT2       "PREFETCHT2"
%token  TOK_PREFETCHNTA      "PREFETCHNTA"
%token  TOK_PSADBW           "PSADBW"
%token  TOK_PSHUFB           "PSHUFB"
%token  TOK_PSHUFD           "PSHUFD"
%token  TOK_PSHUFHW          "PSHUFHW"
%token  TOK_PSHUFLW          "PSHUFLW"
%token  TOK_PSHUFW           "PSHUFW"
%token  TOK_PSIGNB           "PSIGNB"
%token  TOK_PSIGNW           "PSIGNW"
%token  TOK_PSIGND           "PSIGND"
%token  TOK_PSLLDQ           "PSLLDQ"
%token  TOK_PSLLW            "PSLLW"
%token  TOK_PSLLD            "PSLLD"
%token  TOK_PSLLQ            "PSLLQ"
%token  TOK_PSRAW            "PSRAW"
%token  TOK_PSRAD            "PSRAD"
%token  TOK_PSRLDQ           "PSRLDQ"
%token  TOK_PSRLW            "PSRLW"
%token  TOK_PSRLD            "PSRLD"
%token  TOK_PSRLQ            "PSRLQ"
%token  TOK_PSUBB            "PSUBB"
%token  TOK_PSUBW            "PSUBW"
%token  TOK_PSUBD            "PSUBD"
%token  TOK_PSUBQ            "PSUBQ"
%token  TOK_PSUBSB           "PSUBSB"
%token  TOK_PSUBSW           "PSUBSW"
%token  TOK_PSUBUSB          "PSUBUSB"
%token  TOK_PSUBUSW          "PSUBUSW"
%token  TOK_PTEST            "PTEST"
%token  TOK_PUNPCKHBW        "PUNPCKHBW"
%token  TOK_PUNPCKHWD        "PUNPCKHWD"
%token  TOK_PUNPCKHDQ        "PUNPCKHDQ"
%token  TOK_PUNPCKHQDQ       "PUNPCKHQDQ"
%token  TOK_PUNPCKLBW        "PUNPCKLBW"
%token  TOK_PUNPCKLWD        "PUNPCKLWD"
%token  TOK_PUNPCKLDQ        "PUNPCKLDQ"
%token  TOK_PUNPCKLQDQ       "PUNPCKLQDQ"
%token  TOK_PUSH             "PUSH"
%token  TOK_PUSHW            "PUSHW"
%token  TOK_PUSHL            "PUSHL"
%token  TOK_PUSHA            "PUSHA"
%token  TOK_PUSHAW           "PUSHAW"
%token  TOK_PUSHAL           "PUSHAL"
%token  TOK_PUSHF            "PUSHF"
%token  TOK_PUSHFW           "PUSHFW"
%token  TOK_PXOR             "PXOR"
%token  TOK_RCL              "RCL"
%token  TOK_RCLB             "RCLB"
%token  TOK_RCLW             "RCLW"
%token  TOK_RCLL             "RCLL"
%token  TOK_RCR              "RCR"
%token  TOK_RCRB             "RCRB"
%token  TOK_RCRW             "RCRW"
%token  TOK_RCRL             "RCRL"
%token  TOK_ROL              "ROL"
%token  TOK_ROLB             "ROLB"
%token  TOK_ROLW             "ROLW"
%token  TOK_ROLL             "ROLL"
%token  TOK_ROR              "ROR"
%token  TOK_RORB             "RORB"
%token  TOK_RORW             "RORW"
%token  TOK_RORL             "RORL"
%token  TOK_RCPPS            "RCPPS"
%token  TOK_RCPSS            "RCPSS"
%token  TOK_RDMSR            "RDMSR"
%token  TOK_RDPMC            "RDPMC"
%token  TOK_RDRAND           "RDRAND"
%token  TOK_RDTSC            "RDTSC"
%token  TOK_RDTSCP           "RDTSCP"
%token  TOK_REP              "REP"
%token  TOK_REPE             "REPE"
%token  TOK_REPZ             "REPZ"
%token  TOK_REPNE            "REPNE"
%token  TOK_REPNZ            "REPNZ"
%token  TOK_RET              "RET"
%token  TOK_ROUNDPD          "ROUNDPD"
%token  TOK_ROUNDPS          "ROUNDPS"
%token  TOK_ROUNDSD          "ROUNDSD"
%token  TOK_ROUNDSS          "ROUNDSS"
%token  TOK_RSM              "RSM"
%token  TOK_RSQRTPS          "RSQRTPS"
%token  TOK_RSQRTSS          "RSQRTSS"
%token  TOK_SAHF             "SAHF"
%token  TOK_SAL              "SAL"
%token  TOK_SALB             "SALB"
%token  TOK_SALW             "SALW"
%token  TOK_SALL             "SALL"
%token  TOK_SAR              "SAR"
%token  TOK_SARB             "SARB"
%token  TOK_SARW             "SARW"
%token  TOK_SARL             "SARL"
%token  TOK_SHL              "SHL"
%token  TOK_SHLB             "SHLB"
%token  TOK_SHLW             "SHLW"
%token  TOK_SHLL             "SHLL"
%token  TOK_SHR              "SHR"
%token  TOK_SHRB             "SHRB"
%token  TOK_SHRW             "SHRW"
%token  TOK_SHRL             "SHRL"
%token  TOK_SBB              "SBB"
%token  TOK_SBBB             "SBBB"
%token  TOK_SBBW             "SBBW"
%token  TOK_SBBL             "SBBL"
%token  TOK_SCAS             "SCAS"
%token  TOK_SCASB            "SCASB"
%token  TOK_SCASW            "SCASW"
%token  TOK_SCASD            "SCASD"
%token  TOK_SETA             "SETA"
%token  TOK_SETAE            "SETAE"
%token  TOK_SETB             "SETB"
%token  TOK_SETBE            "SETBE"
%token  TOK_SETC             "SETC"
%token  TOK_SETE             "SETE"
%token  TOK_SETG             "SETG"
%token  TOK_SETGE            "SETGE"
%token  TOK_SETL             "SETL"
%token  TOK_SETLE            "SETLE"
%token  TOK_SETNA            "SETNA"
%token  TOK_SETNAE           "SETNAE"
%token  TOK_SETNB            "SETNB"
%token  TOK_SETNBE           "SETNBE"
%token  TOK_SETNC            "SETNC"
%token  TOK_SETNE            "SETNE"
%token  TOK_SETNG            "SETNG"
%token  TOK_SETNGE           "SETNGE"
%token  TOK_SETNL            "SETNL"
%token  TOK_SETNLE           "SETNLE"
%token  TOK_SETNO            "SETNO"
%token  TOK_SETNP            "SETNP"
%token  TOK_SETNS            "SETNS"
%token  TOK_SETNZ            "SETNZ"
%token  TOK_SETO             "SETO"
%token  TOK_SETP             "SETP"
%token  TOK_SETPE            "SETPE"
%token  TOK_SETPO            "SETPO"
%token  TOK_SETS             "SETS"
%token  TOK_SETZ             "SETZ"
%token  TOK_SFENCE           "SFENCE"
%token  TOK_SGDT             "SGDT"
%token  TOK_SHLD             "SHLD"
%token  TOK_SHRD             "SHRD"
%token  TOK_SHUFPD           "SHUFPD"
%token  TOK_SHUFPS           "SHUFPS"
%token  TOK_SIDT             "SIDT"
%token  TOK_SLDT             "SLDT"
%token  TOK_SMSW             "SMSW"
%token  TOK_SQRTPD           "SQRTPD"
%token  TOK_SQRTPS           "SQRTPS"
%token  TOK_SQRTSD           "SQRTSD"
%token  TOK_SQRTSS           "SQRTSS"
%token  TOK_STC              "STC"
%token  TOK_STD              "STD"
%token  TOK_STI              "STI"
%token  TOK_STMXCSR          "STMXCSR"
%token  TOK_STOS             "STOS"
%token  TOK_STR              "STR"
%token  TOK_SUB              "SUB"
%token  TOK_SUBB             "SUBB"
%token  TOK_SUBW             "SUBW"
%token  TOK_SUBL             "SUBL"
%token  TOK_SUBPD            "SUBPD"
%token  TOK_SUBPS            "SUBPS"
%token  TOK_SUBSD            "SUBSD"
%token  TOK_SUBSS            "SUBSS"
%token  TOK_SWAPGS           "SWAPGS"
%token  TOK_SYSCALL          "SYSCALL"
%token  TOK_SYSENTER         "SYSENTER"
%token  TOK_SYSEXIT          "SYSEXIT"
%token  TOK_SYSRET           "SYSRET"
%token  TOK_TEST             "TEST"
%token  TOK_TESTB            "TESTB"
%token  TOK_TESTW            "TESTW"
%token  TOK_TESTL            "TESTL"
%token  TOK_UCOMISD          "UCOMISD"
%token  TOK_UCOMISS          "UCOMISS"
%token  TOK_UD2              "UD2"
%token  TOK_UNPCKHPD         "UNPCKHPD"
%token  TOK_UNPCKHPS         "UNPCKHPS"
%token  TOK_UNPCKLPD         "UNPCKLPD"
%token  TOK_UNPCKLPS         "UNPCKLPS"
%token  TOK_VBROADCAST       "VBROADCAST"
%token  TOK_VERR             "VERR"
%token  TOK_VERW             "VERW"
%token  TOK_VEXTRACTF128     "VEXTRACTF128"
%token  TOK_VMASKMOV         "VMASKMOV"
%token  TOK_VINSERTF128      "VINSERTF128"
%token  TOK_VPERMILPD        "VPERMILPD"
%token  TOK_VPERMILPS        "VPERMILPS"
%token  TOK_VPERM2F128       "VPERM2F128"
%token  TOK_VTESTPD          "VTESTPD"
%token  TOK_VTESTPS          "VTESTPS"
%token  TOK_VZEROALL         "VZEROALL"
%token  TOK_VZEROUPPER       "VZEROUPPER"
%token  TOK_WAIT             "WAIT"
%token  TOK_FWAIT            "FWAIT"
%token  TOK_WBINVD           "WBINVD"
%token  TOK_WRMSR            "WRMSR"
%token  TOK_XADD             "XADD"
%token  TOK_XCHG             "XCHG"
%token  TOK_XGETBV           "XGETBV"
%token  TOK_XLAT             "XLAT"
%token  TOK_XLATB            "XLATB"
%token  TOK_XOR              "XOR"
%token  TOK_XORB             "XORB"
%token  TOK_XORW             "XORW"
%token  TOK_XORL             "XORL"
%token  TOK_XORPD            "XORPD"
%token  TOK_XORPS            "XORPS"
%token  TOK_XRSTOR           "XRSTOR"
%token  TOK_XSAVE            "XSAVE"
%token  TOK_XSAVEOPT         "XSAVEOPT"
%token  TOK_XSETBV           "XSETBV"
%token  TOK_EIZ              "EIZ"

%type <expr> operand register section memory_reference base_index_scale

%type <intValue> integer immediate 

%printer    { debug_stream() << $$; } <intValue>

%printer    { debug_stream() << *$$; } TOK_REGISTER
%destructor { delete $$; } TOK_REGISTER

%% /***** Parser rules *****/

start: instruction;

operand:
  immediate { $$ = Constant::create ($1, 0, 32); }
| register { $$ = $1; }
| register TOK_LPAR integer TOK_RPAR  
  { throw std::runtime_error ("unsupported register"); } 
| memory_reference { $$ = $1; }
| TOK_STAR memory_reference { $$ = MemCell::create ($2); }
| TOK_STAR register { $$ = MemCell::create ($2); }
;

memory_reference:
  section integer base_index_scale
{ $$ = data.get_memory_reference ($1, $2, $3); }
| section integer
{ $$ = data.get_memory_reference ($1, $2, NULL); }
| section base_index_scale
{ $$ = data.get_memory_reference ($1, 0, $2); }

section : 
  register TOK_COLON { $$ = $1; }
| /* empty */        { $$ = NULL; }
;

base_index_scale :
  TOK_LPAR register TOK_COMMA register TOK_COMMA TOK_INTEGER TOK_RPAR 
{ $$ = BinaryApp::create (BV_OP_ADD, $2, 
			  BinaryApp::create (BV_OP_MUL_U, $4, $6)); }
| TOK_LPAR register TOK_COMMA register TOK_RPAR 
{ $$ = BinaryApp::create (BV_OP_ADD, $2, $4); }
| TOK_LPAR register TOK_RPAR 
{ $$ = $2; }
| TOK_LPAR TOK_COMMA register TOK_COMMA TOK_INTEGER TOK_RPAR 
{ $$ = BinaryApp::create (BV_OP_MUL_U, $3, $5); }

| TOK_LPAR TOK_COMMA TOK_INTEGER TOK_RPAR  
{ $$ = NULL; }
;

register :
TOK_REGISTER 
{ 
  $$ = data.get_register ($1->c_str ()); 
  if ($$ == NULL)
    {
      error (yylloc, ": error: unknown register " + *$1);
      delete $1;
      YYERROR;
    }
  else
    {
      delete $1;
    }
}
| TOK_EIZ
{
  $$ = Constant::zero(BV_DEFAULT_SIZE);
}
 ;

immediate:
  TOK_DOLLAR integer { $$ = $2; }
;

integer :
  TOK_PLUS  TOK_INTEGER { $$ = $2; }
| TOK_MINUS TOK_INTEGER { $$ = -$2; }
| TOK_INTEGER           { $$ = $1; }
;

instruction: 
  TOK_CS  { x86_32_translate<X86_32_TOKEN(CS)> (data); }
| TOK_CS { x86_32_translate<X86_32_TOKEN(CS)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(CS)> (data, false); }
| TOK_FS  { x86_32_translate<X86_32_TOKEN(FS)> (data); }
| TOK_FS { x86_32_translate<X86_32_TOKEN(FS)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(FS)> (data, false); }
| TOK_SS  { x86_32_translate<X86_32_TOKEN(SS)> (data); }
| TOK_SS { x86_32_translate<X86_32_TOKEN(SS)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(SS)> (data, false); }
| TOK_DS  { x86_32_translate<X86_32_TOKEN(DS)> (data); }
| TOK_DS { x86_32_translate<X86_32_TOKEN(DS)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(DS)> (data, false); }
| TOK_ES  { x86_32_translate<X86_32_TOKEN(ES)> (data); }
| TOK_ES { x86_32_translate<X86_32_TOKEN(ES)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(ES)> (data, false); }
| TOK_GS  { x86_32_translate<X86_32_TOKEN(GS)> (data); }
| TOK_GS { x86_32_translate<X86_32_TOKEN(GS)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(GS)> (data, false); }
| TOK_DATA32  { x86_32_translate<X86_32_TOKEN(DATA32)> (data); }
| TOK_DATA32 { x86_32_translate<X86_32_TOKEN(DATA32)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(DATA32)> (data, false); }
| TOK_DATA16  { x86_32_translate<X86_32_TOKEN(DATA16)> (data); }
| TOK_DATA16 { x86_32_translate<X86_32_TOKEN(DATA16)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(DATA16)> (data, false); }
| TOK_ADDR16  { x86_32_translate<X86_32_TOKEN(ADDR16)> (data); }
| TOK_ADDR16 { x86_32_translate<X86_32_TOKEN(ADDR16)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(ADDR16)> (data, false); }
| TOK_ADDR32  { x86_32_translate<X86_32_TOKEN(ADDR32)> (data); }
| TOK_ADDR32 { x86_32_translate<X86_32_TOKEN(ADDR32)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(ADDR32)> (data, false); }
| TOK_AAA  { x86_32_translate<X86_32_TOKEN(AAA)> (data); }
| TOK_AAD  { x86_32_translate<X86_32_TOKEN(AAD)> (data); }
| TOK_AAD operand { x86_32_translate<X86_32_TOKEN(AAD)> (data, $2); }
| TOK_AAM  { x86_32_translate<X86_32_TOKEN(AAM)> (data); }
| TOK_AAM operand { x86_32_translate<X86_32_TOKEN(AAM)> (data, $2); }
| TOK_AAS  { x86_32_translate<X86_32_TOKEN(AAS)> (data); }
| TOK_ADC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADC)> (data, $2, $4); }
| TOK_ADCB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADCB)> (data, $2, $4); }
| TOK_ADCW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADCW)> (data, $2, $4); }
| TOK_ADCL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADCL)> (data, $2, $4); }
| TOK_ADD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADD)> (data, $2, $4); }
| TOK_ADDB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDB)> (data, $2, $4); }
| TOK_ADDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDW)> (data, $2, $4); }
| TOK_ADDL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDL)> (data, $2, $4); }
| TOK_ADDPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDPD)> (data, $2, $4); }
| TOK_ADDPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDPD)> (data, $2, $4, $6); }
| TOK_ADDPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDPS)> (data, $2, $4); }
| TOK_ADDPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDPS)> (data, $2, $4, $6); }
| TOK_ADDSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSD)> (data, $2, $4); }
| TOK_ADDSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSD)> (data, $2, $4, $6); }
| TOK_ADDSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSS)> (data, $2, $4); }
| TOK_ADDSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSS)> (data, $2, $4, $6); }
| TOK_ADDSUBPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSUBPD)> (data, $2, $4); }
| TOK_ADDSUBPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSUBPD)> (data, $2, $4, $6); }
| TOK_ADDSUBPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSUBPS)> (data, $2, $4); }
| TOK_ADDSUBPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ADDSUBPS)> (data, $2, $4, $6); }
| TOK_AESDEC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESDEC)> (data, $2, $4); }
| TOK_AESDEC operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESDEC)> (data, $2, $4, $6); }
| TOK_AESDECLAST operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESDECLAST)> (data, $2, $4); }
| TOK_AESDECLAST operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESDECLAST)> (data, $2, $4, $6); }
| TOK_AESENC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESENC)> (data, $2, $4); }
| TOK_AESENC operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESENC)> (data, $2, $4, $6); }
| TOK_AESENCLAST operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESENCLAST)> (data, $2, $4); }
| TOK_AESENCLAST operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESENCLAST)> (data, $2, $4, $6); }
| TOK_AESIMC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESIMC)> (data, $2, $4); }
| TOK_AESKEYGENASSIST operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AESKEYGENASSIST)> (data, $2, $4, $6); }
| TOK_AND operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(AND)> (data, $2, $4); }
| TOK_ANDB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDB)> (data, $2, $4); }
| TOK_ANDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDW)> (data, $2, $4); }
| TOK_ANDL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDL)> (data, $2, $4); }
| TOK_ANDPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDPD)> (data, $2, $4); }
| TOK_ANDPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDPD)> (data, $2, $4, $6); }
| TOK_ANDPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDPS)> (data, $2, $4); }
| TOK_ANDPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDPS)> (data, $2, $4, $6); }
| TOK_ANDNPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDNPD)> (data, $2, $4); }
| TOK_ANDNPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDNPD)> (data, $2, $4, $6); }
| TOK_ANDNPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDNPS)> (data, $2, $4); }
| TOK_ANDNPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ANDNPS)> (data, $2, $4, $6); }
| TOK_ARPL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ARPL)> (data, $2, $4); }
| TOK_BLENDPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDPD)> (data, $2, $4, $6); }
| TOK_BLENDPD operand TOK_COMMA operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDPD)> (data, $2, $4, $6, $8); }
| TOK_BLENDPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDPS)> (data, $2, $4, $6); }
| TOK_BLENDPS operand TOK_COMMA operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDPS)> (data, $2, $4, $6, $8); }
| TOK_BLENDVPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDVPD)> (data, $2, $4, $6); }
| TOK_BLENDVPD operand TOK_COMMA operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDVPD)> (data, $2, $4, $6, $8); }
| TOK_BLENDVPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDVPS)> (data, $2, $4, $6); }
| TOK_BLENDVPS operand TOK_COMMA operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BLENDVPS)> (data, $2, $4, $6, $8); }
| TOK_BOUND operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BOUND)> (data, $2, $4); }
| TOK_BSF operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BSF)> (data, $2, $4); }
| TOK_BSR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BSR)> (data, $2, $4); }
| TOK_BSWAP operand { x86_32_translate<X86_32_TOKEN(BSWAP)> (data, $2); }
| TOK_BT operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BT)> (data, $2, $4); }
| TOK_BTW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTW)> (data, $2, $4); }
| TOK_BTL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTL)> (data, $2, $4); }
| TOK_BTC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTC)> (data, $2, $4); }
| TOK_BTCW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTCW)> (data, $2, $4); }
| TOK_BTCL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTCL)> (data, $2, $4); }
| TOK_BTR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTR)> (data, $2, $4); }
| TOK_BTRW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTRW)> (data, $2, $4); }
| TOK_BTRL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTRL)> (data, $2, $4); }
| TOK_BTS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTS)> (data, $2, $4); }
| TOK_BTSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTSW)> (data, $2, $4); }
| TOK_BTSL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(BTSL)> (data, $2, $4); }
| TOK_CALL operand { x86_32_translate<X86_32_TOKEN(CALL)> (data, $2); }
| TOK_CBW  { x86_32_translate<X86_32_TOKEN(CBW)> (data); }
| TOK_CBTW  { x86_32_translate<X86_32_TOKEN(CBTW)> (data); }
| TOK_CWDE  { x86_32_translate<X86_32_TOKEN(CWDE)> (data); }
| TOK_CWTL  { x86_32_translate<X86_32_TOKEN(CWTL)> (data); }
| TOK_CDQE  { x86_32_translate<X86_32_TOKEN(CDQE)> (data); }
| TOK_CLC  { x86_32_translate<X86_32_TOKEN(CLC)> (data); }
| TOK_CLD  { x86_32_translate<X86_32_TOKEN(CLD)> (data); }
| TOK_CLFLUSH operand { x86_32_translate<X86_32_TOKEN(CLFLUSH)> (data, $2); }
| TOK_CLI  { x86_32_translate<X86_32_TOKEN(CLI)> (data); }
| TOK_CLTS  { x86_32_translate<X86_32_TOKEN(CLTS)> (data); }
| TOK_CMC  { x86_32_translate<X86_32_TOKEN(CMC)> (data); }
| TOK_CMOVA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVA)> (data, $2, $4); }
| TOK_CMOVAE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVAE)> (data, $2, $4); }
| TOK_CMOVB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVB)> (data, $2, $4); }
| TOK_CMOVBE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVBE)> (data, $2, $4); }
| TOK_CMOVC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVC)> (data, $2, $4); }
| TOK_CMOVE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVE)> (data, $2, $4); }
| TOK_CMOVG operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVG)> (data, $2, $4); }
| TOK_CMOVGE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVGE)> (data, $2, $4); }
| TOK_CMOVL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVL)> (data, $2, $4); }
| TOK_CMOVLE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVLE)> (data, $2, $4); }
| TOK_CMOVNA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNA)> (data, $2, $4); }
| TOK_CMOVNAE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNAE)> (data, $2, $4); }
| TOK_CMOVNB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNB)> (data, $2, $4); }
| TOK_CMOVNBE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNBE)> (data, $2, $4); }
| TOK_CMOVNC operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNC)> (data, $2, $4); }
| TOK_CMOVNE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNE)> (data, $2, $4); }
| TOK_CMOVNG operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNG)> (data, $2, $4); }
| TOK_CMOVNGE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNGE)> (data, $2, $4); }
| TOK_CMOVNL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNL)> (data, $2, $4); }
| TOK_CMOVNLE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNLE)> (data, $2, $4); }
| TOK_CMOVNO operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNO)> (data, $2, $4); }
| TOK_CMOVNP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNP)> (data, $2, $4); }
| TOK_CMOVNS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNS)> (data, $2, $4); }
| TOK_CMOVNZ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVNZ)> (data, $2, $4); }
| TOK_CMOVO operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVO)> (data, $2, $4); }
| TOK_CMOVP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVP)> (data, $2, $4); }
| TOK_CMOVPE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVPE)> (data, $2, $4); }
| TOK_CMOVPO operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVPO)> (data, $2, $4); }
| TOK_CMOVS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVS)> (data, $2, $4); }
| TOK_CMOVZ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMOVZ)> (data, $2, $4); }
| TOK_CMP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMP)> (data, $2, $4); }
| TOK_CMPB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPB)> (data, $2, $4); }
| TOK_CMPL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPL)> (data, $2, $4); }
| TOK_CMPW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPW)> (data, $2, $4); }
| TOK_CMPPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPPD)> (data, $2, $4, $6); }
| TOK_CMPPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPPS)> (data, $2, $4, $6); }
| TOK_CMPSB  { x86_32_translate<X86_32_TOKEN(CMPSB)> (data); }
| TOK_CMPSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSB)> (data, $2, $4); }
| TOK_CMPSW  { x86_32_translate<X86_32_TOKEN(CMPSW)> (data); }
| TOK_CMPSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSW)> (data, $2, $4); }
| TOK_CMPSD  { x86_32_translate<X86_32_TOKEN(CMPSD)> (data); }
| TOK_CMPSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSD)> (data, $2, $4); }
| TOK_CMPSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSD)> (data, $2, $4, $6); }
| TOK_CMPSQ  { x86_32_translate<X86_32_TOKEN(CMPSQ)> (data); }
| TOK_CMPSQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSQ)> (data, $2, $4); }
| TOK_CMPSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPSS)> (data, $2, $4, $6); }
| TOK_CMPXCHG operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CMPXCHG)> (data, $2, $4); }
| TOK_CMPXCHG8B operand { x86_32_translate<X86_32_TOKEN(CMPXCHG8B)> (data, $2); }
| TOK_CMPXCHG16B operand { x86_32_translate<X86_32_TOKEN(CMPXCHG16B)> (data, $2); }
| TOK_COMISD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(COMISD)> (data, $2, $4); }
| TOK_COMISS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(COMISS)> (data, $2, $4); }
| TOK_CPUID  { x86_32_translate<X86_32_TOKEN(CPUID)> (data); }
| TOK_CRC32 operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CRC32)> (data, $2, $4); }
| TOK_CVTDQ2PD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTDQ2PD)> (data, $2, $4); }
| TOK_CVTDQ2PS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTDQ2PS)> (data, $2, $4); }
| TOK_CVTPD2DQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPD2DQ)> (data, $2, $4); }
| TOK_CVTPD2PI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPD2PI)> (data, $2, $4); }
| TOK_CVTPD2PS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPD2PS)> (data, $2, $4); }
| TOK_CVTPI2PD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPI2PD)> (data, $2, $4); }
| TOK_CVTPI2PS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPI2PS)> (data, $2, $4); }
| TOK_CVTPS2DQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPS2DQ)> (data, $2, $4); }
| TOK_CVTPS2PD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPS2PD)> (data, $2, $4); }
| TOK_CVTPS2PI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTPS2PI)> (data, $2, $4); }
| TOK_CVTSD2SI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSD2SI)> (data, $2, $4); }
| TOK_CVTSD2SS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSD2SS)> (data, $2, $4); }
| TOK_CVTSD2SS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSD2SS)> (data, $2, $4, $6); }
| TOK_CVTSI2SD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSI2SD)> (data, $2, $4); }
| TOK_CVTSI2SD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSI2SD)> (data, $2, $4, $6); }
| TOK_CVTSI2SS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSI2SS)> (data, $2, $4); }
| TOK_CVTSI2SS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSI2SS)> (data, $2, $4, $6); }
| TOK_CVTSS2SD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSS2SD)> (data, $2, $4); }
| TOK_CVTSS2SD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSS2SD)> (data, $2, $4, $6); }
| TOK_CVTSS2SI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTSS2SI)> (data, $2, $4); }
| TOK_CVTTPD2DQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTPD2DQ)> (data, $2, $4); }
| TOK_CVTTPD2PI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTPD2PI)> (data, $2, $4); }
| TOK_CVTTPS2DQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTPS2DQ)> (data, $2, $4); }
| TOK_CVTTPS2PI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTPS2PI)> (data, $2, $4); }
| TOK_CVTTSD2SI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTSD2SI)> (data, $2, $4); }
| TOK_CVTTSS2SI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(CVTTSS2SI)> (data, $2, $4); }
| TOK_CWD  { x86_32_translate<X86_32_TOKEN(CWD)> (data); }
| TOK_CDQ  { x86_32_translate<X86_32_TOKEN(CDQ)> (data); }
| TOK_CQO  { x86_32_translate<X86_32_TOKEN(CQO)> (data); }
| TOK_DAA  { x86_32_translate<X86_32_TOKEN(DAA)> (data); }
| TOK_DAS  { x86_32_translate<X86_32_TOKEN(DAS)> (data); }
| TOK_DEC operand { x86_32_translate<X86_32_TOKEN(DEC)> (data, $2); }
| TOK_DECB operand { x86_32_translate<X86_32_TOKEN(DECB)> (data, $2); }
| TOK_DECW operand { x86_32_translate<X86_32_TOKEN(DECW)> (data, $2); }
| TOK_DECL operand { x86_32_translate<X86_32_TOKEN(DECL)> (data, $2); }
| TOK_DIV operand { x86_32_translate<X86_32_TOKEN(DIV)> (data, $2); }
| TOK_DIV operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIV)> (data, $2, $4); }
| TOK_DIVB operand { x86_32_translate<X86_32_TOKEN(DIVB)> (data, $2); }
| TOK_DIVB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVB)> (data, $2, $4); }
| TOK_DIVL operand { x86_32_translate<X86_32_TOKEN(DIVL)> (data, $2); }
| TOK_DIVL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVL)> (data, $2, $4); }
| TOK_DIVW operand { x86_32_translate<X86_32_TOKEN(DIVW)> (data, $2); }
| TOK_DIVW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVW)> (data, $2, $4); }
| TOK_DIVPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVPD)> (data, $2, $4); }
| TOK_DIVPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVPD)> (data, $2, $4, $6); }
| TOK_DIVPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVPS)> (data, $2, $4); }
| TOK_DIVPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVPS)> (data, $2, $4, $6); }
| TOK_DIVSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVSD)> (data, $2, $4); }
| TOK_DIVSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVSD)> (data, $2, $4, $6); }
| TOK_DIVSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVSS)> (data, $2, $4); }
| TOK_DIVSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DIVSS)> (data, $2, $4, $6); }
| TOK_DPPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DPPD)> (data, $2, $4, $6); }
| TOK_DPPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(DPPS)> (data, $2, $4, $6); }
| TOK_EMMS operand { x86_32_translate<X86_32_TOKEN(EMMS)> (data, $2); }
| TOK_ENTER operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ENTER)> (data, $2, $4); }
| TOK_ENTERW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ENTERW)> (data, $2, $4); }
| TOK_ENTERL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ENTERL)> (data, $2, $4); }
| TOK_EXTRACTPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(EXTRACTPS)> (data, $2, $4); }
| TOK_F2XM1  { x86_32_translate<X86_32_TOKEN(F2XM1)> (data); }
| TOK_FABS  { x86_32_translate<X86_32_TOKEN(FABS)> (data); }
| TOK_FADD operand { x86_32_translate<X86_32_TOKEN(FADD)> (data, $2); }
| TOK_FADD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADD)> (data, $2, $4); }
| TOK_FADDB operand { x86_32_translate<X86_32_TOKEN(FADDB)> (data, $2); }
| TOK_FADDB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADDB)> (data, $2, $4); }
| TOK_FADDW operand { x86_32_translate<X86_32_TOKEN(FADDW)> (data, $2); }
| TOK_FADDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADDW)> (data, $2, $4); }
| TOK_FADDL operand { x86_32_translate<X86_32_TOKEN(FADDL)> (data, $2); }
| TOK_FADDL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADDL)> (data, $2, $4); }
| TOK_FADDS operand { x86_32_translate<X86_32_TOKEN(FADDS)> (data, $2); }
| TOK_FADDS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADDS)> (data, $2, $4); }
| TOK_FADDP  { x86_32_translate<X86_32_TOKEN(FADDP)> (data); }
| TOK_FADDP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FADDP)> (data, $2, $4); }
| TOK_FIADD operand { x86_32_translate<X86_32_TOKEN(FIADD)> (data, $2); }
| TOK_FBLD operand { x86_32_translate<X86_32_TOKEN(FBLD)> (data, $2); }
| TOK_FBSTP operand { x86_32_translate<X86_32_TOKEN(FBSTP)> (data, $2); }
| TOK_FCHS  { x86_32_translate<X86_32_TOKEN(FCHS)> (data); }
| TOK_FCLEX  { x86_32_translate<X86_32_TOKEN(FCLEX)> (data); }
| TOK_FNCLEX  { x86_32_translate<X86_32_TOKEN(FNCLEX)> (data); }
| TOK_FCMOVB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVB)> (data, $2, $4); }
| TOK_FCMOVE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVE)> (data, $2, $4); }
| TOK_FCMOVBE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVBE)> (data, $2, $4); }
| TOK_FCMOVU operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVU)> (data, $2, $4); }
| TOK_FCMOVNB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVNB)> (data, $2, $4); }
| TOK_FCMOVNE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVNE)> (data, $2, $4); }
| TOK_FCMOVNBE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVNBE)> (data, $2, $4); }
| TOK_FCMOVNU operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FCMOVNU)> (data, $2, $4); }
| TOK_FCOM  { x86_32_translate<X86_32_TOKEN(FCOM)> (data); }
| TOK_FCOM operand { x86_32_translate<X86_32_TOKEN(FCOM)> (data, $2); }
| TOK_FCOMP  { x86_32_translate<X86_32_TOKEN(FCOMP)> (data); }
| TOK_FCOMP operand { x86_32_translate<X86_32_TOKEN(FCOMP)> (data, $2); }
| TOK_FCOMPP  { x86_32_translate<X86_32_TOKEN(FCOMPP)> (data); }
| TOK_FCOMI operand { x86_32_translate<X86_32_TOKEN(FCOMI)> (data, $2); }
| TOK_FCOMIP operand { x86_32_translate<X86_32_TOKEN(FCOMIP)> (data, $2); }
| TOK_FUCOMI operand { x86_32_translate<X86_32_TOKEN(FUCOMI)> (data, $2); }
| TOK_FUCOMI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FUCOMI)> (data, $2, $4); }
| TOK_FUCOMIP operand { x86_32_translate<X86_32_TOKEN(FUCOMIP)> (data, $2); }
| TOK_FUCOMIP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FUCOMIP)> (data, $2, $4); }
| TOK_FCOS  { x86_32_translate<X86_32_TOKEN(FCOS)> (data); }
| TOK_FDECSTP  { x86_32_translate<X86_32_TOKEN(FDECSTP)> (data); }
| TOK_FDIV operand { x86_32_translate<X86_32_TOKEN(FDIV)> (data, $2); }
| TOK_FDIV operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIV)> (data, $2, $4); }
| TOK_FDIVB operand { x86_32_translate<X86_32_TOKEN(FDIVB)> (data, $2); }
| TOK_FDIVB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVB)> (data, $2, $4); }
| TOK_FDIVW operand { x86_32_translate<X86_32_TOKEN(FDIVW)> (data, $2); }
| TOK_FDIVW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVW)> (data, $2, $4); }
| TOK_FDIVL operand { x86_32_translate<X86_32_TOKEN(FDIVL)> (data, $2); }
| TOK_FDIVL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVL)> (data, $2, $4); }
| TOK_FDIVS operand { x86_32_translate<X86_32_TOKEN(FDIVS)> (data, $2); }
| TOK_FDIVS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVS)> (data, $2, $4); }
| TOK_FDIVP  { x86_32_translate<X86_32_TOKEN(FDIVP)> (data); }
| TOK_FDIVP operand { x86_32_translate<X86_32_TOKEN(FDIVP)> (data, $2); }
| TOK_FDIVP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVP)> (data, $2, $4); }
| TOK_FIDIV operand { x86_32_translate<X86_32_TOKEN(FIDIV)> (data, $2); }
| TOK_FDIVR operand { x86_32_translate<X86_32_TOKEN(FDIVR)> (data, $2); }
| TOK_FDIVR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVR)> (data, $2, $4); }
| TOK_FDIVRL operand { x86_32_translate<X86_32_TOKEN(FDIVRL)> (data, $2); }
| TOK_FDIVRL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVRL)> (data, $2, $4); }
| TOK_FDIVRS operand { x86_32_translate<X86_32_TOKEN(FDIVRS)> (data, $2); }
| TOK_FDIVRS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVRS)> (data, $2, $4); }
| TOK_FDIVRP  { x86_32_translate<X86_32_TOKEN(FDIVRP)> (data); }
| TOK_FDIVRP operand { x86_32_translate<X86_32_TOKEN(FDIVRP)> (data, $2); }
| TOK_FDIVRP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FDIVRP)> (data, $2, $4); }
| TOK_FIDIVR operand { x86_32_translate<X86_32_TOKEN(FIDIVR)> (data, $2); }
| TOK_FFREE operand { x86_32_translate<X86_32_TOKEN(FFREE)> (data, $2); }
| TOK_FICOM operand { x86_32_translate<X86_32_TOKEN(FICOM)> (data, $2); }
| TOK_FICOMP operand { x86_32_translate<X86_32_TOKEN(FICOMP)> (data, $2); }
| TOK_FILD operand { x86_32_translate<X86_32_TOKEN(FILD)> (data, $2); }
| TOK_FILDl operand { x86_32_translate<X86_32_TOKEN(FILDl)> (data, $2); }
| TOK_FILDLL operand { x86_32_translate<X86_32_TOKEN(FILDLL)> (data, $2); }
| TOK_FINCSTP  { x86_32_translate<X86_32_TOKEN(FINCSTP)> (data); }
| TOK_FINIT  { x86_32_translate<X86_32_TOKEN(FINIT)> (data); }
| TOK_FNINIT  { x86_32_translate<X86_32_TOKEN(FNINIT)> (data); }
| TOK_FIST operand { x86_32_translate<X86_32_TOKEN(FIST)> (data, $2); }
| TOK_FISTL operand { x86_32_translate<X86_32_TOKEN(FISTL)> (data, $2); }
| TOK_FISTP operand { x86_32_translate<X86_32_TOKEN(FISTP)> (data, $2); }
| TOK_FISTPL operand { x86_32_translate<X86_32_TOKEN(FISTPL)> (data, $2); }
| TOK_FISTPLL operand { x86_32_translate<X86_32_TOKEN(FISTPLL)> (data, $2); }
| TOK_FISTTP operand { x86_32_translate<X86_32_TOKEN(FISTTP)> (data, $2); }
| TOK_FLD operand { x86_32_translate<X86_32_TOKEN(FLD)> (data, $2); }
| TOK_FLDL operand { x86_32_translate<X86_32_TOKEN(FLDL)> (data, $2); }
| TOK_FLDT operand { x86_32_translate<X86_32_TOKEN(FLDT)> (data, $2); }
| TOK_FLDS operand { x86_32_translate<X86_32_TOKEN(FLDS)> (data, $2); }
| TOK_FLD1  { x86_32_translate<X86_32_TOKEN(FLD1)> (data); }
| TOK_FLDL2T  { x86_32_translate<X86_32_TOKEN(FLDL2T)> (data); }
| TOK_FLDL2E  { x86_32_translate<X86_32_TOKEN(FLDL2E)> (data); }
| TOK_FLDPI  { x86_32_translate<X86_32_TOKEN(FLDPI)> (data); }
| TOK_FLDLG2  { x86_32_translate<X86_32_TOKEN(FLDLG2)> (data); }
| TOK_FLDLN2  { x86_32_translate<X86_32_TOKEN(FLDLN2)> (data); }
| TOK_FLDZ  { x86_32_translate<X86_32_TOKEN(FLDZ)> (data); }
| TOK_FLDCW operand { x86_32_translate<X86_32_TOKEN(FLDCW)> (data, $2); }
| TOK_FLDENV operand { x86_32_translate<X86_32_TOKEN(FLDENV)> (data, $2); }
| TOK_FMUL operand { x86_32_translate<X86_32_TOKEN(FMUL)> (data, $2); }
| TOK_FMUL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FMUL)> (data, $2, $4); }
| TOK_FMULL operand { x86_32_translate<X86_32_TOKEN(FMULL)> (data, $2); }
| TOK_FMULL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FMULL)> (data, $2, $4); }
| TOK_FMULS operand { x86_32_translate<X86_32_TOKEN(FMULS)> (data, $2); }
| TOK_FMULS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FMULS)> (data, $2, $4); }
| TOK_FMULP  { x86_32_translate<X86_32_TOKEN(FMULP)> (data); }
| TOK_FMULP operand { x86_32_translate<X86_32_TOKEN(FMULP)> (data, $2); }
| TOK_FMULP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FMULP)> (data, $2, $4); }
| TOK_FIMUL operand { x86_32_translate<X86_32_TOKEN(FIMUL)> (data, $2); }
| TOK_FNOP  { x86_32_translate<X86_32_TOKEN(FNOP)> (data); }
| TOK_FPATAN  { x86_32_translate<X86_32_TOKEN(FPATAN)> (data); }
| TOK_FPREM  { x86_32_translate<X86_32_TOKEN(FPREM)> (data); }
| TOK_FPREM1  { x86_32_translate<X86_32_TOKEN(FPREM1)> (data); }
| TOK_FPTAN  { x86_32_translate<X86_32_TOKEN(FPTAN)> (data); }
| TOK_FRNDINT  { x86_32_translate<X86_32_TOKEN(FRNDINT)> (data); }
| TOK_FRSTOR operand { x86_32_translate<X86_32_TOKEN(FRSTOR)> (data, $2); }
| TOK_FSAVE operand { x86_32_translate<X86_32_TOKEN(FSAVE)> (data, $2); }
| TOK_FNSAVE operand { x86_32_translate<X86_32_TOKEN(FNSAVE)> (data, $2); }
| TOK_FSCALE  { x86_32_translate<X86_32_TOKEN(FSCALE)> (data); }
| TOK_FSIN  { x86_32_translate<X86_32_TOKEN(FSIN)> (data); }
| TOK_FSINCOS  { x86_32_translate<X86_32_TOKEN(FSINCOS)> (data); }
| TOK_FSQRT  { x86_32_translate<X86_32_TOKEN(FSQRT)> (data); }
| TOK_FST operand { x86_32_translate<X86_32_TOKEN(FST)> (data, $2); }
| TOK_FSTS operand { x86_32_translate<X86_32_TOKEN(FSTS)> (data, $2); }
| TOK_FSTB operand { x86_32_translate<X86_32_TOKEN(FSTB)> (data, $2); }
| TOK_FSTW operand { x86_32_translate<X86_32_TOKEN(FSTW)> (data, $2); }
| TOK_FSTL operand { x86_32_translate<X86_32_TOKEN(FSTL)> (data, $2); }
| TOK_FSTP operand { x86_32_translate<X86_32_TOKEN(FSTP)> (data, $2); }
| TOK_FSTPS operand { x86_32_translate<X86_32_TOKEN(FSTPS)> (data, $2); }
| TOK_FSTPT operand { x86_32_translate<X86_32_TOKEN(FSTPT)> (data, $2); }
| TOK_FSTPL operand { x86_32_translate<X86_32_TOKEN(FSTPL)> (data, $2); }
| TOK_FSTCW operand { x86_32_translate<X86_32_TOKEN(FSTCW)> (data, $2); }
| TOK_FNSTCW operand { x86_32_translate<X86_32_TOKEN(FNSTCW)> (data, $2); }
| TOK_FSTENV operand { x86_32_translate<X86_32_TOKEN(FSTENV)> (data, $2); }
| TOK_FNSTENV operand { x86_32_translate<X86_32_TOKEN(FNSTENV)> (data, $2); }
| TOK_FSTSW operand { x86_32_translate<X86_32_TOKEN(FSTSW)> (data, $2); }
| TOK_FNSTSW operand { x86_32_translate<X86_32_TOKEN(FNSTSW)> (data, $2); }
| TOK_FSUB operand { x86_32_translate<X86_32_TOKEN(FSUB)> (data, $2); }
| TOK_FSUB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUB)> (data, $2, $4); }
| TOK_FSUBB operand { x86_32_translate<X86_32_TOKEN(FSUBB)> (data, $2); }
| TOK_FSUBB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBB)> (data, $2, $4); }
| TOK_FSUBW operand { x86_32_translate<X86_32_TOKEN(FSUBW)> (data, $2); }
| TOK_FSUBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBW)> (data, $2, $4); }
| TOK_FSUBL operand { x86_32_translate<X86_32_TOKEN(FSUBL)> (data, $2); }
| TOK_FSUBL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBL)> (data, $2, $4); }
| TOK_FSUBS operand { x86_32_translate<X86_32_TOKEN(FSUBS)> (data, $2); }
| TOK_FSUBS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBS)> (data, $2, $4); }
| TOK_FSUBP  { x86_32_translate<X86_32_TOKEN(FSUBP)> (data); }
| TOK_FSUBP operand { x86_32_translate<X86_32_TOKEN(FSUBP)> (data, $2); }
| TOK_FSUBP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBP)> (data, $2, $4); }
| TOK_FISUB operand { x86_32_translate<X86_32_TOKEN(FISUB)> (data, $2); }
| TOK_FSUBR operand { x86_32_translate<X86_32_TOKEN(FSUBR)> (data, $2); }
| TOK_FSUBR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBR)> (data, $2, $4); }
| TOK_FSUBRP  { x86_32_translate<X86_32_TOKEN(FSUBRP)> (data); }
| TOK_FSUBRP operand { x86_32_translate<X86_32_TOKEN(FSUBRP)> (data, $2); }
| TOK_FSUBRP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(FSUBRP)> (data, $2, $4); }
| TOK_FISUBR operand { x86_32_translate<X86_32_TOKEN(FISUBR)> (data, $2); }
| TOK_FTST operand { x86_32_translate<X86_32_TOKEN(FTST)> (data, $2); }
| TOK_FUCOM  { x86_32_translate<X86_32_TOKEN(FUCOM)> (data); }
| TOK_FUCOM operand { x86_32_translate<X86_32_TOKEN(FUCOM)> (data, $2); }
| TOK_FUCOMP  { x86_32_translate<X86_32_TOKEN(FUCOMP)> (data); }
| TOK_FUCOMP operand { x86_32_translate<X86_32_TOKEN(FUCOMP)> (data, $2); }
| TOK_FUCOMPP operand { x86_32_translate<X86_32_TOKEN(FUCOMPP)> (data, $2); }
| TOK_FXAM  { x86_32_translate<X86_32_TOKEN(FXAM)> (data); }
| TOK_FXCH  { x86_32_translate<X86_32_TOKEN(FXCH)> (data); }
| TOK_FXCH operand { x86_32_translate<X86_32_TOKEN(FXCH)> (data, $2); }
| TOK_FXRSTOR operand { x86_32_translate<X86_32_TOKEN(FXRSTOR)> (data, $2); }
| TOK_FXSAVE operand { x86_32_translate<X86_32_TOKEN(FXSAVE)> (data, $2); }
| TOK_FXTRACT  { x86_32_translate<X86_32_TOKEN(FXTRACT)> (data); }
| TOK_FYL2X  { x86_32_translate<X86_32_TOKEN(FYL2X)> (data); }
| TOK_FYL2XP1 operand { x86_32_translate<X86_32_TOKEN(FYL2XP1)> (data, $2); }
| TOK_HADDPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HADDPD)> (data, $2, $4); }
| TOK_HADDPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HADDPD)> (data, $2, $4, $6); }
| TOK_HADDPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HADDPS)> (data, $2, $4); }
| TOK_HADDPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HADDPS)> (data, $2, $4, $6); }
| TOK_HLT  { x86_32_translate<X86_32_TOKEN(HLT)> (data); }
| TOK_HSUBPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HSUBPD)> (data, $2, $4); }
| TOK_HSUBPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HSUBPD)> (data, $2, $4, $6); }
| TOK_HSUBPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HSUBPS)> (data, $2, $4); }
| TOK_HSUBPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(HSUBPS)> (data, $2, $4, $6); }
| TOK_IDIV operand { x86_32_translate<X86_32_TOKEN(IDIV)> (data, $2); }
| TOK_IDIVB operand { x86_32_translate<X86_32_TOKEN(IDIVB)> (data, $2); }
| TOK_IDIVW operand { x86_32_translate<X86_32_TOKEN(IDIVW)> (data, $2); }
| TOK_IDIVL operand { x86_32_translate<X86_32_TOKEN(IDIVL)> (data, $2); }
| TOK_IMUL operand { x86_32_translate<X86_32_TOKEN(IMUL)> (data, $2); }
| TOK_IMUL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMUL)> (data, $2, $4); }
| TOK_IMUL operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMUL)> (data, $2, $4, $6); }
| TOK_IMULB operand { x86_32_translate<X86_32_TOKEN(IMULB)> (data, $2); }
| TOK_IMULB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULB)> (data, $2, $4); }
| TOK_IMULB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULB)> (data, $2, $4, $6); }
| TOK_IMULW operand { x86_32_translate<X86_32_TOKEN(IMULW)> (data, $2); }
| TOK_IMULW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULW)> (data, $2, $4); }
| TOK_IMULW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULW)> (data, $2, $4, $6); }
| TOK_IMULL operand { x86_32_translate<X86_32_TOKEN(IMULL)> (data, $2); }
| TOK_IMULL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULL)> (data, $2, $4); }
| TOK_IMULL operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IMULL)> (data, $2, $4, $6); }
| TOK_IN operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(IN)> (data, $2, $4); }
| TOK_INC operand { x86_32_translate<X86_32_TOKEN(INC)> (data, $2); }
| TOK_INCB operand { x86_32_translate<X86_32_TOKEN(INCB)> (data, $2); }
| TOK_INCW operand { x86_32_translate<X86_32_TOKEN(INCW)> (data, $2); }
| TOK_INCL operand { x86_32_translate<X86_32_TOKEN(INCL)> (data, $2); }
| TOK_INSB  { x86_32_translate<X86_32_TOKEN(INSB)> (data); }
| TOK_INSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(INSB)> (data, $2, $4); }
| TOK_INSW  { x86_32_translate<X86_32_TOKEN(INSW)> (data); }
| TOK_INSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(INSW)> (data, $2, $4); }
| TOK_INSL  { x86_32_translate<X86_32_TOKEN(INSL)> (data); }
| TOK_INSL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(INSL)> (data, $2, $4); }
| TOK_INSD  { x86_32_translate<X86_32_TOKEN(INSD)> (data); }
| TOK_INSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(INSD)> (data, $2, $4); }
| TOK_INSERTPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(INSERTPS)> (data, $2, $4, $6); }
| TOK_INT operand { x86_32_translate<X86_32_TOKEN(INT)> (data, $2); }
| TOK_INTO  { x86_32_translate<X86_32_TOKEN(INTO)> (data); }
| TOK_INT3  { x86_32_translate<X86_32_TOKEN(INT3)> (data); }
| TOK_INVD  { x86_32_translate<X86_32_TOKEN(INVD)> (data); }
| TOK_INVLPG operand { x86_32_translate<X86_32_TOKEN(INVLPG)> (data, $2); }
| TOK_IRET  { x86_32_translate<X86_32_TOKEN(IRET)> (data); }
| TOK_IRETD  { x86_32_translate<X86_32_TOKEN(IRETD)> (data); }
| TOK_IRETQ  { x86_32_translate<X86_32_TOKEN(IRETQ)> (data); }
| TOK_JA operand { x86_32_translate<X86_32_TOKEN(JA)> (data, $2); }
| TOK_JAE operand { x86_32_translate<X86_32_TOKEN(JAE)> (data, $2); }
| TOK_JB operand { x86_32_translate<X86_32_TOKEN(JB)> (data, $2); }
| TOK_JBE operand { x86_32_translate<X86_32_TOKEN(JBE)> (data, $2); }
| TOK_JC operand { x86_32_translate<X86_32_TOKEN(JC)> (data, $2); }
| TOK_JCXZ operand { x86_32_translate<X86_32_TOKEN(JCXZ)> (data, $2); }
| TOK_JECXZ operand { x86_32_translate<X86_32_TOKEN(JECXZ)> (data, $2); }
| TOK_JRCXZ operand { x86_32_translate<X86_32_TOKEN(JRCXZ)> (data, $2); }
| TOK_JE operand { x86_32_translate<X86_32_TOKEN(JE)> (data, $2); }
| TOK_JG operand { x86_32_translate<X86_32_TOKEN(JG)> (data, $2); }
| TOK_JGE operand { x86_32_translate<X86_32_TOKEN(JGE)> (data, $2); }
| TOK_JL operand { x86_32_translate<X86_32_TOKEN(JL)> (data, $2); }
| TOK_JLE operand { x86_32_translate<X86_32_TOKEN(JLE)> (data, $2); }
| TOK_JNA operand { x86_32_translate<X86_32_TOKEN(JNA)> (data, $2); }
| TOK_JNAE operand { x86_32_translate<X86_32_TOKEN(JNAE)> (data, $2); }
| TOK_JNB operand { x86_32_translate<X86_32_TOKEN(JNB)> (data, $2); }
| TOK_JNBE operand { x86_32_translate<X86_32_TOKEN(JNBE)> (data, $2); }
| TOK_JNC operand { x86_32_translate<X86_32_TOKEN(JNC)> (data, $2); }
| TOK_JNE operand { x86_32_translate<X86_32_TOKEN(JNE)> (data, $2); }
| TOK_JNG operand { x86_32_translate<X86_32_TOKEN(JNG)> (data, $2); }
| TOK_JNGE operand { x86_32_translate<X86_32_TOKEN(JNGE)> (data, $2); }
| TOK_JNL operand { x86_32_translate<X86_32_TOKEN(JNL)> (data, $2); }
| TOK_JNLE operand { x86_32_translate<X86_32_TOKEN(JNLE)> (data, $2); }
| TOK_JNO operand { x86_32_translate<X86_32_TOKEN(JNO)> (data, $2); }
| TOK_JNP operand { x86_32_translate<X86_32_TOKEN(JNP)> (data, $2); }
| TOK_JNS operand { x86_32_translate<X86_32_TOKEN(JNS)> (data, $2); }
| TOK_JNZ operand { x86_32_translate<X86_32_TOKEN(JNZ)> (data, $2); }
| TOK_JO operand { x86_32_translate<X86_32_TOKEN(JO)> (data, $2); }
| TOK_JP operand { x86_32_translate<X86_32_TOKEN(JP)> (data, $2); }
| TOK_JPE operand { x86_32_translate<X86_32_TOKEN(JPE)> (data, $2); }
| TOK_JPO operand { x86_32_translate<X86_32_TOKEN(JPO)> (data, $2); }
| TOK_JS operand { x86_32_translate<X86_32_TOKEN(JS)> (data, $2); }
| TOK_JZ operand { x86_32_translate<X86_32_TOKEN(JZ)> (data, $2); }
| TOK_JMP operand { x86_32_translate<X86_32_TOKEN(JMP)> (data, $2); }
| TOK_JMPW operand { x86_32_translate<X86_32_TOKEN(JMPW)> (data, $2); }
| TOK_LAHF  { x86_32_translate<X86_32_TOKEN(LAHF)> (data); }
| TOK_LAR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LAR)> (data, $2, $4); }
| TOK_LDDQU operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LDDQU)> (data, $2, $4); }
| TOK_LDMXCSR operand { x86_32_translate<X86_32_TOKEN(LDMXCSR)> (data, $2); }
| TOK_LDS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LDS)> (data, $2, $4); }
| TOK_LES operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LES)> (data, $2, $4); }
| TOK_LFS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LFS)> (data, $2, $4); }
| TOK_LGS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LGS)> (data, $2, $4); }
| TOK_LSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LSS)> (data, $2, $4); }
| TOK_LEA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LEA)> (data, $2, $4); }
| TOK_LEAVE  { x86_32_translate<X86_32_TOKEN(LEAVE)> (data); }
| TOK_LEAVEW  { x86_32_translate<X86_32_TOKEN(LEAVEW)> (data); }
| TOK_LEAVEL  { x86_32_translate<X86_32_TOKEN(LEAVEL)> (data); }
| TOK_LFENCE  { x86_32_translate<X86_32_TOKEN(LFENCE)> (data); }
| TOK_LGDT operand { x86_32_translate<X86_32_TOKEN(LGDT)> (data, $2); }
| TOK_LIDT operand { x86_32_translate<X86_32_TOKEN(LIDT)> (data, $2); }
| TOK_LLDT operand { x86_32_translate<X86_32_TOKEN(LLDT)> (data, $2); }
| TOK_LMSW operand { x86_32_translate<X86_32_TOKEN(LMSW)> (data, $2); }
| TOK_LOCK { x86_32_translate<X86_32_TOKEN(LOCK)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(LOCK)> (data, false); }
| TOK_LODS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LODS)> (data, $2, $4); }
| TOK_LOOP operand { x86_32_translate<X86_32_TOKEN(LOOP)> (data, $2); }
| TOK_LOOPE operand { x86_32_translate<X86_32_TOKEN(LOOPE)> (data, $2); }
| TOK_LOOPNE operand { x86_32_translate<X86_32_TOKEN(LOOPNE)> (data, $2); }
| TOK_LOOPW operand { x86_32_translate<X86_32_TOKEN(LOOPW)> (data, $2); }
| TOK_LOOPEW operand { x86_32_translate<X86_32_TOKEN(LOOPEW)> (data, $2); }
| TOK_LOOPNEW operand { x86_32_translate<X86_32_TOKEN(LOOPNEW)> (data, $2); }
| TOK_LSL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(LSL)> (data, $2, $4); }
| TOK_LTR operand { x86_32_translate<X86_32_TOKEN(LTR)> (data, $2); }
| TOK_MASKMOVDQU operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MASKMOVDQU)> (data, $2, $4); }
| TOK_MASKMOVQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MASKMOVQ)> (data, $2, $4); }
| TOK_MAXPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXPD)> (data, $2, $4); }
| TOK_MAXPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXPD)> (data, $2, $4, $6); }
| TOK_MAXPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXPS)> (data, $2, $4); }
| TOK_MAXPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXPS)> (data, $2, $4, $6); }
| TOK_MAXSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXSD)> (data, $2, $4); }
| TOK_MAXSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXSD)> (data, $2, $4, $6); }
| TOK_MAXSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXSS)> (data, $2, $4); }
| TOK_MAXSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MAXSS)> (data, $2, $4, $6); }
| TOK_MFENCE  { x86_32_translate<X86_32_TOKEN(MFENCE)> (data); }
| TOK_MINPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINPD)> (data, $2, $4); }
| TOK_MINPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINPD)> (data, $2, $4, $6); }
| TOK_MINPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINPS)> (data, $2, $4); }
| TOK_MINPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINPS)> (data, $2, $4, $6); }
| TOK_MINSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINSD)> (data, $2, $4); }
| TOK_MINSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINSD)> (data, $2, $4, $6); }
| TOK_MINSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINSS)> (data, $2, $4); }
| TOK_MINSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MINSS)> (data, $2, $4, $6); }
| TOK_MONITOR  { x86_32_translate<X86_32_TOKEN(MONITOR)> (data); }
| TOK_MOV operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOV)> (data, $2, $4); }
| TOK_MOVB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVB)> (data, $2, $4); }
| TOK_MOVW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVW)> (data, $2, $4); }
| TOK_MOVL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVL)> (data, $2, $4); }
| TOK_MOVAPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVAPD)> (data, $2, $4); }
| TOK_MOVAPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVAPS)> (data, $2, $4); }
| TOK_MOVBE operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVBE)> (data, $2, $4); }
| TOK_MOVD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVD)> (data, $2, $4); }
| TOK_MOVQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVQ)> (data, $2, $4); }
| TOK_MOVDDUP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVDDUP)> (data, $2, $4); }
| TOK_MOVDQA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVDQA)> (data, $2, $4); }
| TOK_MOVDQU operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVDQU)> (data, $2, $4); }
| TOK_MOVDQ2Q operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVDQ2Q)> (data, $2, $4); }
| TOK_MOVHLPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHLPS)> (data, $2, $4); }
| TOK_MOVHLPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHLPS)> (data, $2, $4, $6); }
| TOK_MOVHPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHPD)> (data, $2, $4); }
| TOK_MOVHPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHPD)> (data, $2, $4, $6); }
| TOK_MOVHPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHPS)> (data, $2, $4); }
| TOK_MOVHPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVHPS)> (data, $2, $4, $6); }
| TOK_MOVLHPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLHPS)> (data, $2, $4); }
| TOK_MOVLHPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLHPS)> (data, $2, $4, $6); }
| TOK_MOVLPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLPD)> (data, $2, $4); }
| TOK_MOVLPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLPD)> (data, $2, $4, $6); }
| TOK_MOVLPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLPS)> (data, $2, $4); }
| TOK_MOVLPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVLPS)> (data, $2, $4, $6); }
| TOK_MOVMSKPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVMSKPD)> (data, $2, $4); }
| TOK_MOVMSKPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVMSKPS)> (data, $2, $4); }
| TOK_MOVNTDQA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTDQA)> (data, $2, $4); }
| TOK_MOVNTDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTDQ)> (data, $2, $4); }
| TOK_MOVNTI operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTI)> (data, $2, $4); }
| TOK_MOVNTPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTPD)> (data, $2, $4); }
| TOK_MOVNTPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTPS)> (data, $2, $4); }
| TOK_MOVNTQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVNTQ)> (data, $2, $4); }
| TOK_MOVQ2DQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVQ2DQ)> (data, $2, $4); }
| TOK_MOVSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSB)> (data, $2, $4); }
| TOK_MOVSBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSBW)> (data, $2, $4); }
| TOK_MOVSBL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSBL)> (data, $2, $4); }
| TOK_MOVSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSW)> (data, $2, $4); }
| TOK_MOVSWL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSWL)> (data, $2, $4); }
| TOK_MOVSL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSL)> (data, $2, $4); }
| TOK_MOVSHDUP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSHDUP)> (data, $2, $4); }
| TOK_MOVSLDUP operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSLDUP)> (data, $2, $4); }
| TOK_MOVSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSS)> (data, $2, $4); }
| TOK_MOVSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSS)> (data, $2, $4, $6); }

| TOK_MOVSXD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVSXD)> (data, $2, $4); }
| TOK_MOVUPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVUPD)> (data, $2, $4); }
| TOK_MOVUPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVUPS)> (data, $2, $4); }

| TOK_MOVZBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVZBW)> (data, $2, $4); }
| TOK_MOVZBL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVZBL)> (data, $2, $4); }
| TOK_MOVZWL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MOVZWL)> (data, $2, $4); }

| TOK_MPSADBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MPSADBW)> (data, $2, $4, $6); }
| TOK_MUL operand { x86_32_translate<X86_32_TOKEN(MUL)> (data, $2); }
| TOK_MULB operand { x86_32_translate<X86_32_TOKEN(MULB)> (data, $2); }
| TOK_MULW operand { x86_32_translate<X86_32_TOKEN(MULW)> (data, $2); }
| TOK_MULL operand { x86_32_translate<X86_32_TOKEN(MULL)> (data, $2); }
| TOK_MULPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULPD)> (data, $2, $4); }
| TOK_MULPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULPD)> (data, $2, $4, $6); }
| TOK_MULPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULPS)> (data, $2, $4); }
| TOK_MULPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULPS)> (data, $2, $4, $6); }
| TOK_MULSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULSD)> (data, $2, $4); }
| TOK_MULSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULSD)> (data, $2, $4, $6); }
| TOK_MULSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULSS)> (data, $2, $4); }
| TOK_MULSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(MULSS)> (data, $2, $4, $6); }
| TOK_MWAIT  { x86_32_translate<X86_32_TOKEN(MWAIT)> (data); }
| TOK_NEG operand { x86_32_translate<X86_32_TOKEN(NEG)> (data, $2); }
| TOK_NEGB operand { x86_32_translate<X86_32_TOKEN(NEGB)> (data, $2); }
| TOK_NEGW operand { x86_32_translate<X86_32_TOKEN(NEGW)> (data, $2); }
| TOK_NEGL operand { x86_32_translate<X86_32_TOKEN(NEGL)> (data, $2); }
| TOK_NOP  { x86_32_translate<X86_32_TOKEN(NOP)> (data); }
| TOK_NOP operand { x86_32_translate<X86_32_TOKEN(NOP)> (data, $2); }
| TOK_NOPB  { x86_32_translate<X86_32_TOKEN(NOPB)> (data); }
| TOK_NOPB operand { x86_32_translate<X86_32_TOKEN(NOPB)> (data, $2); }
| TOK_NOPW  { x86_32_translate<X86_32_TOKEN(NOPW)> (data); }
| TOK_NOPW operand { x86_32_translate<X86_32_TOKEN(NOPW)> (data, $2); }
| TOK_NOPL  { x86_32_translate<X86_32_TOKEN(NOPL)> (data); }
| TOK_NOPL operand { x86_32_translate<X86_32_TOKEN(NOPL)> (data, $2); }
| TOK_NOT operand { x86_32_translate<X86_32_TOKEN(NOT)> (data, $2); }
| TOK_NOTB operand { x86_32_translate<X86_32_TOKEN(NOTB)> (data, $2); }
| TOK_NOTW operand { x86_32_translate<X86_32_TOKEN(NOTW)> (data, $2); }
| TOK_NOTL operand { x86_32_translate<X86_32_TOKEN(NOTL)> (data, $2); }
| TOK_OR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(OR)> (data, $2, $4); }
| TOK_ORB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORB)> (data, $2, $4); }
| TOK_ORW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORW)> (data, $2, $4); }
| TOK_ORL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORL)> (data, $2, $4); }
| TOK_ORPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORPD)> (data, $2, $4); }
| TOK_ORPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORPD)> (data, $2, $4, $6); }
| TOK_ORPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORPS)> (data, $2, $4); }
| TOK_ORPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ORPS)> (data, $2, $4, $6); }
| TOK_OUT  { x86_32_translate<X86_32_TOKEN(OUT)> (data); }
| TOK_OUT operand { x86_32_translate<X86_32_TOKEN(OUT)> (data, $2); }
| TOK_OUTSB  { x86_32_translate<X86_32_TOKEN(OUTSB)> (data); }
| TOK_OUTSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(OUTSB)> (data, $2, $4); }
| TOK_OUTSW  { x86_32_translate<X86_32_TOKEN(OUTSW)> (data); }
| TOK_OUTSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(OUTSW)> (data, $2, $4); }
| TOK_OUTSL  { x86_32_translate<X86_32_TOKEN(OUTSL)> (data); }
| TOK_OUTSL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(OUTSL)> (data, $2, $4); }
| TOK_OUTSD  { x86_32_translate<X86_32_TOKEN(OUTSD)> (data); }
| TOK_OUTSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(OUTSD)> (data, $2, $4); }
| TOK_PABSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PABSB)> (data, $2, $4); }
| TOK_PABSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PABSW)> (data, $2, $4); }
| TOK_PABSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PABSD)> (data, $2, $4); }
| TOK_PACKSSWB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKSSWB)> (data, $2, $4); }
| TOK_PACKSSWB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKSSWB)> (data, $2, $4, $6); }
| TOK_PACKSSDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKSSDW)> (data, $2, $4); }
| TOK_PACKSSDW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKSSDW)> (data, $2, $4, $6); }
| TOK_PACKUSDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKUSDW)> (data, $2, $4); }
| TOK_PACKUSDW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKUSDW)> (data, $2, $4, $6); }
| TOK_PACKUSWB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKUSWB)> (data, $2, $4); }
| TOK_PACKUSWB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PACKUSWB)> (data, $2, $4, $6); }
| TOK_PADDB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDB)> (data, $2, $4); }
| TOK_PADDB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDB)> (data, $2, $4, $6); }
| TOK_PADDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDW)> (data, $2, $4); }
| TOK_PADDW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDW)> (data, $2, $4, $6); }
| TOK_PADDD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDD)> (data, $2, $4); }
| TOK_PADDD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDD)> (data, $2, $4, $6); }
| TOK_PADDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDQ)> (data, $2, $4); }
| TOK_PADDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDQ)> (data, $2, $4, $6); }
| TOK_PADDSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDSB)> (data, $2, $4); }
| TOK_PADDSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDSB)> (data, $2, $4, $6); }
| TOK_PADDSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDSW)> (data, $2, $4); }
| TOK_PADDSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDSW)> (data, $2, $4, $6); }
| TOK_PADDUSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDUSB)> (data, $2, $4); }
| TOK_PADDUSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDUSB)> (data, $2, $4, $6); }
| TOK_PADDUSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDUSW)> (data, $2, $4); }
| TOK_PADDUSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PADDUSW)> (data, $2, $4, $6); }
| TOK_PALIGNR operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PALIGNR)> (data, $2, $4, $6); }
| TOK_PAND operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAND)> (data, $2, $4); }
| TOK_PAND operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAND)> (data, $2, $4, $6); }
| TOK_PANDN operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PANDN)> (data, $2, $4); }
| TOK_PANDN operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PANDN)> (data, $2, $4, $6); }
| TOK_PAUSE  { x86_32_translate<X86_32_TOKEN(PAUSE)> (data); }
| TOK_PAVGB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAVGB)> (data, $2, $4); }
| TOK_PAVGB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAVGB)> (data, $2, $4, $6); }
| TOK_PAVGW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAVGW)> (data, $2, $4); }
| TOK_PAVGW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PAVGW)> (data, $2, $4, $6); }
| TOK_PBLENDVB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PBLENDVB)> (data, $2, $4, $6); }
| TOK_PBLENDW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PBLENDW)> (data, $2, $4, $6); }
| TOK_PCLMULQDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCLMULQDQ)> (data, $2, $4); }
| TOK_PCLMULQDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCLMULQDQ)> (data, $2, $4, $6); }
| TOK_PCMPEQB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQB)> (data, $2, $4); }
| TOK_PCMPEQB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQB)> (data, $2, $4, $6); }
| TOK_PCMPEQW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQW)> (data, $2, $4); }
| TOK_PCMPEQW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQW)> (data, $2, $4, $6); }
| TOK_PCMPEQD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQD)> (data, $2, $4); }
| TOK_PCMPEQD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQD)> (data, $2, $4, $6); }
| TOK_PCMPEQQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQQ)> (data, $2, $4); }
| TOK_PCMPEQQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPEQQ)> (data, $2, $4, $6); }
| TOK_PCMPESTRI operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPESTRI)> (data, $2, $4, $6); }
| TOK_PCMPESTRM operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPESTRM)> (data, $2, $4, $6); }
| TOK_PCMPGTB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTB)> (data, $2, $4); }
| TOK_PCMPGTB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTB)> (data, $2, $4, $6); }
| TOK_PCMPGTW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTW)> (data, $2, $4); }
| TOK_PCMPGTW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTW)> (data, $2, $4, $6); }
| TOK_PCMPGTD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTD)> (data, $2, $4); }
| TOK_PCMPGTD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTD)> (data, $2, $4, $6); }
| TOK_PCMPGTQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTQ)> (data, $2, $4); }
| TOK_PCMPGTQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPGTQ)> (data, $2, $4, $6); }
| TOK_PCMPISTRI operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPISTRI)> (data, $2, $4, $6); }
| TOK_PCMPISTRM operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PCMPISTRM)> (data, $2, $4, $6); }
| TOK_PEXTRB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PEXTRB)> (data, $2, $4, $6); }
| TOK_PEXTRD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PEXTRD)> (data, $2, $4, $6); }
| TOK_PEXTRQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PEXTRQ)> (data, $2, $4, $6); }
| TOK_PEXTRW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PEXTRW)> (data, $2, $4, $6); }
| TOK_PHADDW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDW)> (data, $2, $4); }
| TOK_PHADDW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDW)> (data, $2, $4, $6); }
| TOK_PHADDD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDD)> (data, $2, $4); }
| TOK_PHADDD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDD)> (data, $2, $4, $6); }
| TOK_PHADDSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDSW)> (data, $2, $4); }
| TOK_PHADDSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHADDSW)> (data, $2, $4, $6); }
| TOK_PHMINPOSUW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHMINPOSUW)> (data, $2, $4); }
| TOK_PHSUBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBW)> (data, $2, $4); }
| TOK_PHSUBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBW)> (data, $2, $4, $6); }
| TOK_PHSUBD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBD)> (data, $2, $4); }
| TOK_PHSUBD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBD)> (data, $2, $4, $6); }
| TOK_PHSUBSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBSW)> (data, $2, $4); }
| TOK_PHSUBSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PHSUBSW)> (data, $2, $4, $6); }
| TOK_PINSRB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PINSRB)> (data, $2, $4, $6); }
| TOK_PINSRD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PINSRD)> (data, $2, $4, $6); }
| TOK_PINSRQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PINSRQ)> (data, $2, $4, $6); }
| TOK_PINSRW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PINSRW)> (data, $2, $4, $6); }
| TOK_PMADDUBSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMADDUBSW)> (data, $2, $4); }
| TOK_PMADDUBSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMADDUBSW)> (data, $2, $4, $6); }
| TOK_PMADDWD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMADDWD)> (data, $2, $4); }
| TOK_PMADDWD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMADDWD)> (data, $2, $4, $6); }
| TOK_PMAXSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSB)> (data, $2, $4); }
| TOK_PMAXSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSB)> (data, $2, $4, $6); }
| TOK_PMAXSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSD)> (data, $2, $4); }
| TOK_PMAXSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSD)> (data, $2, $4, $6); }
| TOK_PMAXSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSW)> (data, $2, $4); }
| TOK_PMAXSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXSW)> (data, $2, $4, $6); }
| TOK_PMAXUB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUB)> (data, $2, $4); }
| TOK_PMAXUB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUB)> (data, $2, $4, $6); }
| TOK_PMAXUD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUD)> (data, $2, $4); }
| TOK_PMAXUD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUD)> (data, $2, $4, $6); }
| TOK_PMAXUW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUW)> (data, $2, $4); }
| TOK_PMAXUW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMAXUW)> (data, $2, $4, $6); }
| TOK_PMINSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSB)> (data, $2, $4); }
| TOK_PMINSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSB)> (data, $2, $4, $6); }
| TOK_PMINSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSD)> (data, $2, $4); }
| TOK_PMINSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSD)> (data, $2, $4, $6); }
| TOK_PMINSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSW)> (data, $2, $4); }
| TOK_PMINSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINSW)> (data, $2, $4, $6); }
| TOK_PMINUB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUB)> (data, $2, $4); }
| TOK_PMINUB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUB)> (data, $2, $4, $6); }
| TOK_PMINUD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUD)> (data, $2, $4); }
| TOK_PMINUD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUD)> (data, $2, $4, $6); }
| TOK_PMINUW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUW)> (data, $2, $4); }
| TOK_PMINUW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMINUW)> (data, $2, $4, $6); }
| TOK_PMOVMSKB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMOVMSKB)> (data, $2, $4); }
| TOK_PMOVSX operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMOVSX)> (data, $2, $4); }
| TOK_PMOVZX operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMOVZX)> (data, $2, $4); }
| TOK_PMULDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULDQ)> (data, $2, $4); }
| TOK_PMULDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULDQ)> (data, $2, $4, $6); }
| TOK_PMULHRSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHRSW)> (data, $2, $4); }
| TOK_PMULHRSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHRSW)> (data, $2, $4, $6); }
| TOK_PMULHUW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHUW)> (data, $2, $4); }
| TOK_PMULHUW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHUW)> (data, $2, $4, $6); }
| TOK_PMULHW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHW)> (data, $2, $4); }
| TOK_PMULHW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULHW)> (data, $2, $4, $6); }
| TOK_PMULLD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULLD)> (data, $2, $4); }
| TOK_PMULLD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULLD)> (data, $2, $4, $6); }
| TOK_PMULLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULLW)> (data, $2, $4); }
| TOK_PMULLW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULLW)> (data, $2, $4, $6); }
| TOK_PMULUDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULUDQ)> (data, $2, $4); }
| TOK_PMULUDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PMULUDQ)> (data, $2, $4, $6); }
| TOK_POP operand { x86_32_translate<X86_32_TOKEN(POP)> (data, $2); }
| TOK_POPW operand { x86_32_translate<X86_32_TOKEN(POPW)> (data, $2); }
| TOK_POPL operand { x86_32_translate<X86_32_TOKEN(POPL)> (data, $2); }
| TOK_POPA  { x86_32_translate<X86_32_TOKEN(POPA)> (data); }
| TOK_POPAW  { x86_32_translate<X86_32_TOKEN(POPAW)> (data); }
| TOK_POPAL  { x86_32_translate<X86_32_TOKEN(POPAL)> (data); }
| TOK_POPAD  { x86_32_translate<X86_32_TOKEN(POPAD)> (data); }
| TOK_POPCNT operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(POPCNT)> (data, $2, $4); }
| TOK_POPF  { x86_32_translate<X86_32_TOKEN(POPF)> (data); }
| TOK_POPFW  { x86_32_translate<X86_32_TOKEN(POPFW)> (data); }
| TOK_POPFQ  { x86_32_translate<X86_32_TOKEN(POPFQ)> (data); }
| TOK_POR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(POR)> (data, $2, $4); }
| TOK_POR operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(POR)> (data, $2, $4, $6); }
| TOK_PREFETCHT0 operand { x86_32_translate<X86_32_TOKEN(PREFETCHT0)> (data, $2); }
| TOK_PREFETCHT1 operand { x86_32_translate<X86_32_TOKEN(PREFETCHT1)> (data, $2); }
| TOK_PREFETCHT2 operand { x86_32_translate<X86_32_TOKEN(PREFETCHT2)> (data, $2); }
| TOK_PREFETCHNTA operand { x86_32_translate<X86_32_TOKEN(PREFETCHNTA)> (data, $2); }
| TOK_PSADBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSADBW)> (data, $2, $4); }
| TOK_PSADBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSADBW)> (data, $2, $4, $6); }
| TOK_PSHUFB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFB)> (data, $2, $4); }
| TOK_PSHUFB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFB)> (data, $2, $4, $6); }
| TOK_PSHUFD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFD)> (data, $2, $4, $6); }
| TOK_PSHUFHW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFHW)> (data, $2, $4, $6); }
| TOK_PSHUFLW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFLW)> (data, $2, $4, $6); }
| TOK_PSHUFW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSHUFW)> (data, $2, $4, $6); }
| TOK_PSIGNB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGNB)> (data, $2, $4); }
| TOK_PSIGNB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGNB)> (data, $2, $4, $6); }
| TOK_PSIGNW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGNW)> (data, $2, $4); }
| TOK_PSIGNW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGNW)> (data, $2, $4, $6); }
| TOK_PSIGND operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGND)> (data, $2, $4); }
| TOK_PSIGND operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSIGND)> (data, $2, $4, $6); }
| TOK_PSLLDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLDQ)> (data, $2, $4); }
| TOK_PSLLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLW)> (data, $2, $4); }
| TOK_PSLLW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLW)> (data, $2, $4, $6); }
| TOK_PSLLD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLD)> (data, $2, $4); }
| TOK_PSLLD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLD)> (data, $2, $4, $6); }
| TOK_PSLLQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLQ)> (data, $2, $4); }
| TOK_PSLLQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSLLQ)> (data, $2, $4, $6); }
| TOK_PSRAW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRAW)> (data, $2, $4); }
| TOK_PSRAW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRAW)> (data, $2, $4, $6); }
| TOK_PSRAD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRAD)> (data, $2, $4); }
| TOK_PSRAD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRAD)> (data, $2, $4, $6); }
| TOK_PSRLDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLDQ)> (data, $2, $4); }
| TOK_PSRLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLW)> (data, $2, $4); }
| TOK_PSRLW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLW)> (data, $2, $4, $6); }
| TOK_PSRLD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLD)> (data, $2, $4); }
| TOK_PSRLD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLD)> (data, $2, $4, $6); }
| TOK_PSRLQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLQ)> (data, $2, $4); }
| TOK_PSRLQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSRLQ)> (data, $2, $4, $6); }
| TOK_PSUBB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBB)> (data, $2, $4); }
| TOK_PSUBB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBB)> (data, $2, $4, $6); }
| TOK_PSUBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBW)> (data, $2, $4); }
| TOK_PSUBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBW)> (data, $2, $4, $6); }
| TOK_PSUBD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBD)> (data, $2, $4); }
| TOK_PSUBD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBD)> (data, $2, $4, $6); }
| TOK_PSUBQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBQ)> (data, $2, $4); }
| TOK_PSUBQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBQ)> (data, $2, $4, $6); }
| TOK_PSUBSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBSB)> (data, $2, $4); }
| TOK_PSUBSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBSB)> (data, $2, $4, $6); }
| TOK_PSUBSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBSW)> (data, $2, $4); }
| TOK_PSUBSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBSW)> (data, $2, $4, $6); }
| TOK_PSUBUSB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBUSB)> (data, $2, $4); }
| TOK_PSUBUSB operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBUSB)> (data, $2, $4, $6); }
| TOK_PSUBUSW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBUSW)> (data, $2, $4); }
| TOK_PSUBUSW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PSUBUSW)> (data, $2, $4, $6); }
| TOK_PTEST operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PTEST)> (data, $2, $4); }
| TOK_PUNPCKHBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHBW)> (data, $2, $4); }
| TOK_PUNPCKHBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHBW)> (data, $2, $4, $6); }
| TOK_PUNPCKHWD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHWD)> (data, $2, $4); }
| TOK_PUNPCKHWD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHWD)> (data, $2, $4, $6); }
| TOK_PUNPCKHDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHDQ)> (data, $2, $4); }
| TOK_PUNPCKHDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHDQ)> (data, $2, $4, $6); }
| TOK_PUNPCKHQDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHQDQ)> (data, $2, $4); }
| TOK_PUNPCKHQDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKHQDQ)> (data, $2, $4, $6); }
| TOK_PUNPCKLBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLBW)> (data, $2, $4); }
| TOK_PUNPCKLBW operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLBW)> (data, $2, $4, $6); }
| TOK_PUNPCKLWD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLWD)> (data, $2, $4); }
| TOK_PUNPCKLWD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLWD)> (data, $2, $4, $6); }
| TOK_PUNPCKLDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLDQ)> (data, $2, $4); }
| TOK_PUNPCKLDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLDQ)> (data, $2, $4, $6); }
| TOK_PUNPCKLQDQ operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLQDQ)> (data, $2, $4); }
| TOK_PUNPCKLQDQ operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PUNPCKLQDQ)> (data, $2, $4, $6); }
| TOK_PUSH operand { x86_32_translate<X86_32_TOKEN(PUSH)> (data, $2); }
| TOK_PUSHW operand { x86_32_translate<X86_32_TOKEN(PUSHW)> (data, $2); }
| TOK_PUSHL operand { x86_32_translate<X86_32_TOKEN(PUSHL)> (data, $2); }
| TOK_PUSHA  { x86_32_translate<X86_32_TOKEN(PUSHA)> (data); }
| TOK_PUSHAW  { x86_32_translate<X86_32_TOKEN(PUSHAW)> (data); }
| TOK_PUSHAL  { x86_32_translate<X86_32_TOKEN(PUSHAL)> (data); }
| TOK_PUSHF  { x86_32_translate<X86_32_TOKEN(PUSHF)> (data); }
| TOK_PUSHFW  { x86_32_translate<X86_32_TOKEN(PUSHFW)> (data); }
| TOK_PXOR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PXOR)> (data, $2, $4); }
| TOK_PXOR operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(PXOR)> (data, $2, $4, $6); }
| TOK_RCL operand { x86_32_translate<X86_32_TOKEN(RCL)> (data, $2); }
| TOK_RCL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCL)> (data, $2, $4); }
| TOK_RCLB operand { x86_32_translate<X86_32_TOKEN(RCLB)> (data, $2); }
| TOK_RCLB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCLB)> (data, $2, $4); }
| TOK_RCLW operand { x86_32_translate<X86_32_TOKEN(RCLW)> (data, $2); }
| TOK_RCLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCLW)> (data, $2, $4); }
| TOK_RCLL operand { x86_32_translate<X86_32_TOKEN(RCLL)> (data, $2); }
| TOK_RCLL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCLL)> (data, $2, $4); }
| TOK_RCR operand { x86_32_translate<X86_32_TOKEN(RCR)> (data, $2); }
| TOK_RCR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCR)> (data, $2, $4); }
| TOK_RCRB operand { x86_32_translate<X86_32_TOKEN(RCRB)> (data, $2); }
| TOK_RCRB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCRB)> (data, $2, $4); }
| TOK_RCRW operand { x86_32_translate<X86_32_TOKEN(RCRW)> (data, $2); }
| TOK_RCRW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCRW)> (data, $2, $4); }
| TOK_RCRL operand { x86_32_translate<X86_32_TOKEN(RCRL)> (data, $2); }
| TOK_RCRL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCRL)> (data, $2, $4); }
| TOK_ROL operand { x86_32_translate<X86_32_TOKEN(ROL)> (data, $2); }
| TOK_ROL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROL)> (data, $2, $4); }
| TOK_ROLB operand { x86_32_translate<X86_32_TOKEN(ROLB)> (data, $2); }
| TOK_ROLB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROLB)> (data, $2, $4); }
| TOK_ROLW operand { x86_32_translate<X86_32_TOKEN(ROLW)> (data, $2); }
| TOK_ROLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROLW)> (data, $2, $4); }
| TOK_ROLL operand { x86_32_translate<X86_32_TOKEN(ROLL)> (data, $2); }
| TOK_ROLL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROLL)> (data, $2, $4); }
| TOK_ROR operand { x86_32_translate<X86_32_TOKEN(ROR)> (data, $2); }
| TOK_ROR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROR)> (data, $2, $4); }
| TOK_RORB operand { x86_32_translate<X86_32_TOKEN(RORB)> (data, $2); }
| TOK_RORB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RORB)> (data, $2, $4); }
| TOK_RORW operand { x86_32_translate<X86_32_TOKEN(RORW)> (data, $2); }
| TOK_RORW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RORW)> (data, $2, $4); }
| TOK_RORL operand { x86_32_translate<X86_32_TOKEN(RORL)> (data, $2); }
| TOK_RORL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RORL)> (data, $2, $4); }
| TOK_RCPPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCPPS)> (data, $2, $4); }
| TOK_RCPSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCPSS)> (data, $2, $4); }
| TOK_RCPSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RCPSS)> (data, $2, $4, $6); }
| TOK_RDMSR  { x86_32_translate<X86_32_TOKEN(RDMSR)> (data); }
| TOK_RDPMC  { x86_32_translate<X86_32_TOKEN(RDPMC)> (data); }
| TOK_RDRAND operand { x86_32_translate<X86_32_TOKEN(RDRAND)> (data, $2); }
| TOK_RDTSC  { x86_32_translate<X86_32_TOKEN(RDTSC)> (data); }
| TOK_RDTSCP  { x86_32_translate<X86_32_TOKEN(RDTSCP)> (data); }
| TOK_REP { x86_32_translate<X86_32_TOKEN(REP)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(REP)> (data, false); }
| TOK_REPE { x86_32_translate<X86_32_TOKEN(REPE)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(REPE)> (data, false); }
| TOK_REPZ { x86_32_translate<X86_32_TOKEN(REPZ)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(REPZ)> (data, false); }
| TOK_REPNE { x86_32_translate<X86_32_TOKEN(REPNE)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(REPNE)> (data, false); }
| TOK_REPNZ { x86_32_translate<X86_32_TOKEN(REPNZ)> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(REPNZ)> (data, false); }
| TOK_RET  { x86_32_translate<X86_32_TOKEN(RET)> (data); }
| TOK_RET operand { x86_32_translate<X86_32_TOKEN(RET)> (data, $2); }
| TOK_ROUNDPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROUNDPD)> (data, $2, $4, $6); }
| TOK_ROUNDPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROUNDPS)> (data, $2, $4, $6); }
| TOK_ROUNDSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROUNDSD)> (data, $2, $4, $6); }
| TOK_ROUNDSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(ROUNDSS)> (data, $2, $4, $6); }
| TOK_RSM  { x86_32_translate<X86_32_TOKEN(RSM)> (data); }
| TOK_RSQRTPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RSQRTPS)> (data, $2, $4); }
| TOK_RSQRTSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RSQRTSS)> (data, $2, $4); }
| TOK_RSQRTSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(RSQRTSS)> (data, $2, $4, $6); }
| TOK_SAHF  { x86_32_translate<X86_32_TOKEN(SAHF)> (data); }
| TOK_SAL operand { x86_32_translate<X86_32_TOKEN(SAL)> (data, $2); }
| TOK_SAL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SAL)> (data, $2, $4); }
| TOK_SALB operand { x86_32_translate<X86_32_TOKEN(SALB)> (data, $2); }
| TOK_SALB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SALB)> (data, $2, $4); }
| TOK_SALW operand { x86_32_translate<X86_32_TOKEN(SALW)> (data, $2); }
| TOK_SALW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SALW)> (data, $2, $4); }
| TOK_SALL operand { x86_32_translate<X86_32_TOKEN(SALL)> (data, $2); }
| TOK_SALL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SALL)> (data, $2, $4); }
| TOK_SAR operand { x86_32_translate<X86_32_TOKEN(SAR)> (data, $2); }
| TOK_SAR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SAR)> (data, $2, $4); }
| TOK_SARB operand { x86_32_translate<X86_32_TOKEN(SARB)> (data, $2); }
| TOK_SARB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SARB)> (data, $2, $4); }
| TOK_SARW operand { x86_32_translate<X86_32_TOKEN(SARW)> (data, $2); }
| TOK_SARW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SARW)> (data, $2, $4); }
| TOK_SARL operand { x86_32_translate<X86_32_TOKEN(SARL)> (data, $2); }
| TOK_SARL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SARL)> (data, $2, $4); }
| TOK_SHL operand { x86_32_translate<X86_32_TOKEN(SHL)> (data, $2); }
| TOK_SHL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHL)> (data, $2, $4); }
| TOK_SHLB operand { x86_32_translate<X86_32_TOKEN(SHLB)> (data, $2); }
| TOK_SHLB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHLB)> (data, $2, $4); }
| TOK_SHLW operand { x86_32_translate<X86_32_TOKEN(SHLW)> (data, $2); }
| TOK_SHLW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHLW)> (data, $2, $4); }
| TOK_SHLL operand { x86_32_translate<X86_32_TOKEN(SHLL)> (data, $2); }
| TOK_SHLL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHLL)> (data, $2, $4); }
| TOK_SHR operand { x86_32_translate<X86_32_TOKEN(SHR)> (data, $2); }
| TOK_SHR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHR)> (data, $2, $4); }
| TOK_SHRB operand { x86_32_translate<X86_32_TOKEN(SHRB)> (data, $2); }
| TOK_SHRB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHRB)> (data, $2, $4); }
| TOK_SHRW operand { x86_32_translate<X86_32_TOKEN(SHRW)> (data, $2); }
| TOK_SHRW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHRW)> (data, $2, $4); }
| TOK_SHRL operand { x86_32_translate<X86_32_TOKEN(SHRL)> (data, $2); }
| TOK_SHRL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHRL)> (data, $2, $4); }
| TOK_SBB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SBB)> (data, $2, $4); }
| TOK_SBBB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SBBB)> (data, $2, $4); }
| TOK_SBBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SBBW)> (data, $2, $4); }
| TOK_SBBL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SBBL)> (data, $2, $4); }
| TOK_SCAS  { x86_32_translate<X86_32_TOKEN(SCAS)> (data); }
| TOK_SCAS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SCAS)> (data, $2, $4); }
| TOK_SCASB  { x86_32_translate<X86_32_TOKEN(SCASB)> (data); }
| TOK_SCASB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SCASB)> (data, $2, $4); }
| TOK_SCASW  { x86_32_translate<X86_32_TOKEN(SCASW)> (data); }
| TOK_SCASW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SCASW)> (data, $2, $4); }
| TOK_SCASD  { x86_32_translate<X86_32_TOKEN(SCASD)> (data); }
| TOK_SCASD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SCASD)> (data, $2, $4); }
| TOK_SETA operand { x86_32_translate<X86_32_TOKEN(SETA)> (data, $2); }
| TOK_SETAE operand { x86_32_translate<X86_32_TOKEN(SETAE)> (data, $2); }
| TOK_SETB operand { x86_32_translate<X86_32_TOKEN(SETB)> (data, $2); }
| TOK_SETBE operand { x86_32_translate<X86_32_TOKEN(SETBE)> (data, $2); }
| TOK_SETC operand { x86_32_translate<X86_32_TOKEN(SETC)> (data, $2); }
| TOK_SETE operand { x86_32_translate<X86_32_TOKEN(SETE)> (data, $2); }
| TOK_SETG operand { x86_32_translate<X86_32_TOKEN(SETG)> (data, $2); }
| TOK_SETGE operand { x86_32_translate<X86_32_TOKEN(SETGE)> (data, $2); }
| TOK_SETL operand { x86_32_translate<X86_32_TOKEN(SETL)> (data, $2); }
| TOK_SETLE operand { x86_32_translate<X86_32_TOKEN(SETLE)> (data, $2); }
| TOK_SETNA operand { x86_32_translate<X86_32_TOKEN(SETNA)> (data, $2); }
| TOK_SETNAE operand { x86_32_translate<X86_32_TOKEN(SETNAE)> (data, $2); }
| TOK_SETNB operand { x86_32_translate<X86_32_TOKEN(SETNB)> (data, $2); }
| TOK_SETNBE operand { x86_32_translate<X86_32_TOKEN(SETNBE)> (data, $2); }
| TOK_SETNC operand { x86_32_translate<X86_32_TOKEN(SETNC)> (data, $2); }
| TOK_SETNE operand { x86_32_translate<X86_32_TOKEN(SETNE)> (data, $2); }
| TOK_SETNG operand { x86_32_translate<X86_32_TOKEN(SETNG)> (data, $2); }
| TOK_SETNGE operand { x86_32_translate<X86_32_TOKEN(SETNGE)> (data, $2); }
| TOK_SETNL operand { x86_32_translate<X86_32_TOKEN(SETNL)> (data, $2); }
| TOK_SETNLE operand { x86_32_translate<X86_32_TOKEN(SETNLE)> (data, $2); }
| TOK_SETNO operand { x86_32_translate<X86_32_TOKEN(SETNO)> (data, $2); }
| TOK_SETNP operand { x86_32_translate<X86_32_TOKEN(SETNP)> (data, $2); }
| TOK_SETNS operand { x86_32_translate<X86_32_TOKEN(SETNS)> (data, $2); }
| TOK_SETNZ operand { x86_32_translate<X86_32_TOKEN(SETNZ)> (data, $2); }
| TOK_SETO operand { x86_32_translate<X86_32_TOKEN(SETO)> (data, $2); }
| TOK_SETP operand { x86_32_translate<X86_32_TOKEN(SETP)> (data, $2); }
| TOK_SETPE operand { x86_32_translate<X86_32_TOKEN(SETPE)> (data, $2); }
| TOK_SETPO operand { x86_32_translate<X86_32_TOKEN(SETPO)> (data, $2); }
| TOK_SETS operand { x86_32_translate<X86_32_TOKEN(SETS)> (data, $2); }
| TOK_SETZ operand { x86_32_translate<X86_32_TOKEN(SETZ)> (data, $2); }
| TOK_SFENCE  { x86_32_translate<X86_32_TOKEN(SFENCE)> (data); }
| TOK_SGDT operand { x86_32_translate<X86_32_TOKEN(SGDT)> (data, $2); }
| TOK_SHLD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHLD)> (data, $2, $4, $6); }
| TOK_SHRD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHRD)> (data, $2, $4, $6); }
| TOK_SHUFPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHUFPD)> (data, $2, $4, $6); }
| TOK_SHUFPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SHUFPS)> (data, $2, $4, $6); }
| TOK_SIDT operand { x86_32_translate<X86_32_TOKEN(SIDT)> (data, $2); }
| TOK_SLDT operand { x86_32_translate<X86_32_TOKEN(SLDT)> (data, $2); }
| TOK_SMSW operand { x86_32_translate<X86_32_TOKEN(SMSW)> (data, $2); }
| TOK_SQRTPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTPD)> (data, $2, $4); }
| TOK_SQRTPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTPS)> (data, $2, $4); }
| TOK_SQRTSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTSD)> (data, $2, $4); }
| TOK_SQRTSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTSD)> (data, $2, $4, $6); }
| TOK_SQRTSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTSS)> (data, $2, $4); }
| TOK_SQRTSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SQRTSS)> (data, $2, $4, $6); }
| TOK_STC  { x86_32_translate<X86_32_TOKEN(STC)> (data); }
| TOK_STD  { x86_32_translate<X86_32_TOKEN(STD)> (data); }
| TOK_STI  { x86_32_translate<X86_32_TOKEN(STI)> (data); }
| TOK_STMXCSR operand { x86_32_translate<X86_32_TOKEN(STMXCSR)> (data, $2); }
| TOK_STOS  { x86_32_translate<X86_32_TOKEN(STOS)> (data); }
| TOK_STOS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(STOS)> (data, $2, $4); }
| TOK_STR operand { x86_32_translate<X86_32_TOKEN(STR)> (data, $2); }
| TOK_SUB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUB)> (data, $2, $4); }
| TOK_SUBB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBB)> (data, $2, $4); }
| TOK_SUBW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBW)> (data, $2, $4); }
| TOK_SUBL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBL)> (data, $2, $4); }
| TOK_SUBPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBPD)> (data, $2, $4); }
| TOK_SUBPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBPD)> (data, $2, $4, $6); }
| TOK_SUBPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBPS)> (data, $2, $4); }
| TOK_SUBPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBPS)> (data, $2, $4, $6); }
| TOK_SUBSD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBSD)> (data, $2, $4); }
| TOK_SUBSD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBSD)> (data, $2, $4, $6); }
| TOK_SUBSS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBSS)> (data, $2, $4); }
| TOK_SUBSS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(SUBSS)> (data, $2, $4, $6); }
| TOK_SWAPGS  { x86_32_translate<X86_32_TOKEN(SWAPGS)> (data); }
| TOK_SYSCALL  { x86_32_translate<X86_32_TOKEN(SYSCALL)> (data); }
| TOK_SYSENTER  { x86_32_translate<X86_32_TOKEN(SYSENTER)> (data); }
| TOK_SYSEXIT  { x86_32_translate<X86_32_TOKEN(SYSEXIT)> (data); }
| TOK_SYSRET  { x86_32_translate<X86_32_TOKEN(SYSRET)> (data); }
| TOK_TEST operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(TEST)> (data, $2, $4); }
| TOK_TESTB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(TESTB)> (data, $2, $4); }
| TOK_TESTW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(TESTW)> (data, $2, $4); }
| TOK_TESTL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(TESTL)> (data, $2, $4); }
| TOK_UCOMISD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UCOMISD)> (data, $2, $4); }
| TOK_UCOMISS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UCOMISS)> (data, $2, $4); }
| TOK_UD2  { x86_32_translate<X86_32_TOKEN(UD2)> (data); }
| TOK_UNPCKHPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKHPD)> (data, $2, $4); }
| TOK_UNPCKHPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKHPD)> (data, $2, $4, $6); }
| TOK_UNPCKHPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKHPS)> (data, $2, $4); }
| TOK_UNPCKHPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKHPS)> (data, $2, $4, $6); }
| TOK_UNPCKLPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKLPD)> (data, $2, $4); }
| TOK_UNPCKLPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKLPD)> (data, $2, $4, $6); }
| TOK_UNPCKLPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKLPS)> (data, $2, $4); }
| TOK_UNPCKLPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(UNPCKLPS)> (data, $2, $4, $6); }
| TOK_VBROADCAST operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VBROADCAST)> (data, $2, $4); }
| TOK_VERR  { x86_32_translate<X86_32_TOKEN(VERR)> (data); }
| TOK_VERR operand { x86_32_translate<X86_32_TOKEN(VERR)> (data, $2); }
| TOK_VERW  { x86_32_translate<X86_32_TOKEN(VERW)> (data); }
| TOK_VERW operand { x86_32_translate<X86_32_TOKEN(VERW)> (data, $2); }
| TOK_VEXTRACTF128 operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VEXTRACTF128)> (data, $2, $4); }
| TOK_VMASKMOV operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VMASKMOV)> (data, $2, $4, $6); }
| TOK_VINSERTF128 operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VINSERTF128)> (data, $2, $4, $6); }
| TOK_VPERMILPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VPERMILPD)> (data, $2, $4); }
| TOK_VPERMILPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VPERMILPD)> (data, $2, $4, $6); }
| TOK_VPERMILPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VPERMILPS)> (data, $2, $4); }
| TOK_VPERMILPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VPERMILPS)> (data, $2, $4, $6); }
| TOK_VPERM2F128 operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VPERM2F128)> (data, $2, $4, $6); }
| TOK_VTESTPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VTESTPD)> (data, $2, $4); }
| TOK_VTESTPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(VTESTPS)> (data, $2, $4); }
| TOK_VZEROALL  { x86_32_translate<X86_32_TOKEN(VZEROALL)> (data); }
| TOK_VZEROUPPER  { x86_32_translate<X86_32_TOKEN(VZEROUPPER)> (data); }
| TOK_WAIT  { x86_32_translate<X86_32_TOKEN(WAIT)> (data); }
| TOK_FWAIT  { x86_32_translate<X86_32_TOKEN(FWAIT)> (data); }
| TOK_WBINVD  { x86_32_translate<X86_32_TOKEN(WBINVD)> (data); }
| TOK_WRMSR  { x86_32_translate<X86_32_TOKEN(WRMSR)> (data); }
| TOK_XADD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XADD)> (data, $2, $4); }
| TOK_XCHG operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XCHG)> (data, $2, $4); }
| TOK_XGETBV  { x86_32_translate<X86_32_TOKEN(XGETBV)> (data); }
| TOK_XLAT operand { x86_32_translate<X86_32_TOKEN(XLAT)> (data, $2); }
| TOK_XLATB  { x86_32_translate<X86_32_TOKEN(XLATB)> (data); }
| TOK_XOR operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XOR)> (data, $2, $4); }
| TOK_XORB operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORB)> (data, $2, $4); }
| TOK_XORW operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORW)> (data, $2, $4); }
| TOK_XORL operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORL)> (data, $2, $4); }
| TOK_XORPD operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORPD)> (data, $2, $4); }
| TOK_XORPD operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORPD)> (data, $2, $4, $6); }
| TOK_XORPS operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORPS)> (data, $2, $4); }
| TOK_XORPS operand TOK_COMMA operand TOK_COMMA operand { x86_32_translate<X86_32_TOKEN(XORPS)> (data, $2, $4, $6); }
| TOK_XRSTOR operand { x86_32_translate<X86_32_TOKEN(XRSTOR)> (data, $2); }
| TOK_XSAVE operand { x86_32_translate<X86_32_TOKEN(XSAVE)> (data, $2); }
| TOK_XSAVEOPT operand { x86_32_translate<X86_32_TOKEN(XSAVEOPT)> (data, $2); }
| TOK_XSETBV  { x86_32_translate<X86_32_TOKEN(XSETBV)> (data); }
;

%% /***** Parser subroutines *****/

void parser::error(const parser::location_type &loc,
		   const string &msg)
{
  cerr << loc << ":" << msg << endl;
}

