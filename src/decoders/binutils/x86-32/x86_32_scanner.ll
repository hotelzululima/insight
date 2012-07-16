%{                      /* -*- C++ -*- */

#include <cerrno>
#include <climits>
#include <cstdlib>
#include <sstream>
#include <string>
#include <unistd.h>

#include "x86_32_parser.hh"

#define YY_DECL					 \
  x86_32::parser::token_type			 \
    yylex(x86_32::parser::semantic_type *yylval, \
	  x86_32::parser::location_type *yylloc)

/* Work around an incompatibility in flex (at least versions 2.5.31
 * through 2.5.33): it generates code that does not conform to C89. */
/* FIXME: Is this needed when the option 'noyywrap' has been set ? */
#undef yywrap
#define yywrap() 1

/* By default yylex returns int, we use token_type. Unfortunately
 * yyterminate by default returns 0, which is not of token_type. */
#define yyterminate() return token::TOK_EOF

/* This disables inclusion of unistd.h, which is not available under
 * Visual C++ on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

/* This suffices to track locations accurately. Each time yylex is
 * invoked, the begin position is moved onto the end position. */
#define YY_USER_ACTION yylloc->columns(yyleng);

using namespace std;
using namespace x86_32;

typedef parser::token token;


%}

 /* Flex efficiency tuning */
%option 7bit noyywrap nounput batch full align
%option prefix="x86_32_"

 /* Getting the scanner to share with other architectures */
 // %option reentrant
 // %option bison-bridge
 // %option prefix="x86_32_"

 /* Custom macros */
hexvalue  [0-9a-f]+
varname   [a-z][a-z0-9]+
optype    [bswlqt]

 /* NOTE: optype immediately follows the operator/mnemonic and gives
  * the type of the handled data-size:
  * b = byte (8 bit)
  * s = short (16 bit integer) or single (32-bit floating point)
  * w = word (16 bit)
  * l = long (32 bit integer or 64-bit floating point)
  * q = quad (64 bit)
  * t = ten bytes (80-bit floating point)
  * _ = default (no postfix given) a word size in the current architecture.
  */


%% /***** Lexer rules *****/

%{
  /* Reset location at the beginning of yylex() */
  yylloc->step();
%}

"cs"               { return token::TOK_CS; }
"fs"               { return token::TOK_FS; }
"ss"               { return token::TOK_SS; }
"ds"               { return token::TOK_DS; }
"es"               { return token::TOK_ES; }
"gs"               { return token::TOK_GS; }
"data32"           { return token::TOK_DATA32; }
"data16"           { return token::TOK_DATA16; }
"addr16"           { return token::TOK_ADDR16; }
"addr32"           { return token::TOK_ADDR32; }
"aaa"              { return token::TOK_AAA; }
"aad"              { return token::TOK_AAD; }
"aam"              { return token::TOK_AAM; }
"aas"              { return token::TOK_AAS; }
"adc"              { return token::TOK_ADC; }
"adcb"             { return token::TOK_ADCB; }
"adcw"             { return token::TOK_ADCW; }
"adcl"             { return token::TOK_ADCL; }
"add"              { return token::TOK_ADD; }
"addb"             { return token::TOK_ADDB; }
"addw"             { return token::TOK_ADDW; }
"addl"             { return token::TOK_ADDL; }
"addpd"            { return token::TOK_ADDPD; }
"addps"            { return token::TOK_ADDPS; }
"addsd"            { return token::TOK_ADDSD; }
"addss"            { return token::TOK_ADDSS; }
"addsubpd"         { return token::TOK_ADDSUBPD; }
"addsubps"         { return token::TOK_ADDSUBPS; }
"aesdec"           { return token::TOK_AESDEC; }
"aesdeclast"       { return token::TOK_AESDECLAST; }
"aesenc"           { return token::TOK_AESENC; }
"aesenclast"       { return token::TOK_AESENCLAST; }
"aesimc"           { return token::TOK_AESIMC; }
"aeskeygenassist"  { return token::TOK_AESKEYGENASSIST; }
"and"              { return token::TOK_AND; }
"andb"             { return token::TOK_ANDB; }
"andw"             { return token::TOK_ANDW; }
"andl"             { return token::TOK_ANDL; }
"andpd"            { return token::TOK_ANDPD; }
"andps"            { return token::TOK_ANDPS; }
"andnpd"           { return token::TOK_ANDNPD; }
"andnps"           { return token::TOK_ANDNPS; }
"arpl"             { return token::TOK_ARPL; }
"blendpd"          { return token::TOK_BLENDPD; }
"blendps"          { return token::TOK_BLENDPS; }
"blendvpd"         { return token::TOK_BLENDVPD; }
"blendvps"         { return token::TOK_BLENDVPS; }
"bound"            { return token::TOK_BOUND; }
"bsf"              { return token::TOK_BSF; }
"bsr"              { return token::TOK_BSR; }
"bswap"            { return token::TOK_BSWAP; }
"bt"               { return token::TOK_BT; }
"btc"              { return token::TOK_BTC; }
"btr"              { return token::TOK_BTR; }
"bts"              { return token::TOK_BTS; }
"btw"               { return token::TOK_BTW; }
"btcw"              { return token::TOK_BTCW; }
"btrw"              { return token::TOK_BTRW; }
"btsw"              { return token::TOK_BTSW; }
"btl"               { return token::TOK_BTL; }
"btcl"              { return token::TOK_BTCL; }
"btrl"              { return token::TOK_BTRL; }
"btsl"              { return token::TOK_BTSL; }
"call"             { return token::TOK_CALL; }
"cbw"              { return token::TOK_CBW; }
"cbtw"             { return token::TOK_CBTW; }
"cwtl"             { return token::TOK_CWDE; }
"cdqe"             { return token::TOK_CDQE; }
"clc"              { return token::TOK_CLC; }
"cld"              { return token::TOK_CLD; }
"clflush"          { return token::TOK_CLFLUSH; }
"cli"              { return token::TOK_CLI; }
"clts"             { return token::TOK_CLTS; }
"cmc"              { return token::TOK_CMC; }
"cmova"            { return token::TOK_CMOVA; }
"cmovae"           { return token::TOK_CMOVAE; }
"cmovb"            { return token::TOK_CMOVB; }
"cmovbe"           { return token::TOK_CMOVBE; }
"cmovc"            { return token::TOK_CMOVC; }
"cmove"            { return token::TOK_CMOVE; }
"cmovg"            { return token::TOK_CMOVG; }
"cmovge"           { return token::TOK_CMOVGE; }
"cmovl"            { return token::TOK_CMOVL; }
"cmovle"           { return token::TOK_CMOVLE; }
"cmovna"           { return token::TOK_CMOVNA; }
"cmovnae"          { return token::TOK_CMOVNAE; }
"cmovnb"           { return token::TOK_CMOVNB; }
"cmovnbe"          { return token::TOK_CMOVNBE; }
"cmovnc"           { return token::TOK_CMOVNC; }
"cmovne"           { return token::TOK_CMOVNE; }
"cmovng"           { return token::TOK_CMOVNG; }
"cmovnge"          { return token::TOK_CMOVNGE; }
"cmovnl"           { return token::TOK_CMOVNL; }
"cmovnle"          { return token::TOK_CMOVNLE; }
"cmovno"           { return token::TOK_CMOVNO; }
"cmovnp"           { return token::TOK_CMOVNP; }
"cmovns"           { return token::TOK_CMOVNS; }
"cmovnz"           { return token::TOK_CMOVNZ; }
"cmovo"            { return token::TOK_CMOVO; }
"cmovp"            { return token::TOK_CMOVP; }
"cmovpe"           { return token::TOK_CMOVPE; }
"cmovpo"           { return token::TOK_CMOVPO; }
"cmovs"            { return token::TOK_CMOVS; }
"cmovz"            { return token::TOK_CMOVZ; }
"cmp"              { return token::TOK_CMP; }
"cmpb"             { return token::TOK_CMPB; }
"cmpl"             { return token::TOK_CMPL; }
"cmpw"             { return token::TOK_CMPW; }
"cmppd"            { return token::TOK_CMPPD; }
"cmpps"            { return token::TOK_CMPPS; }
"cmpsb"            { return token::TOK_CMPSB; }
"cmpsw"            { return token::TOK_CMPSW; }
"cmpsd"            { return token::TOK_CMPSD; }
"cmpsl"            { return token::TOK_CMPSD; }
"cmpsq"            { return token::TOK_CMPSQ; }
"cmpss"            { return token::TOK_CMPSS; }
"cmpxchg"          { return token::TOK_CMPXCHG; }
"cmpxchg8b"        { return token::TOK_CMPXCHG8B; }
"cmpxchg16b"       { return token::TOK_CMPXCHG16B; }
"comisd"           { return token::TOK_COMISD; }
"comiss"           { return token::TOK_COMISS; }
"cpuid"            { return token::TOK_CPUID; }
"crc32"            { return token::TOK_CRC32; }
"cvtdq2pd"         { return token::TOK_CVTDQ2PD; }
"cvtdq2ps"         { return token::TOK_CVTDQ2PS; }
"cvtpd2dq"         { return token::TOK_CVTPD2DQ; }
"cvtpd2pi"         { return token::TOK_CVTPD2PI; }
"cvtpd2ps"         { return token::TOK_CVTPD2PS; }
"cvtpi2pd"         { return token::TOK_CVTPI2PD; }
"cvtpi2ps"         { return token::TOK_CVTPI2PS; }
"cvtps2dq"         { return token::TOK_CVTPS2DQ; }
"cvtps2pd"         { return token::TOK_CVTPS2PD; }
"cvtps2pi"         { return token::TOK_CVTPS2PI; }
"cvtsd2si"         { return token::TOK_CVTSD2SI; }
"cvtsd2ss"         { return token::TOK_CVTSD2SS; }
"cvtsi2sd"         { return token::TOK_CVTSI2SD; }
"cvtsi2ss"         { return token::TOK_CVTSI2SS; }
"cvtss2sd"         { return token::TOK_CVTSS2SD; }
"cvtss2si"         { return token::TOK_CVTSS2SI; }
"cvttpd2dq"        { return token::TOK_CVTTPD2DQ; }
"cvttpd2pi"        { return token::TOK_CVTTPD2PI; }
"cvttps2dq"        { return token::TOK_CVTTPS2DQ; }
"cvttps2pi"        { return token::TOK_CVTTPS2PI; }
"cvttsd2si"        { return token::TOK_CVTTSD2SI; }
"cvttss2si"        { return token::TOK_CVTTSS2SI; }

"cwd"              { return token::TOK_CWD; }
"cwtd"             { return token::TOK_CWD; }

"cdq"              { return token::TOK_CDQ; }
"cltd"             { return token::TOK_CDQ; }

"cqo"              { return token::TOK_CQO; }
"daa"              { return token::TOK_DAA; }
"das"              { return token::TOK_DAS; }
"dec"              { return token::TOK_DEC; }
"decb"             { return token::TOK_DECB; }
"decw"             { return token::TOK_DECW; }
"decl"             { return token::TOK_DECL; }
"div"              { return token::TOK_DIV; }
"divb"             { return token::TOK_DIVB; }
"divl"             { return token::TOK_DIVL; }
"divw"             { return token::TOK_DIVW; }
"divpd"            { return token::TOK_DIVPD; }
"divps"            { return token::TOK_DIVPS; }
"divsd"            { return token::TOK_DIVSD; }
"divss"            { return token::TOK_DIVSS; }
"dppd"             { return token::TOK_DPPD; }
"dpps"             { return token::TOK_DPPS; }
"emms"             { return token::TOK_EMMS; }
"enter"            { return token::TOK_ENTER; }
"extractps"        { return token::TOK_EXTRACTPS; }
"f2xm1"            { return token::TOK_F2XM1; }
"fabs"             { return token::TOK_FABS; }
"fadd"             { return token::TOK_FADD; }
"faddb"            { return token::TOK_FADDB; }
"faddw"            { return token::TOK_FADDW; }
"faddl"            { return token::TOK_FADDL; }
"fadds"            { return token::TOK_FADDS; }
"faddp"            { return token::TOK_FADDP; }
"fiadd"            { return token::TOK_FIADD; }
"fbld"             { return token::TOK_FBLD; }
"fbstp"            { return token::TOK_FBSTP; }
"fchs"             { return token::TOK_FCHS; }
"fclex"            { return token::TOK_FCLEX; }
"fnclex"           { return token::TOK_FNCLEX; }
"fcmovb"           { return token::TOK_FCMOVB; }
"fcmove"           { return token::TOK_FCMOVE; }
"fcmovbe"          { return token::TOK_FCMOVBE; }
"fcmovu"           { return token::TOK_FCMOVU; }
"fcmovnb"          { return token::TOK_FCMOVNB; }
"fcmovne"          { return token::TOK_FCMOVNE; }
"fcmovnbe"         { return token::TOK_FCMOVNBE; }
"fcmovnu"          { return token::TOK_FCMOVNU; }
"fcom"             { return token::TOK_FCOM; }
"fcomp"            { return token::TOK_FCOMP; }
"fcompp"           { return token::TOK_FCOMPP; }
"fcomi"            { return token::TOK_FCOMI; }
"fcomip"           { return token::TOK_FCOMIP; }
"fucomi"           { return token::TOK_FUCOMI; }
"fucomip"          { return token::TOK_FUCOMIP; }
"fcos"             { return token::TOK_FCOS; }
"fdecstp"          { return token::TOK_FDECSTP; }
"fdiv"             { return token::TOK_FDIV; }
"fdivb"            { return token::TOK_FDIVB; }
"fdivw"            { return token::TOK_FDIVW; }
"fdivl"            { return token::TOK_FDIVL; }
"fdivs"            { return token::TOK_FDIVS; }
"fdivp"            { return token::TOK_FDIVP; }
"fidiv"            { return token::TOK_FIDIV; }
"fdivr"            { return token::TOK_FDIVR; }
"fdivrl"           { return token::TOK_FDIVRL; }
"fdivrs"           { return token::TOK_FDIVRS; }
"fdivrp"           { return token::TOK_FDIVRP; }
"fidivr"           { return token::TOK_FIDIVR; }
"ffree"            { return token::TOK_FFREE; }
"ficom"            { return token::TOK_FICOM; }
"ficomp"           { return token::TOK_FICOMP; }
"fild"             { return token::TOK_FILD; }
"fildl"            { return token::TOK_FILDl; }
"fildll"           { return token::TOK_FILDLL; }
"fincstp"          { return token::TOK_FINCSTP; }
"finit"            { return token::TOK_FINIT; }
"fninit"           { return token::TOK_FNINIT; }
"fist"             { return token::TOK_FIST; }
"fistl"            { return token::TOK_FISTL; }
"fistp"            { return token::TOK_FISTP; }
"fistpl"           { return token::TOK_FISTPL; }
"fistpll"          { return token::TOK_FISTPLL; }
"fisttp"           { return token::TOK_FISTTP; }
"fld"              { return token::TOK_FLD; }
"fldl"             { return token::TOK_FLDL; }
"fldt"             { return token::TOK_FLDT; }
"flds"             { return token::TOK_FLDS; }
"fld1"             { return token::TOK_FLD1; }
"fldl2t"           { return token::TOK_FLDL2T; }
"fldl2e"           { return token::TOK_FLDL2E; }
"fldpi"            { return token::TOK_FLDPI; }
"fldlg2"           { return token::TOK_FLDLG2; }
"fldln2"           { return token::TOK_FLDLN2; }
"fldz"             { return token::TOK_FLDZ; }
"fldcw"            { return token::TOK_FLDCW; }
"fldenv"           { return token::TOK_FLDENV; }
"fmul"             { return token::TOK_FMUL; }
"fmull"            { return token::TOK_FMULL; }
"fmuls"            { return token::TOK_FMULS; }
"fmulp"            { return token::TOK_FMULP; }
"fimul"            { return token::TOK_FIMUL; }
"fnop"             { return token::TOK_FNOP; }
"fpatan"           { return token::TOK_FPATAN; }
"fprem"            { return token::TOK_FPREM; }
"fprem1"           { return token::TOK_FPREM1; }
"fptan"            { return token::TOK_FPTAN; }
"frndint"          { return token::TOK_FRNDINT; }
"frstor"           { return token::TOK_FRSTOR; }
"fsave"            { return token::TOK_FSAVE; }
"fnsave"           { return token::TOK_FNSAVE; }
"fscale"           { return token::TOK_FSCALE; }
"fsin"             { return token::TOK_FSIN; }
"fsincos"          { return token::TOK_FSINCOS; }
"fsqrt"            { return token::TOK_FSQRT; }
"fst"              { return token::TOK_FST; }
"fsts"             { return token::TOK_FSTS; }
"fstb"             { return token::TOK_FSTB; }
"fstw"             { return token::TOK_FSTW; }
"fstl"             { return token::TOK_FSTL; }
"fstp"             { return token::TOK_FSTP; }
"fstps"            { return token::TOK_FSTPS; }
"fstpt"            { return token::TOK_FSTPT; }
"fstpl"            { return token::TOK_FSTPL; }
"fstcw"            { return token::TOK_FSTCW; }
"fnstcw"           { return token::TOK_FNSTCW; }
"fstenv"           { return token::TOK_FSTENV; }
"fnstenv"          { return token::TOK_FNSTENV; }
"fstsw"            { return token::TOK_FSTSW; }
"fnstsw"           { return token::TOK_FNSTSW; }
"fsub"             { return token::TOK_FSUB; }
"fsubb"            { return token::TOK_FSUBB; }
"fsubw"            { return token::TOK_FSUBW; }
"fsubl"            { return token::TOK_FSUBL; }
"fsubs"            { return token::TOK_FSUBS; }
"fsubp"            { return token::TOK_FSUBP; }
"fisub"            { return token::TOK_FISUB; }
"fsubr"            { return token::TOK_FSUBR; }
"fsubrp"           { return token::TOK_FSUBRP; }
"fisubr"           { return token::TOK_FISUBR; }
"ftst"             { return token::TOK_FTST; }
"fucom"            { return token::TOK_FUCOM; }
"fucomp"           { return token::TOK_FUCOMP; }
"fucompp"          { return token::TOK_FUCOMPP; }
"fxam"             { return token::TOK_FXAM; }
"fxch"             { return token::TOK_FXCH; }
"fxrstor"          { return token::TOK_FXRSTOR; }
"fxsave"           { return token::TOK_FXSAVE; }
"fxtract"          { return token::TOK_FXTRACT; }
"fyl2x"            { return token::TOK_FYL2X; }
"fyl2xp1"          { return token::TOK_FYL2XP1; }
"haddpd"           { return token::TOK_HADDPD; }
"haddps"           { return token::TOK_HADDPS; }
"hlt"              { return token::TOK_HLT; }
"hsubpd"           { return token::TOK_HSUBPD; }
"hsubps"           { return token::TOK_HSUBPS; }
"idiv"             { return token::TOK_IDIV; }
"idivb"            { return token::TOK_IDIVB; }
"idivw"            { return token::TOK_IDIVW; }
"idivl"            { return token::TOK_IDIVL; }
"imul"             { return token::TOK_IMUL; }
"imulb"            { return token::TOK_IMULB; }
"imulw"            { return token::TOK_IMULW; }
"imull"            { return token::TOK_IMULL; }
"in"               { return token::TOK_IN; }
"inc"              { return token::TOK_INC; }
"incb"             { return token::TOK_INCB; }
"incw"             { return token::TOK_INCW; }
"incl"             { return token::TOK_INCL; }
"insb"             { return token::TOK_INSB; }
"insw"             { return token::TOK_INSW; }
"insl"             { return token::TOK_INSL; }
"insd"             { return token::TOK_INSD; }
"insertps"         { return token::TOK_INSERTPS; }
"int"              { return token::TOK_INT; }
"into"             { return token::TOK_INTO; }
"int3"             { return token::TOK_INT3; }
"invd"             { return token::TOK_INVD; }
"invlpg"           { return token::TOK_INVLPG; }
"iret"             { return token::TOK_IRET; }
"iretd"            { return token::TOK_IRETD; }
"iretq"            { return token::TOK_IRETQ; }
"ja"               { return token::TOK_JA; }
"jae"              { return token::TOK_JAE; }
"jb"               { return token::TOK_JB; }
"jbe"              { return token::TOK_JBE; }
"jc"               { return token::TOK_JC; }
"jcxz"             { return token::TOK_JCXZ; }
"jecxz"            { return token::TOK_JECXZ; }
"jrcxz"            { return token::TOK_JRCXZ; }
"je"               { return token::TOK_JE; }
"jg"               { return token::TOK_JG; }
"jge"              { return token::TOK_JGE; }
"jl"               { return token::TOK_JL; }
"jle"              { return token::TOK_JLE; }
"jna"              { return token::TOK_JNA; }
"jnae"             { return token::TOK_JNAE; }
"jnb"              { return token::TOK_JNB; }
"jnbe"             { return token::TOK_JNBE; }
"jnc"              { return token::TOK_JNC; }
"jne"              { return token::TOK_JNE; }
"jng"              { return token::TOK_JNG; }
"jnge"             { return token::TOK_JNGE; }
"jnl"              { return token::TOK_JNL; }
"jnle"             { return token::TOK_JNLE; }
"jno"              { return token::TOK_JNO; }
"jnp"              { return token::TOK_JNP; }
"jns"              { return token::TOK_JNS; }
"jnz"              { return token::TOK_JNZ; }
"jo"               { return token::TOK_JO; }
"jp"               { return token::TOK_JP; }
"jpe"              { return token::TOK_JPE; }
"jpo"              { return token::TOK_JPO; }
"js"               { return token::TOK_JS; }
"jz"               { return token::TOK_JZ; }
"jmp"              { return token::TOK_JMP; }
"jmpw"             { return token::TOK_JMPW; }
"lahf"             { return token::TOK_LAHF; }
"lar"              { return token::TOK_LAR; }
"lddqu"            { return token::TOK_LDDQU; }
"ldmxcsr"          { return token::TOK_LDMXCSR; }
"lds"              { return token::TOK_LDS; }
"les"              { return token::TOK_LES; }
"lfs"              { return token::TOK_LFS; }
"lgs"              { return token::TOK_LGS; }
"lss"              { return token::TOK_LSS; }
"lea"              { return token::TOK_LEA; }
"leave"            { return token::TOK_LEAVE; }
"lfence"           { return token::TOK_LFENCE; }
"lgdt"             { return token::TOK_LGDT; }
"lidt"             { return token::TOK_LIDT; }
"lldt"             { return token::TOK_LLDT; }
"lmsw"             { return token::TOK_LMSW; }
"lock"             { return token::TOK_LOCK; }
"lods"             { return token::TOK_LODS; }
"lodsb"            { return token::TOK_LODSB; }
"lodsw"            { return token::TOK_LODSW; }
"lodsd"            { return token::TOK_LODSD; }
"lodsq"            { return token::TOK_LODSQ; }
"loop"             { return token::TOK_LOOP; }
"loope"            { return token::TOK_LOOPE; }
"loopne"           { return token::TOK_LOOPNE; }
"lsl"              { return token::TOK_LSL; }
"ltr"              { return token::TOK_LTR; }
"maskmovdqu"       { return token::TOK_MASKMOVDQU; }
"maskmovq"         { return token::TOK_MASKMOVQ; }
"maxpd"            { return token::TOK_MAXPD; }
"maxps"            { return token::TOK_MAXPS; }
"maxsd"            { return token::TOK_MAXSD; }
"maxss"            { return token::TOK_MAXSS; }
"mfence"           { return token::TOK_MFENCE; }
"minpd"            { return token::TOK_MINPD; }
"minps"            { return token::TOK_MINPS; }
"minsd"            { return token::TOK_MINSD; }
"minss"            { return token::TOK_MINSS; }
"monitor"          { return token::TOK_MONITOR; }
"mov"              { return token::TOK_MOV; }
"movb"             { return token::TOK_MOVB; }
"movw"             { return token::TOK_MOVW; }
"movl"             { return token::TOK_MOVL; }
"movapd"           { return token::TOK_MOVAPD; }
"movaps"           { return token::TOK_MOVAPS; }
"movbe"            { return token::TOK_MOVBE; }
"movd"             { return token::TOK_MOVD; }
"movq"             { return token::TOK_MOVQ; }
"movddup"          { return token::TOK_MOVDDUP; }
"movdqa"           { return token::TOK_MOVDQA; }
"movdqu"           { return token::TOK_MOVDQU; }
"movdq2q"          { return token::TOK_MOVDQ2Q; }
"movhlps"          { return token::TOK_MOVHLPS; }
"movhpd"           { return token::TOK_MOVHPD; }
"movhps"           { return token::TOK_MOVHPS; }
"movlhps"          { return token::TOK_MOVLHPS; }
"movlpd"           { return token::TOK_MOVLPD; }
"movlps"           { return token::TOK_MOVLPS; }
"movmskpd"         { return token::TOK_MOVMSKPD; }
"movmskps"         { return token::TOK_MOVMSKPS; }
"movntdqa"         { return token::TOK_MOVNTDQA; }
"movntdq"          { return token::TOK_MOVNTDQ; }
"movnti"           { return token::TOK_MOVNTI; }
"movntpd"          { return token::TOK_MOVNTPD; }
"movntps"          { return token::TOK_MOVNTPS; }
"movntq"           { return token::TOK_MOVNTQ; }
"movq2dq"          { return token::TOK_MOVQ2DQ; }
"movsb"            { return token::TOK_MOVSB; }
"movsbw"           { return token::TOK_MOVSBW; }
"movsbl"           { return token::TOK_MOVSBL; }
"movsw"            { return token::TOK_MOVSW; }
"movswl"           { return token::TOK_MOVSWL; }
"movsl"            { return token::TOK_MOVSL; }
"movsd"            { return token::TOK_MOVSD; }
"movsq"            { return token::TOK_MOVSQ; }
"movshdup"         { return token::TOK_MOVSHDUP; }
"movsldup"         { return token::TOK_MOVSLDUP; }
"movss"            { return token::TOK_MOVSS; }
"movsx"            { return token::TOK_MOVSX; }
"movsxd"           { return token::TOK_MOVSXD; }
"movupd"           { return token::TOK_MOVUPD; }
"movups"           { return token::TOK_MOVUPS; }
"movzx"            { return token::TOK_MOVZX; }
"movzbl"           { return token::TOK_MOVZBL; }
"movzwl"           { return token::TOK_MOVZWL; }
"mpsadbw"          { return token::TOK_MPSADBW; }
"mul"              { return token::TOK_MUL; }
"mulb"             { return token::TOK_MULB; }
"mulw"             { return token::TOK_MULW; }
"mull"             { return token::TOK_MULL; }
"mulpd"            { return token::TOK_MULPD; }
"mulps"            { return token::TOK_MULPS; }
"mulsd"            { return token::TOK_MULSD; }
"mulss"            { return token::TOK_MULSS; }
"mwait"            { return token::TOK_MWAIT; }
"neg"              { return token::TOK_NEG; }
"negb"             { return token::TOK_NEGB; }
"negw"             { return token::TOK_NEGW; }
"negl"             { return token::TOK_NEGL; }
"nop"              { return token::TOK_NOP; }
"nopb"             { return token::TOK_NOPB; }
"nopw"             { return token::TOK_NOPW; }
"nopl"             { return token::TOK_NOPL; }
"not"              { return token::TOK_NOT; }
"notb"             { return token::TOK_NOTB; }
"notw"             { return token::TOK_NOTW; }
"notl"             { return token::TOK_NOTL; }
"or"               { return token::TOK_OR; }
"orb"              { return token::TOK_ORB; }
"orw"              { return token::TOK_ORW; }
"orl"              { return token::TOK_ORL; }
"orpd"             { return token::TOK_ORPD; }
"orps"             { return token::TOK_ORPS; }
"out"              { return token::TOK_OUT; }
"outsb"            { return token::TOK_OUTSB; }
"outsw"            { return token::TOK_OUTSW; }
"outsl"            { return token::TOK_OUTSL; }
"outsd"            { return token::TOK_OUTSD; }
"pabsb"            { return token::TOK_PABSB; }
"pabsw"            { return token::TOK_PABSW; }
"pabsd"            { return token::TOK_PABSD; }
"packsswb"         { return token::TOK_PACKSSWB; }
"packssdw"         { return token::TOK_PACKSSDW; }
"packusdw"         { return token::TOK_PACKUSDW; }
"packuswb"         { return token::TOK_PACKUSWB; }
"paddb"            { return token::TOK_PADDB; }
"paddw"            { return token::TOK_PADDW; }
"paddd"            { return token::TOK_PADDD; }
"paddq"            { return token::TOK_PADDQ; }
"paddsb"           { return token::TOK_PADDSB; }
"paddsw"           { return token::TOK_PADDSW; }
"paddusb"          { return token::TOK_PADDUSB; }
"paddusw"          { return token::TOK_PADDUSW; }
"palignr"          { return token::TOK_PALIGNR; }
"pand"             { return token::TOK_PAND; }
"pandn"            { return token::TOK_PANDN; }
"pause"            { return token::TOK_PAUSE; }
"pavgb"            { return token::TOK_PAVGB; }
"pavgw"            { return token::TOK_PAVGW; }
"pblendvb"         { return token::TOK_PBLENDVB; }
"pblendw"          { return token::TOK_PBLENDW; }
"pclmulqdq"        { return token::TOK_PCLMULQDQ; }
"pcmpeqb"          { return token::TOK_PCMPEQB; }
"pcmpeqw"          { return token::TOK_PCMPEQW; }
"pcmpeqd"          { return token::TOK_PCMPEQD; }
"pcmpeqq"          { return token::TOK_PCMPEQQ; }
"pcmpestri"        { return token::TOK_PCMPESTRI; }
"pcmpestrm"        { return token::TOK_PCMPESTRM; }
"pcmpgtb"          { return token::TOK_PCMPGTB; }
"pcmpgtw"          { return token::TOK_PCMPGTW; }
"pcmpgtd"          { return token::TOK_PCMPGTD; }
"pcmpgtq"          { return token::TOK_PCMPGTQ; }
"pcmpistri"        { return token::TOK_PCMPISTRI; }
"pcmpistrm"        { return token::TOK_PCMPISTRM; }
"pextrb"           { return token::TOK_PEXTRB; }
"pextrd"           { return token::TOK_PEXTRD; }
"pextrq"           { return token::TOK_PEXTRQ; }
"pextrw"           { return token::TOK_PEXTRW; }
"phaddw"           { return token::TOK_PHADDW; }
"phaddd"           { return token::TOK_PHADDD; }
"phaddsw"          { return token::TOK_PHADDSW; }
"phminposuw"       { return token::TOK_PHMINPOSUW; }
"phsubw"           { return token::TOK_PHSUBW; }
"phsubd"           { return token::TOK_PHSUBD; }
"phsubsw"          { return token::TOK_PHSUBSW; }
"pinsrb"           { return token::TOK_PINSRB; }
"pinsrd"           { return token::TOK_PINSRD; }
"pinsrq"           { return token::TOK_PINSRQ; }
"pinsrw"           { return token::TOK_PINSRW; }
"pmaddubsw"        { return token::TOK_PMADDUBSW; }
"pmaddwd"          { return token::TOK_PMADDWD; }
"pmaxsb"           { return token::TOK_PMAXSB; }
"pmaxsd"           { return token::TOK_PMAXSD; }
"pmaxsw"           { return token::TOK_PMAXSW; }
"pmaxub"           { return token::TOK_PMAXUB; }
"pmaxud"           { return token::TOK_PMAXUD; }
"pmaxuw"           { return token::TOK_PMAXUW; }
"pminsb"           { return token::TOK_PMINSB; }
"pminsd"           { return token::TOK_PMINSD; }
"pminsw"           { return token::TOK_PMINSW; }
"pminub"           { return token::TOK_PMINUB; }
"pminud"           { return token::TOK_PMINUD; }
"pminuw"           { return token::TOK_PMINUW; }
"pmovmskb"         { return token::TOK_PMOVMSKB; }
"pmovsx"           { return token::TOK_PMOVSX; }
"pmovzx"           { return token::TOK_PMOVZX; }
"pmuldq"           { return token::TOK_PMULDQ; }
"pmulhrsw"         { return token::TOK_PMULHRSW; }
"pmulhuw"          { return token::TOK_PMULHUW; }
"pmulhw"           { return token::TOK_PMULHW; }
"pmulld"           { return token::TOK_PMULLD; }
"pmullw"           { return token::TOK_PMULLW; }
"pmuludq"          { return token::TOK_PMULUDQ; }
"pop"              { return token::TOK_POP; }
"popw"             { return token::TOK_POPW; }
"popl"             { return token::TOK_POPL; }
"popa"             { return token::TOK_POPA; }
"popaw"            { return token::TOK_POPAW; }
"popal"            { return token::TOK_POPAL; }
"popad"            { return token::TOK_POPAD; }
"popcnt"           { return token::TOK_POPCNT; }
"popf"             { return token::TOK_POPF; }
"popfd"            { return token::TOK_POPFD; }
"popfq"            { return token::TOK_POPFQ; }
"por"              { return token::TOK_POR; }
"prefetcht0"       { return token::TOK_PREFETCHT0; }
"prefetcht1"       { return token::TOK_PREFETCHT1; }
"prefetcht2"       { return token::TOK_PREFETCHT2; }
"prefetchnta"      { return token::TOK_PREFETCHNTA; }
"psadbw"           { return token::TOK_PSADBW; }
"pshufb"           { return token::TOK_PSHUFB; }
"pshufd"           { return token::TOK_PSHUFD; }
"pshufhw"          { return token::TOK_PSHUFHW; }
"pshuflw"          { return token::TOK_PSHUFLW; }
"pshufw"           { return token::TOK_PSHUFW; }
"psignb"           { return token::TOK_PSIGNB; }
"psignw"           { return token::TOK_PSIGNW; }
"psignd"           { return token::TOK_PSIGND; }
"pslldq"           { return token::TOK_PSLLDQ; }
"psllw"            { return token::TOK_PSLLW; }
"pslld"            { return token::TOK_PSLLD; }
"psllq"            { return token::TOK_PSLLQ; }
"psraw"            { return token::TOK_PSRAW; }
"psrad"            { return token::TOK_PSRAD; }
"psrldq"           { return token::TOK_PSRLDQ; }
"psrlw"            { return token::TOK_PSRLW; }
"psrld"            { return token::TOK_PSRLD; }
"psrlq"            { return token::TOK_PSRLQ; }
"psubb"            { return token::TOK_PSUBB; }
"psubw"            { return token::TOK_PSUBW; }
"psubd"            { return token::TOK_PSUBD; }
"psubq"            { return token::TOK_PSUBQ; }
"psubsb"           { return token::TOK_PSUBSB; }
"psubsw"           { return token::TOK_PSUBSW; }
"psubusb"          { return token::TOK_PSUBUSB; }
"psubusw"          { return token::TOK_PSUBUSW; }
"ptest"            { return token::TOK_PTEST; }
"punpckhbw"        { return token::TOK_PUNPCKHBW; }
"punpckhwd"        { return token::TOK_PUNPCKHWD; }
"punpckhdq"        { return token::TOK_PUNPCKHDQ; }
"punpckhqdq"       { return token::TOK_PUNPCKHQDQ; }
"punpcklbw"        { return token::TOK_PUNPCKLBW; }
"punpcklwd"        { return token::TOK_PUNPCKLWD; }
"punpckldq"        { return token::TOK_PUNPCKLDQ; }
"punpcklqdq"       { return token::TOK_PUNPCKLQDQ; }
"push"             { return token::TOK_PUSH; }
"pushw"            { return token::TOK_PUSHW; }
"pushl"            { return token::TOK_PUSHL; }
"pusha"            { return token::TOK_PUSHA; }
"pushad"           { return token::TOK_PUSHAD; }
"pushf"            { return token::TOK_PUSHF; }
"pushfd"           { return token::TOK_PUSHFD; }
"pxor"             { return token::TOK_PXOR; }
"rcl"              { return token::TOK_RCL; }
"rclb"             { return token::TOK_RCLB; }
"rclw"             { return token::TOK_RCLW; }
"rcll"             { return token::TOK_RCLL; }
"rcr"              { return token::TOK_RCR; }
"rcrb"             { return token::TOK_RCRB; }
"rcrw"             { return token::TOK_RCRW; }
"rcrl"             { return token::TOK_RCRL; }
"rol"              { return token::TOK_ROL; }
"rolb"             { return token::TOK_ROLB; }
"rolw"             { return token::TOK_ROLW; }
"roll"             { return token::TOK_ROLL; }
"ror"              { return token::TOK_ROR; }
"rorb"             { return token::TOK_RORB; }
"rorw"             { return token::TOK_RORW; }
"rorl"             { return token::TOK_RORL; }
"rcpps"            { return token::TOK_RCPPS; }
"rcpss"            { return token::TOK_RCPSS; }
"rdmsr"            { return token::TOK_RDMSR; }
"rdpmc"            { return token::TOK_RDPMC; }
"rdrand"           { return token::TOK_RDRAND; }
"rdtsc"            { return token::TOK_RDTSC; }
"rdtscp"           { return token::TOK_RDTSCP; }
"rep"              { return token::TOK_REP; }
"repe"             { return token::TOK_REPE; }
"repz"             { return token::TOK_REPZ; }
"repne"            { return token::TOK_REPNE; }
"repnz"            { return token::TOK_REPNZ; }
"ret"              { return token::TOK_RET; }
"roundpd"          { return token::TOK_ROUNDPD; }
"roundps"          { return token::TOK_ROUNDPS; }
"roundsd"          { return token::TOK_ROUNDSD; }
"roundss"          { return token::TOK_ROUNDSS; }
"rsm"              { return token::TOK_RSM; }
"rsqrtps"          { return token::TOK_RSQRTPS; }
"rsqrtss"          { return token::TOK_RSQRTSS; }
"sahf"             { return token::TOK_SAHF; }
"sal"              { return token::TOK_SAL; }
"salb"             { return token::TOK_SALB; }
"salw"             { return token::TOK_SALW; }
"sall"             { return token::TOK_SALL; }
"sar"              { return token::TOK_SAR; }
"sarb"             { return token::TOK_SARB; }
"sarw"             { return token::TOK_SARW; }
"sarl"             { return token::TOK_SARL; }
"shl"              { return token::TOK_SHL; }
"shlb"             { return token::TOK_SHLB; }
"shlw"             { return token::TOK_SHLW; }
"shll"             { return token::TOK_SHLL; }
"shr"              { return token::TOK_SHR; }
"shrb"             { return token::TOK_SHRB; }
"shrw"             { return token::TOK_SHRW; }
"shrl"             { return token::TOK_SHRL; }
"sbb"              { return token::TOK_SBB; }
"sbbb"             { return token::TOK_SBBB; }
"sbbw"             { return token::TOK_SBBW; }
"sbbl"             { return token::TOK_SBBL; }
"scas"             { return token::TOK_SCAS; }
"scasb"            { return token::TOK_SCASB; }
"scasw"            { return token::TOK_SCASW; }
"scasd"            { return token::TOK_SCASD; }
"seta"             { return token::TOK_SETA; }
"setae"            { return token::TOK_SETAE; }
"setb"             { return token::TOK_SETB; }
"setbe"            { return token::TOK_SETBE; }
"setc"             { return token::TOK_SETC; }
"sete"             { return token::TOK_SETE; }
"setg"             { return token::TOK_SETG; }
"setge"            { return token::TOK_SETGE; }
"setl"             { return token::TOK_SETL; }
"setle"            { return token::TOK_SETLE; }
"setna"            { return token::TOK_SETNA; }
"setnae"           { return token::TOK_SETNAE; }
"setnb"            { return token::TOK_SETNB; }
"setnbe"           { return token::TOK_SETNBE; }
"setnc"            { return token::TOK_SETNC; }
"setne"            { return token::TOK_SETNE; }
"setng"            { return token::TOK_SETNG; }
"setnge"           { return token::TOK_SETNGE; }
"setnl"            { return token::TOK_SETNL; }
"setnle"           { return token::TOK_SETNLE; }
"setno"            { return token::TOK_SETNO; }
"setnp"            { return token::TOK_SETNP; }
"setns"            { return token::TOK_SETNS; }
"setnz"            { return token::TOK_SETNZ; }
"seto"             { return token::TOK_SETO; }
"setp"             { return token::TOK_SETP; }
"setpe"            { return token::TOK_SETPE; }
"setpo"            { return token::TOK_SETPO; }
"sets"             { return token::TOK_SETS; }
"setz"             { return token::TOK_SETZ; }
"sfence"           { return token::TOK_SFENCE; }
"sgdt"             { return token::TOK_SGDT; }
"shld"             { return token::TOK_SHLD; }
"shrd"             { return token::TOK_SHRD; }
"shufpd"           { return token::TOK_SHUFPD; }
"shufps"           { return token::TOK_SHUFPS; }
"sidt"             { return token::TOK_SIDT; }
"sldt"             { return token::TOK_SLDT; }
"smsw"             { return token::TOK_SMSW; }
"sqrtpd"           { return token::TOK_SQRTPD; }
"sqrtps"           { return token::TOK_SQRTPS; }
"sqrtsd"           { return token::TOK_SQRTSD; }
"sqrtss"           { return token::TOK_SQRTSS; }
"stc"              { return token::TOK_STC; }
"std"              { return token::TOK_STD; }
"sti"              { return token::TOK_STI; }
"stmxcsr"          { return token::TOK_STMXCSR; }
"stos"             { return token::TOK_STOS; }
"stosb"            { return token::TOK_STOSB; }
"stosw"            { return token::TOK_STOSW; }
"stosd"            { return token::TOK_STOSD; }
"stosq"            { return token::TOK_STOSQ; }
"str"              { return token::TOK_STR; }
"sub"              { return token::TOK_SUB; }
"subb"             { return token::TOK_SUBB; }
"subw"             { return token::TOK_SUBW; }
"subl"             { return token::TOK_SUBL; }
"subpd"            { return token::TOK_SUBPD; }
"subps"            { return token::TOK_SUBPS; }
"subsd"            { return token::TOK_SUBSD; }
"subss"            { return token::TOK_SUBSS; }
"swapgs"           { return token::TOK_SWAPGS; }
"syscall"          { return token::TOK_SYSCALL; }
"sysenter"         { return token::TOK_SYSENTER; }
"sysexit"          { return token::TOK_SYSEXIT; }
"sysret"           { return token::TOK_SYSRET; }
"test"             { return token::TOK_TEST; }
"testb"            { return token::TOK_TESTB; }
"testw"            { return token::TOK_TESTW; }
"testl"            { return token::TOK_TESTL; }
"ucomisd"          { return token::TOK_UCOMISD; }
"ucomiss"          { return token::TOK_UCOMISS; }
"ud2"              { return token::TOK_UD2; }
"unpckhpd"         { return token::TOK_UNPCKHPD; }
"unpckhps"         { return token::TOK_UNPCKHPS; }
"unpcklpd"         { return token::TOK_UNPCKLPD; }
"unpcklps"         { return token::TOK_UNPCKLPS; }
"vbroadcast"       { return token::TOK_VBROADCAST; }
"verr"             { return token::TOK_VERR; }
"verw"             { return token::TOK_VERW; }
"vextractf128"     { return token::TOK_VEXTRACTF128; }
"vmaskmov"         { return token::TOK_VMASKMOV; }
"vinsertf128"      { return token::TOK_VINSERTF128; }
"vpermilpd"        { return token::TOK_VPERMILPD; }
"vpermilps"        { return token::TOK_VPERMILPS; }
"vperm2f128"       { return token::TOK_VPERM2F128; }
"vtestpd"          { return token::TOK_VTESTPD; }
"vtestps"          { return token::TOK_VTESTPS; }
"vzeroall"         { return token::TOK_VZEROALL; }
"vzeroupper"       { return token::TOK_VZEROUPPER; }
"wait"             { return token::TOK_WAIT; }
"fwait"            { return token::TOK_FWAIT; }
"wbinvd"           { return token::TOK_WBINVD; }
"wrmsr"            { return token::TOK_WRMSR; }
"xadd"             { return token::TOK_XADD; }
"xchg"             { return token::TOK_XCHG; }
"xgetbv"           { return token::TOK_XGETBV; }
"xlat"             { return token::TOK_XLAT; }
"xlatb"            { return token::TOK_XLATB; }
"xor"              { return token::TOK_XOR; }
"xorb"             { return token::TOK_XORB; }
"xorw"             { return token::TOK_XORW; }
"xorl"             { return token::TOK_XORL; }
"xorpd"            { return token::TOK_XORPD; }
"xorps"            { return token::TOK_XORPS; }
"xrstor"           { return token::TOK_XRSTOR; }
"xsave"            { return token::TOK_XSAVE; }
"xsaveopt"         { return token::TOK_XSAVEOPT; }
"xsetbv"           { return token::TOK_XSETBV; }

"," { return token::TOK_COMMA;     }
":" { return token::TOK_COLON; }
"(" { return token::TOK_LPAR;      }
")" { return token::TOK_RPAR;      }
"+" { return token::TOK_PLUS;      }
"-" { return token::TOK_MINUS;     }
"*" { return token::TOK_STAR;      }
"$" { return token::TOK_DOLLAR;    }

 /* Spaces and end of lines */
[ \t]+ { yylloc->lines(yyleng); yylloc->step(); }
[\n]+  { yylloc->lines(yyleng); yylloc->step(); return token::TOK_EOL; }

 /* Integer values */
"0x"?{hexvalue} {
                   if (yytext[1] != 'x')
		     yylval->intValue = strtol (yytext, NULL, 10);
		   else
		     {
		       char *s = yytext+2;
		       yylval->intValue = 0;
		       for (; *s; s++)
			 {
			   yylval->intValue *= 16;
			   if ('A' <= *s && *s <= 'F')
			     yylval->intValue += 10 + (*s - 'A');
			   else if ('a' <= *s && *s <= 'f')
			     yylval->intValue += 10 + (*s - 'a');
			   else
			     yylval->intValue += (*s - '0');
			 }
		     }
		   return token::TOK_INTEGER;
                }

 /* Registers */
"%"{varname} {
                yylval->stringValue = new string (yytext + 1);
	        return token::TOK_REGISTER;
             }

 /* Anything else is probable an error */
.  { 
     char tmp[2] = { yytext[0], 0 };
     yylval->stringValue = new string (tmp);
     return token::TOK_INVALID;
   }

%% /***** Lexer subroutines *****/


bool x86_32_scanner_open(const string &instr)
{
  return yy_scan_string (instr.c_str ());
}

void x86_32_scanner_close()
{
  yy_delete_buffer (YY_CURRENT_BUFFER);
}
