#!/bin/sh

INSTRFILE=x86_32_instructions.txt
HH_FILE=x86_32_translation_functions.hh
RULES=x86_32_parser_rules.yy
TOKENS=x86_32_parser_tokens.yy
TOKENTYPE=
LEXRULES=x86_32_lexer_rules.ll

# Cleaning before starting
rm -f ${RULES} ${TOKENS} ${HH_FILE} ${LEXRULES}

CCPS=`tr [:lower:]. [:upper:]_ <<< "${HH_FILE}"`
cat > ${HH_FILE} <<EOF
#ifndef $CCPS
# define $CCPS

# include "x86_32_translate.hh"

EOF

echo "instruction: " > ${RULES}
RULEPREFIX=" "

cat ${INSTRFILE} | while read instline ; do
    INST=`awk '{ print $1 }' <<< "${instline}"`
    NBARGS=`sed "s/${INST} *//g" <<< "${instline}"`
    INITIAL=${INST:0:1}
    CC_FILE="x86_32_${INITIAL}_instr.cc"

    if ! test -f ${CC_FILE}; then
	echo "#include \"${HH_FILE}\"" >> ${CC_FILE}
	echo >> ${CC_FILE}
	echo "using namespace std;" >> ${CC_FILE}
	echo >> ${CC_FILE}
    fi

    for nbargs in ${NBARGS}; do
	if test "$nbargs" = "prefix"; then
	    PROTO=`sed -e "s+\(.*\)$+X86_32_TRANSLATE_PREFIX(\1)+g" <<< "${INST}"`

	    if grep -q "^${PROTO}[^;]*$" *.c; then
		(echo "${PROTO};"; echo) >> ${HH_FILE}
	    else
		(echo "// ${PROTO};"; echo) >> ${HH_FILE}
	    fi

	    (echo "${RULEPREFIX} TOK_${INST} { x86_32_translate<X86_32_TOKEN(${INST})> (data, true); } instruction { x86_32_translate<X86_32_TOKEN(${INST})> (data, false); }") >> ${RULES}
	    RULEPREFIX="|"
	else
	    N=1
	    RARGS=""
	    SEMARGS="data"
	    while test ${N} -le ${nbargs}; do
		if test "x${RARGS}" != "x"; then
		    RARGS="${RARGS} TOK_COMMA "
		fi
		RARGS="${RARGS}operand"
		SEMARGS="${SEMARGS}, \$`expr 2 '*' $N`"
		let N=$N+1
	    done
	    PROTO=`sed -e "s+\(.*\)$+X86_32_TRANSLATE_${nbargs}_OP(\1)+g" <<< "${INST}"`

	    if grep -q "^${PROTO}[^;]*$" *.cc; then
		(echo "${PROTO};"; echo) >> ${HH_FILE}
	    else
		(echo "// ${PROTO};"; echo) >> ${HH_FILE}
	    fi

	    (echo "${RULEPREFIX} TOK_${INST} ${RARGS} { x86_32_translate<X86_32_TOKEN(${INST})> (${SEMARGS}); }") >> ${RULES}
	    RULEPREFIX="|"
	fi
    done
    RULEPREFIX="|"

    echo "%token ${TOKENTYPE} TOK_${INST}*\"${INST}\"" >> ${TOKENS}
    RE=`tr [:upper:] [:lower:] <<< "${INST}"`;
    echo "\"${RE}\"*{ return token::TOK_${INST}; }" >> ${LEXRULES}
done

# Formatting the rules
for file in ${TOKENS} ${LEXRULES}; do
    column -t -s "*" ${file} > ${file}.tmp
    mv -f ${file}.tmp ${file}
done

echo ";" >> ${RULES}
cat >> ${HH_FILE} <<EOF

#endif /* ! $CCPS */
EOF

awk "/@RULES@/ { system(\"cat ${RULES}\"); } /@TOKENS@/ { system(\"cat ${TOKENS}\"); } !(/@RULES@/||/@TOKENS@/) { print; }" x86_32_parser.yy.tmpl > x86_32_parser.yy

awk "/@RULES@/ { system(\"cat ${LEXRULES}\"); } !(/@RULES@/) { print; }" x86_32_scanner.ll.tmpl > x86_32_scanner.ll

# Cleaning temporary files
rm -f ${RULES} ${TOKENS} ${LEXRULES}
