#!/bin/sh

if test "x$1" = "x"; then
    echo "Usage: $0 test-name" 1>&2
    exit 1
fi

TESTNAME="$1"
if test "$(basename ${TESTNAME})" = "check-diff"; 
then
    REFNAME=/dev/null
else
    REFNAME="$(basename $(basename ${TESTNAME} .res) .memres).mc.xml"
fi

exec diff -u "${REFNAME}" "${TESTNAME}"
