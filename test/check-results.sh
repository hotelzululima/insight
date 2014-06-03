#!/bin/sh

if test "x$1" = "x"; then
    echo "Usage: $0 test-name" 1>&2
    exit 1
fi

TESTNAME="$1"
REFNAME="${srcdir}/`basename ${TESTNAME}`.result"

exec diff -u "${REFNAME}" "${TESTNAME}"
