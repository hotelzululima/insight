#!/bin/sh

#
# small to compare addresses visited by objdump and recursive traversal
# engine of cfgrecovery
#

for f in *.rt.res; do
    testname=`basename $f .rt.res`
    binfile=../../../../test/test-samples/${testname}.bin
    objdump -d ${binfile} | grep -e "^ *[a-z0-9][a-z0-9]*:" | awk -F : '{print $1 }' | tr -d " " > $testname.addr.od
    grep -e '^\[(.*,0)\]' $f | sed -e 's/^\[(0x\([a-zA-Z0-9]*\),0)\].*/\1/g' | tr [:upper:] [:lower:] > $testname.addr.rt
    diff $testname.addr.od  $testname.addr.rt > $testname.addr.diff
    rm -f $testname.addr.od  $testname.addr.rt
done


for f in *.addr.diff; do
    testname=`basename $f .addr.diff`
    binfile=../../../../test/test-samples/${testname}.bin
    for a in `grep '<' $f | awk '{ print $2 }'`; do
	objdump -d ${binfile} | grep -e "^ *$a:" >> $testname.addr.diff
    done
done