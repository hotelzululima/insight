#! /bin/sh

autotools_files=autotools-files

if [ ! -d ${autotools_files}/m4 ]; then
    mkdir -p ${autotools_files}/m4
fi

autoreconf -i
