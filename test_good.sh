#!/bin/bash
FILES="./lattests/good/*/*.lat"

for f in $FILES
do
    CORE=${f%.*}
    ./latc_x86_64 $f
    if [ -f $CORE.input ]; then
        $CORE <$CORE.input >$CORE.out
    else
        $CORE >$CORE.out
    fi
    diff $CORE.out $CORE.output
done