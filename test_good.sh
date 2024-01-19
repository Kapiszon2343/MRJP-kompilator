#!/bin/bash
FILES="./lattests/good/*.lat"

for f in $FILES
do
    CORE=${f%.*}
    ./latc_x86_64 $f
    $CORE >$CORE.out
    diff $CORE.out $CORE.output
done