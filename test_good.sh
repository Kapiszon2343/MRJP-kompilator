#!/bin/bash
FILES="./lattests/good/*.lat"

for f in $FILES
do
    core = {f%.lat}
    ./latc_x86_64 $f
    $core >$core.out
    diff $core.out $core.output
done