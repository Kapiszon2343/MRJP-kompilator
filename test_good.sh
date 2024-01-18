#!/bin/bash
FILES="./lattests/good/*.lat"

for f in $FILES
do
    core = {f%.lat}
    ./latc_x86_64 ./lattests/good/$f
    ./lattests/good/$core >./lattests/good/$core.out
    diff ./lattests/good/$core.out ./lattests/good/$core.output
done