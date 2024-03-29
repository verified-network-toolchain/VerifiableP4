#!/bin/bash

example_dir="./examples"
include_dir="./includes"

if [ $1 == "all" ]; then
    for entry in `find "$example_dir" -d 1 -type d`; do
        printf "\nGenerating Coq AST of $entry/basic.p4 \n"
        if `test -e "$entry"/basic.p4`
        then
            petr4 typecheck -json \
                "$entry"/basic.p4 \
                -I "$include_dir" -exportp4 \
                -export-file "$entry"/p4ast.v \
                -normalize -gen-loc
        fi
    done
else
    petr4 check \
        $1 \
        -I "$include_dir" -I "." \
        -output-p4light $(dirname $1)/p4ast.v \
        -normalize -gen-loc
fi
