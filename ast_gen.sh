#!/bin/bash
cd ../petr4
dune build 

example_dir="../ProD3/examples"
include_dir="../ProD3/includes"

for entry in `find "$example_dir" -d 1 -type d`; do
    printf "\nGenerating Coq AST of $entry/basic.p4 \n"
    if `test -e "$entry"/basic.p4`
    then
        ../petr4/_build/default/bin/main.exe typecheck \
            "$entry"/basic.p4 \
            -I "$include_dir" -exportp4 \
            -export-file "$entry"/p4ast.v
    fi
done
