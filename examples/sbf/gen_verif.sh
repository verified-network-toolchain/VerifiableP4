#!/bin/bash

cd $( dirname -- "$0"; )

cp verif_Row11.v verif_Row12.v
sed -i 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_2"\]/' verif_Row12.v
cp verif_Row11.v verif_Row13.v
sed -i 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_3"\]/' verif_Row13.v
