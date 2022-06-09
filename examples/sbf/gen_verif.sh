#!/bin/bash

cd $( dirname -- "$0"; )

cp verif_Row11.v verif_Row12.v
sed -i.bak 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_2"\]/' verif_Row12.v
rm verif_Row12.v.bak

cp verif_Row11.v verif_Row13.v
sed -i.bak 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_3"\]/' verif_Row13.v
rm verif_Row13.v.bak

cp verif_Win_lazy.v verif_Win2.v
sed -i.bak 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_2"\]/' verif_Win2.v
sed -i.bak 's/verif_Row1/verif_Row2/' verif_Win2.v
rm verif_Win2.v.bak

cp verif_Win_lazy.v verif_Win3.v
sed -i.bak 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_3"\]/' verif_Win3.v
sed -i.bak 's/verif_Row1/verif_Row3/' verif_Win3.v
rm verif_Win3.v.bak

cp verif_Win_lazy.v verif_Win4.v
sed -i.bak 's/\["pipe"; "ingress"; "bf2_ds"; "win_1"\]/\["pipe"; "ingress"; "bf2_ds"; "win_4"\]/' verif_Win4.v
sed -i.bak 's/verif_Row1/verif_Row4/' verif_Win4.v
rm verif_Win4.v.bak
