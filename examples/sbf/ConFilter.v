Require Import Coq.ZArith.BinInt.
Require Import ProD3.examples.sbf.Utils.
Import ListNotations.
Open Scope Z_scope.

Section ConFilter.

Definition row := list bool.

Definition frame := list row.

Definition row_insert (r : row) (i : Z) : row :=
  upd_Znth i r true.

Definition frame_insert (f : frame) (is : list Z) : frame :=
  map2 row_insert f is.

Definition row_clear (r : row) (i : Z) : row :=
  upd_Znth i r false.

Definition frame_clear (f : frame) (is : list Z) : frame :=
  map2 row_clear f is.

Definition row_query (r : row) (i : Z) : bool :=
  Znth i r.

Definition frame_query (f : frame) (is : list Z) : bool :=
  fold_andb (map2 row_query f is).

End ConFilter.
