Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Import ProD3.examples.sbf.Utils.
Import ListNotations.
Open Scope Z_scope.

Section ConFilter.

Definition row num_slots := { r: list bool | Zlength r = num_slots }.

Definition frame num_rows num_slots := { fr: list (row num_slots) | Zlength fr = num_rows }.

Program Definition row_insert {num_slots} (r : row num_slots) (i : Z) : row num_slots :=
  upd_Znth i r true.
Next Obligation.
  rewrite Zlength_upd_Znth.
  destruct r. easy.
Qed.

Definition items size := { i: list Z | Zlength i = size }.

Program Definition frame_insert {num_rows num_slots} (f : frame num_rows num_slots)
  (is : items num_rows) : frame num_rows num_slots := map2 row_insert f is.
Next Obligation.
  rewrite Zlength_map2. destruct is, f. simpl. lia.
Qed.

Program Definition row_clear {num_slots} (r : row num_slots) (i : Z) : row num_slots:=
  upd_Znth i r false.
Next Obligation.
  rewrite Zlength_upd_Znth. destruct r. easy.
Qed.

Program Definition empty_row num_slots (H: 0 < num_slots) : row num_slots :=
  Zrepeat false num_slots.
Next Obligation.
  apply Zlength_Zrepeat. lia.
Qed.

Program Definition frame_clear {num_rows num_slots} (f : frame num_rows num_slots)
  (is : items num_rows) : frame num_rows num_slots:= map2 row_clear f is.
Next Obligation.
  rewrite Zlength_map2. destruct is, f. simpl. lia.
Qed.

Program Definition row_query {num_slots} (r : row num_slots) (i : Z) : bool :=
  Znth i r.

Program Definition frame_query {num_rows num_slots} (f : frame num_rows num_slots)
  (is : list Z) : bool :=
  fold_andb (map2 row_query f is).

End ConFilter.
