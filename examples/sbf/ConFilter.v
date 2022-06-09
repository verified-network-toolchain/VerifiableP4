Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Import ProD3.examples.sbf.Utils.
Import ListNotations.
Open Scope Z_scope.

Definition listn (T : Type) size := { i : list T | Zlength i = size }.

Program Definition map_listn {A B : Type} {size}
    (f : A -> B) (l : listn A size) : listn B size :=
  map f l.
Next Obligation.
  destruct l as [l ?H]. list_solve.
Qed.

Definition row num_slots := listn bool num_slots.

Definition frame num_rows num_slots := listn (row num_slots) num_rows.

Section ConFilter.

Context {num_rows num_slots : Z}.

Program Definition row_insert (r : row num_slots) (i : Z) : row num_slots :=
  upd_Znth i r true.
Next Obligation.
  destruct r. list_solve.
Qed.

Lemma row_insert_comm : forall (r : row num_slots) x y,
  row_insert (row_insert r x) y = row_insert (row_insert r y) x.
Proof.
  intros. destruct r as [r ?H]. unfold row_insert. simpl.
  apply subset_eq_compat. list_solve.
Qed.

Program Definition frame_insert (f : frame num_rows num_slots)
    (is : listn Z num_rows) : frame num_rows num_slots :=
  map2 row_insert f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_clear (r : row num_slots) (i : Z) : row num_slots:=
  upd_Znth i r false.
Next Obligation.
  destruct r. list_solve.
Qed.

Program Definition empty_row num_slots (H: 0 < num_slots) : row num_slots :=
  Zrepeat false num_slots.
Next Obligation.
  list_solve.
Qed.

Program Definition frame_clear (f : frame num_rows num_slots)
    (is : listn Z num_rows) : frame num_rows num_slots :=
  map2 row_clear f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_query (r : row num_slots) (i : Z) : bool :=
  Znth i r.

Lemma row_query_insert_true : forall (r: row num_slots) z,
  0 <= z < num_slots -> row_query (row_insert r z) z = true.
Proof.
  intros. destruct r as [r ?H]. unfold row_query, row_insert. simpl. list_solve.
Qed.

Program Definition frame_query (f : frame num_rows num_slots)
    (is : list Z) : bool :=
  fold_andb (map2 row_query f is).

End ConFilter.
