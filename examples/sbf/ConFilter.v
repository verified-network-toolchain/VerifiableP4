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

Program Definition Inhabitant_listn {A : Type} {dA : Inhabitant A} size (H : 0 <= size) : Inhabitant (listn A size) :=
  Zrepeat (default (Inhabitant := dA)) size.
Next Obligation.
  list_solve.
Qed.

Section ConFilter.

Context {num_rows num_slots : Z}.

Definition row := listn bool num_slots.

Definition frame := listn row num_rows.

Program Definition row_insert (r : row) (i : Z) : row :=
  upd_Znth i r true.
Next Obligation.
  destruct r. list_solve.
Qed.

Lemma row_insert_comm : forall (r : row) x y,
  row_insert (row_insert r x) y = row_insert (row_insert r y) x.
Proof.
  intros. destruct r as [r ?H]. unfold row_insert. simpl.
  apply subset_eq_compat. list_solve.
Qed.

Program Definition frame_insert (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_insert f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_clear (r : row) (i : Z) : row:=
  upd_Znth i r false.
Next Obligation.
  destruct r. list_solve.
Qed.

Program Definition frame_clear (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_clear f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_query (r : row) (i : Z) : bool :=
  Znth i r.

Lemma row_query_insert_true : forall (r: row) z,
  0 <= z < num_slots -> row_query (row_insert r z) z = true.
Proof.
  intros. destruct r as [r ?H]. unfold row_query, row_insert. simpl. list_solve.
Qed.

Program Definition frame_query (f : frame) (is : list Z) : bool :=
  fold_andb (map2 row_query f is).

End ConFilter.

Arguments row : clear implicits.
Arguments frame : clear implicits.
