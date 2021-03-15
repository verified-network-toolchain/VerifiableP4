Require Import Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Parameter Index:Type.
Parameter index_beq: Index -> Index -> bool.
(*Parameter Index_eq: forall (i j:Index), {i=j} + {i<>j}.*)

Parameter index_refl: forall i, index_beq i i = true.

Parameter Hash0: Z -> Index.
Parameter Hash1: Z -> Index.
Parameter Hash2: Z -> Index.

Definition Filter:= Index -> bool.

Definition upd (F:Filter) (i:Index) (b:bool): Filter :=
  fun j => if index_beq i j then b else F j.

Definition get (F:Filter) (i:Index): bool := F i.

Definition add0 (F:Filter) (z:Z) :=
   upd F (Hash0 z) true.

Definition add1 (F:Filter) (z:Z) :=
   upd F (Hash1 z) true.

Definition add2 (F:Filter) (z:Z) :=
   upd F (Hash2 z) true.

Definition add (F:Filter * Filter * Filter) (z:Z) :=
match F with (F0, F1, F2) =>
  (add0 F0 z, add1 F1 z, add2 F2 z)
end.

Definition addm (F:Filter * Filter * Filter) (zs:list Z):=
List.fold_left add zs F.

Definition query (F:Filter * Filter * Filter) (z:Z) : bool :=
match F with (F0, F1, F2) =>
  get F0 (Hash0 z) && get F1 (Hash1 z) && get F2 (Hash2 z)
end.

Lemma bf_add_query_true z F: query (add F z) z = true.
destruct F as [[F0 F1] F2]. simpl. unfold get, add0, add1, add2, upd.
rewrite ! index_refl. trivial. Qed.

Lemma eqindexP : forall n m, reflect (index_beq n m = true) (index_beq n m).
Proof.
  intros n m. apply iff_reflect. reflexivity.
Qed.

Lemma add0_comm x y F: add0 (add0 F x) y = add0 (add0 F y) x.
Proof.
  unfold add0, upd.
  apply functional_extensionality.
  intros.
  destruct (eqindexP (Hash0 x) x0) as [H1|H2];
  destruct (eqindexP (Hash0 y) x0) as [H3|H4];
  reflexivity.
Qed.

Lemma add1_comm x y F: add1 (add1 F x) y = add1 (add1 F y) x.
Proof.
  unfold add1, upd.
  apply functional_extensionality.
  intros.
  destruct (eqindexP (Hash1 x) x0) as [H1|H2];
  destruct (eqindexP (Hash1 y) x0) as [H3|H4];
  reflexivity.
Qed.

Lemma add2_comm x y F: add2 (add2 F x) y = add2 (add2 F y) x.
Proof.
  unfold add2, upd.
  apply functional_extensionality.
  intros.
  destruct (eqindexP (Hash2 x) x0) as [H1|H2];
  destruct (eqindexP (Hash2 y) x0) as [H3|H4];
  reflexivity.
Qed.

Lemma add_comm x y F: add (add F x) y = add (add F y) x.
Proof.
  destruct F as [[F0 F1] F2]. simpl.
  apply pair_equal_spec. split.
  apply pair_equal_spec. split.
  apply add0_comm. apply add1_comm. apply add2_comm.
Qed.

Lemma addm_add_comm : forall x ys F, addm (add F x) ys = add (addm F ys) x.
Proof.
  intros. generalize F.
  induction ys as [|hd tl IH]; unfold addm.
  - intros. reflexivity.
  - intros. unfold addm in IH. unfold fold_left in *. rewrite add_comm.
    rewrite IH. reflexivity.
Qed.

Theorem BFNoFalseNegative z zs F: query (addm (add F z) zs) z  = true.
Proof.
  rewrite addm_add_comm. apply bf_add_query_true.
Qed.

