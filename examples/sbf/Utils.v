Require Export Coq.Lists.List.
Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zcomplements.
Require Export Coq.micromega.Lia.
Require Export VST.zlist.Zlist.
Open Scope Z_scope.

Definition fold_andb (l : list bool) :=
  fold_left andb l true.

Definition fold_orb (l : list bool) :=
  fold_left orb l false.

Definition map2 {A B C} (f : A -> B -> C) (al : list A) (bl : list B) : list C :=
  map (uncurry f) (combine al bl).

Lemma Zlength_map2 : forall {A B C} (f : A -> B -> C) al bl,
  Zlength (map2 f al bl) = Z.min (Zlength al) (Zlength bl).
Proof.
  unfold map2. induction al; intros; destruct bl.
  - auto.
  - simpl. list_solve.
  - simpl. list_solve.
  - simpl. specialize (IHal bl). list_solve.
Qed.

Lemma Znth_map2 : forall {A B C} {da : Inhabitant A} {db : Inhabitant B} {dc : Inhabitant C}
    (f : A -> B -> C) al bl i,
  Zlength al = Zlength bl ->
  0 <= i < Zlength al ->
  Znth i (map2 f al bl) = f (Znth i al) (Znth i bl).
Proof.
  unfold map2. induction al; intros; destruct bl.
  - list_solve.
  - simpl. list_solve.
  - simpl. list_solve.
  - simpl. specialize (IHal bl (i-1)).
    destruct (Z.eq_dec i 0).
    + list_solve.
    + list_simplify.
      apply IHal; list_solve.
Qed.

Hint Rewrite @Zlength_map2 using Zlength_solve : Zlength.
Hint Rewrite @Znth_map2 using Zlength_solve : Znth.

Lemma Forall2_forall_range2 : forall {A B} {da : Inhabitant A} {db : Inhabitant B}
    (P : A -> B -> Prop) al bl,
  Forall2 P al bl <-> Zlength al = Zlength bl /\ forall_range2 0 (Zlength al) 0 al bl P.
Proof.
  intros. split; intros.
  - induction H.
    + unfold forall_range2, forall_i; split; intros; list_solve.
    + destruct IHForall2.
      unfold forall_range2, forall_i; split; intros; list_solve.
  - destruct H. generalize dependent bl; induction al; intros.
    + assert (bl = nil) by list_solve. subst; auto.
    + destruct bl; only 1 : list_solve.
      constructor.
      { specialize (H0 0 ltac:(list_solve)). simpl in H0. list_solve. }
      { apply IHal; list_solve. }
Qed.
