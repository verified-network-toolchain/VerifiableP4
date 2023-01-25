Require Export Coq.Lists.List.
Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zcomplements.
Require Export Coq.Sorting.Permutation.
Require Export Coq.micromega.Lia.
Require Export VST.zlist.Zlist.
Require Export Poulet4.Utils.Utils.
Open Scope Z_scope.

Definition map2 {A B C} (f : A -> B -> C) (al : list A) (bl : list B) : list C :=
  map (uncurry f) (combine al bl).

Lemma fold_andb_false: forall l, fold_left andb l false = false.
Proof. induction l; simpl; intros; auto. Qed.

Lemma fold_andb_cons: forall l b, fold_andb (b :: l) = (b && fold_andb l)%bool.
Proof.
  intros. unfold fold_andb. simpl. destruct b; simpl; auto.
  apply fold_andb_false.
Qed.

Lemma fold_andb_true: forall l, fold_andb l = true <-> (forall i, 0 <= i < Zlength l -> Znth i l = true).
Proof.
  induction l; split; intros; simpl in *; auto.
  - list_solve.
  - rewrite fold_andb_cons in H. apply andb_prop in H. destruct H. subst.
    rewrite IHl in H1. list_simplify. apply H1. lia.
  - rewrite fold_andb_cons. cut (a = true).
    + intros. subst. simpl. apply IHl. intros.
      assert (0 <= i + 1 < Zlength (true :: l)) by list_solve.
      apply H in H1. rewrite Znth_pos_cons in H1 by lia. rewrite <- H1. f_equal. lia.
    + assert (0 <= 0 < Zlength (a :: l)) by list_solve. apply H in H0.
      now rewrite Znth_0_cons in H0.
Qed.

Lemma forallb_fold_andb {A : Type}: forall (f: A -> bool) l, forallb f l = fold_andb (map f l).
Proof.
  intros. induction l; simpl; auto. rewrite IHl, fold_andb_cons. auto.
Qed.

Lemma fold_orb_cons: forall l b, fold_orb (b :: l) = (b || fold_orb l)%bool.
Proof.
  intros. unfold fold_orb. simpl. destruct b; simpl; auto.
  induction l; simpl; intros; auto.
Qed.

Lemma existsb_fold_orb {A: Type}: forall (f: A -> bool) l, existsb f l = fold_orb (map f l).
Proof.
  intros. induction l; simpl; auto. rewrite IHl, fold_orb_cons. auto.
Qed.

Lemma fold_orb_false: forall l, fold_orb (false :: l) = fold_orb l.
Proof. intros. rewrite fold_orb_cons. now simpl. Qed.

Lemma fold_orb_perm: forall l1 l2, Permutation l1 l2 -> fold_orb l1 = fold_orb l2.
Proof.
  intros. induction H; simpl; auto; try rewrite !fold_orb_cons.
  - now f_equal.
  - rewrite !Bool.orb_assoc, (Bool.orb_comm x y). auto.
  - rewrite IHPermutation1. auto.
Qed.

Lemma map2_cons {A B C}: forall (f : A -> B -> C) a al b bl,
    map2 f (a :: al) (b :: bl) = f a b :: map2 f al bl.
Proof. intros. unfold map2. simpl. auto. Qed.

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

Lemma Zlength_fold_right {A B}: forall (f: B -> list A -> list A) init l,
    (forall b la, Zlength (f b la) = Zlength la) ->
    Zlength (fold_right f init l) = Zlength init.
Proof.
  intros. revert l init. induction l; intros; simpl; auto.
  rewrite H. easy.
Qed.

Lemma Forall_wrap {A: Type}: forall (P: A -> Prop) (l: list A) i len,
    len = Zlength l -> 0 <= i < len -> Forall P l <-> Forall P (sublist i (i + len) (l ++ l)).
Proof.
  intros. rewrite <- (sublist_rejoin i len) by list_solve. rewrite Forall_app.
  rewrite (sublist_app1 A i len) by lia. rewrite (sublist_app2 len (i + len)) by lia.
  replace (len - Zlength l) with 0 by lia. replace (i + len - Zlength l) with i by lia.
  now rewrite and_comm, <- Forall_app, sublist_rejoin, sublist_same by lia.
Qed.

Definition sumup (l: list Z) := fold_left Z.add l 0.

Lemma sumup_cons: forall l b, sumup (b :: l) = b + sumup l.
Proof.
Admitted.

Lemma sumup_perm: forall l1 l2, Permutation l1 l2 -> sumup l1 = sumup l2.
Proof. intros. induction H; simpl; auto; try rewrite !sumup_cons; lia. Qed.
