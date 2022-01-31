Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Members.
Require Import Poulet4.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Section SvalRefine.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).

(* bit_refine a b means a includes b. *)
Inductive bit_refine : option bool -> option bool -> Prop :=
  | read_none : forall ob, bit_refine None ob
  | read_some : forall b, bit_refine (Some b) (Some b).

(* sval_refine a b means a includes b. *)
Definition sval_refine := exec_val bit_refine.

Section exec_val_refl.
  Context {A : Type} (f : A -> A -> Prop).
  Hypothesis H_f_refl : forall x, f x x.

  Lemma Forall2_refl : forall v,
    Forall2 f v v.
  Proof.
    induction v; intros.
    - constructor.
    - constructor; eauto.
  Qed.

  Hint Resolve Forall2_refl : core.

  Lemma exec_val_refl_case1 : forall vs,
    Forall (fun v : ValueBase => exec_val f v v) vs ->
    Forall2 (exec_val f) vs vs.
  Proof.
    induction vs; intros; inv H; constructor; auto.
  Qed.

  Lemma exec_val_refl_case2 : forall (vs : list (ident * ValueBase)),
    Forall (fun '(_, v) => exec_val f v v) vs ->
    AList.all_values (exec_val f) vs vs.
  Proof.
    induction vs; intros; inv H; constructor.
    - destruct a; auto.
    - apply IHvs; auto.
  Qed.

  Lemma exec_val_refl : forall v,
    exec_val f v v.
  Proof.
    intros v.
    induction v using custom_ValueBase_ind;
      constructor; eauto.
    - eapply exec_val_refl_case1; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case1; eauto.
  Qed.
End exec_val_refl.

Lemma bit_refine_refl : forall b : option bool,
  bit_refine b b.
Proof.
  destruct b as [[] | ]; constructor.
Qed.

Lemma sval_refine_refl : forall sv,
  sval_refine sv sv.
Proof.
  apply exec_val_refl. exact bit_refine_refl.
Qed.

Definition rel_trans {A B C} (f : A -> B -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop) :=
  forall a b c,
    f a b ->
    g b c ->
    h a c.

Section exec_val_trans.
  Context {A B C : Type} (f : A -> B -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop).
  Hypothesis H_rel_trans : rel_trans f g h.

  Lemma Forall2_trans : forall v1 v2 v3,
    Forall2 f v1 v2 ->
    Forall2 g v2 v3 ->
    Forall2 h v1 v3.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; inv H0; constructor.
    - inv H; inv H0; constructor; eauto.
  Qed.

  Hint Resolve Forall2_trans : core.

  Lemma exec_val_trans_case1 : forall vs1 vs2 vs3,
    Forall
      (fun v2 : ValueBase =>
        forall v1 v3 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v3 -> exec_val h v1 v3) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs2 vs3 ->
    Forall2 (exec_val h) vs1 vs3.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H1; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_trans_case2 : forall (vs1 : list (ident * ValueBase)) vs2 vs3,
    Forall
      (fun '(_, v2) =>
        forall v1 v3 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v3 -> exec_val h v1 v3) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs2 vs3 ->
    AList.all_values (exec_val h) vs1 vs3.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H1; inv H0; inv H; constructor.
    - destruct H4; destruct H5; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  (* rel_trans (exec_val f) (exec_val g) (exec_val h) *)
  Lemma exec_val_trans : forall v1 v2 v3,
    exec_val f v1 v2 ->
    exec_val g v2 v3 ->
    exec_val h v1 v3.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f H_g;
      inv H_f; inv H_g;
      constructor; eauto.
    - eapply exec_val_trans_case1; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case1; eauto.
  Qed.
End exec_val_trans.

Section exec_val_sym.
  Context {A B : Type} (f : A -> B -> Prop) (g : B -> A -> Prop).
  Hypothesis H_rel_sym : forall a b, f a b -> g b a.

  Lemma Forall2_sym : forall v1 v2,
    Forall2 f v1 v2 ->
    Forall2 g v2 v1.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; constructor.
    - inv H; constructor; eauto.
  Qed.

  Hint Resolve Forall2_sym : core.

  Lemma exec_val_sym_case1 : forall vs1 vs2,
    Forall
      (fun v2 : ValueBase =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v1) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs2 vs1.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_sym_case2 : forall (vs1 : list (ident * ValueBase)) vs2,
    Forall
      (fun '(_, v2) =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v1) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs2 vs1.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor.
    - destruct H4; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  Lemma exec_val_sym : forall v1 v2,
    exec_val f v1 v2 ->
    exec_val g v2 v1.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f;
      inv H_f;
      constructor; eauto.
    - eapply exec_val_sym_case1; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case1; eauto.
  Qed.
End exec_val_sym.

Section exec_val_impl.
  Context {A B : Type} (f : A -> B -> Prop) (g : A -> B -> Prop).
  Hypothesis H_rel_impl : forall a b, f a b -> g a b.

  Lemma Forall2_impl : forall v1 v2,
    Forall2 f v1 v2 ->
    Forall2 g v1 v2.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; constructor.
    - inv H; constructor; eauto.
  Qed.

  Hint Resolve Forall2_impl : core.

  Lemma exec_val_impl_case1 : forall vs1 vs2,
    Forall
      (fun v2 : ValueBase =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v1 v2) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs1 vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_impl_case2 : forall (vs1 : list (ident * ValueBase)) vs2,
    Forall
      (fun '(_, v2) =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v1 v2) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs1 vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor.
    - destruct H4; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  Lemma exec_val_impl : forall v1 v2,
    exec_val f v1 v2 ->
    exec_val g v1 v2.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f;
      inv H_f;
      constructor; eauto.
    - eapply exec_val_impl_case1; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case1; eauto.
  Qed.
End exec_val_impl.

Lemma Forall2_True: forall {A B: Type} (l1: list A) (l2: list B),
    length l1 = length l2 -> Forall2 (fun _ _ => True) l1 l2.
Proof.
  intros. revert l2 H.
  induction l1; intros; destruct l2; simpl in H; inv H; constructor; auto.
Qed.

Lemma bit_refine_trans : forall b1 b2 b3 : option bool,
  bit_refine b1 b2 ->
  bit_refine b2 b3 ->
  bit_refine b1 b3.
Proof.
  intros.
  inv H; inv H0; constructor.
Qed.

Lemma sval_refine_trans : forall sv1 sv2 sv3,
  sval_refine sv1 sv2 ->
  sval_refine sv2 sv3 ->
  sval_refine sv1 sv3.
Proof.
  apply exec_val_trans. exact bit_refine_trans.
Qed.

Lemma all_values_get_some_rel : forall {A} (kvl kvl' : AList.StringAList A) f rel v v',
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  AList.get kvl' f = Some v' ->
  rel v v'.
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H1, H0 by auto.
      inv H1; inv H0.
      auto.
    + rewrite AList.get_neq_cons in H1, H0 by auto.
      auto.
Qed.

Lemma all_values_get_some_is_some : forall {A} (kvl kvl' : AList.StringAList A) f rel v,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  is_some (AList.get kvl' f).
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H0 |- * by auto.
      auto.
    + rewrite AList.get_neq_cons in H0 |- * by auto.
      auto.
Qed.

Lemma all_values_get_some_exists_rel: forall {A} (kvl kvl' : AList.StringAList A) f rel v,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  exists v', AList.get kvl' f = Some v' /\ rel v v'.
Proof.
  intros. pose proof H0. eapply all_values_get_some_is_some in H0; eauto.
  unfold is_some, isSome in H0. destruct (AList.get kvl' f) eqn:?H. 2: inv H0.
  eapply all_values_get_some_rel in H2; eauto.
Qed.

Lemma all_values_get_none_is_none : forall {A} (kvl kvl' : AList.StringAList A) f rel,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = None ->
  AList.get kvl' f = None.
Proof.
  intros.
  induction H; auto.
  destruct x as [kx vx]; destruct y as [ky vy].
  destruct H. simpl in H. subst ky.
  destruct (String.string_dec f kx) eqn:?.
  - rewrite AList.get_eq_cons in H0 |- * by auto. inv H0.
  - rewrite AList.get_neq_cons in H0 |- * by auto. auto.
Qed.

Lemma all_values_get_some_is_some' : forall {A} (kvl kvl' : AList.StringAList A) f rel v',
  AList.all_values rel kvl kvl' ->
  AList.get kvl' f = Some v' ->
  is_some (AList.get kvl f).
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H0 |- * by auto.
      auto.
    + rewrite AList.get_neq_cons in H0 |- * by auto.
      auto.
Qed.

Lemma all_values_get_is_some : forall {A} (kvl kvl' : AList.StringAList A) f rel,
  AList.all_values rel kvl kvl' ->
  is_some (AList.get kvl f) = is_some (AList.get kvl' f).
Proof.
  intros.
  destruct (AList.get kvl f) eqn:H_get1; destruct (AList.get kvl' f) eqn:H_get2; auto.
  - epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0; auto.
    rewrite H_get2 in H0. inv H0.
  - epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0; auto.
    rewrite H_get1 in H0. inv H0.
Qed.

Lemma all_values_key_unique : forall {A} (kvl kvl' : AList.StringAList A) rel,
    AList.all_values rel kvl kvl' ->
    AList.key_unique kvl -> AList.key_unique kvl'.
Proof.
  intros. induction H; auto. inv H0. destruct x. destruct (AList.get l s) eqn:?H.
  1: inv H3. simpl. destruct y. eapply all_values_get_none_is_none in H0; eauto.
  simpl in H. destruct H. subst s0. rewrite H0. apply IHForall2; auto.
Qed.

Lemma sval_refine_get_case1 : forall f kvs kvs',
  AList.all_values (exec_val bit_refine) kvs kvs' ->
  sval_refine (force ValBaseNull (AList.get kvs f)) (force ValBaseNull (AList.get kvs' f)).
Proof.
  intros.
  destruct (AList.get kvs f) eqn:H_get1; destruct (AList.get kvs' f) eqn:H_get2.
  + eapply all_values_get_some_rel; eauto.
  + epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0.
    rewrite H_get2 in H0. inv H0.
  + epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0.
    rewrite H_get1 in H0. inv H0.
  + constructor.
Qed.

Lemma sval_refine_get : forall sv sv' f,
  sval_refine sv sv' ->
  sval_refine (get f sv) (get f sv').
Proof.
  intros.
  inv H; try solve [constructor | apply sval_refine_get_case1; auto].
  - unfold get.
    destruct (String.eqb f "size").
    {
      apply Forall2_length in H0.
      pose proof (Zlength_correct lv).
      pose proof (Zlength_correct lv').
      replace (Zlength lv) with (Zlength lv') by lia.
      apply sval_refine_refl.
    }
    destruct (String.eqb f "lastIndex");
      apply sval_refine_refl.
Qed.

Lemma Forall2_bit_refine_Some_same:
  forall l1 l2 : list bool, Forall2 bit_refine (map Some l1) (map Some l2) -> l1 = l2.
Proof.
  induction l1; intros.
  - inv H. symmetry in H0. apply map_eq_nil in H0. now subst.
  - destruct l2; simpl in H; inv H. inv H3. f_equal. now apply IHl1.
Qed.

#[local] Open Scope Z_scope.

Lemma sval_refine_to_loptbool_eq : forall w n1 n2,
  0 <= n1 < Z.pow 2 (Z.of_N w) ->
  0 <= n2 < Z.pow 2 (Z.of_N w) ->
  SvalRefine.sval_refine
    (Value.ValBaseBit (P4Arith.to_loptbool w n1))
    (Value.ValBaseBit (P4Arith.to_loptbool w n2)) ->
  n1 = n2.
Proof.
  intros. inv H1. unfold P4Arith.to_loptbool in H4.
  apply Forall2_bit_refine_Some_same in H4.
  pose proof (eq_refl (P4Arith.BitArith.lbool_to_val (P4Arith.to_lbool w n1) 1 0)).
  rewrite H4 in H1 at 2. rewrite !P4Arith.bit_to_lbool_back in H1.
  unfold P4Arith.BitArith.mod_bound, P4Arith.BitArith.upper_bound in H1.
  rewrite !Zmod_small in H1; auto.
Qed.

End SvalRefine.
