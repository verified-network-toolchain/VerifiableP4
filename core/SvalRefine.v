Require Import Coq.NArith.BinNat.
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
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (String.string).
Notation path := (list ident).

(* bit_refine a b means a includes b. *)
Inductive bit_refine : option bool -> option bool -> Prop :=
  | read_none : forall ob, bit_refine None ob
  | read_some : forall b, bit_refine (Some b) (Some b).

(* sval_refine a b means a includes b. *)
Definition sval_refine := exec_val bit_refine.

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
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case1; eauto.
  Qed.
End exec_val_trans.

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

Lemma sval_refine_get : forall sv sv' f,
  sval_refine sv sv' ->
  sval_refine (get f sv) (get f sv').
Proof.
  intros.
  inv H; try solve [constructor].
  - unfold get.
    destruct (AList.get kvs f) eqn:H_get1; destruct (AList.get kvs' f) eqn:H_get2.
    + eapply all_values_get_some_rel; eauto.
    + epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get2 in H. inv H.
    + epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get1 in H. inv H.
    + constructor.
  - unfold get.
    destruct (AList.get kvs f) eqn:H_get1; destruct (AList.get kvs' f) eqn:H_get2.
    + eapply all_values_get_some_rel; eauto.
    + epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get2 in H. inv H.
    + epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get1 in H. inv H.
    + constructor.
  - unfold get.
    destruct (AList.get kvs f) eqn:H_get1; destruct (AList.get kvs' f) eqn:H_get2.
    + eapply all_values_get_some_rel; eauto.
    + epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get2 in H. inv H.
    + epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H.
      rewrite H_get1 in H. inv H.
    + constructor.
Qed.

End SvalRefine.
