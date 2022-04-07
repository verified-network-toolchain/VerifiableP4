Require Import Coq.ZArith.ZArith.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.Utils.Utils.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.ExtPred.
Require Import Poulet4.P4light.Syntax.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Section Implies.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).
Notation Expression := (@Expression tags_t).

Context {target : @Target tags_t Expression}.

Definition mem_simplify_aux (a : mem_assertion) '((p, sv) : path * Sval) : option (Sval * Sval) :=
  match AList.get a p with
  | Some sv' => Some (sv, sv')
  | None => None
  end.

Lemma mem_simplify_aux_sound : forall a psv svp,
  mem_simplify_aux a psv = Some svp ->
  uncurry sval_refine svp ->
  forall m, mem_denote a m -> mem_satisfies_unit m psv.
Proof.
  intros.
  destruct psv as [p sv].
  unfold mem_simplify_aux in *.
  destruct (AList.get a p) eqn:H_get; inv H.
  eapply mem_denote_get in H_get; eauto.
  unfold mem_satisfies_unit in *.
  destruct (PathMap.get p m); only 2 : inv H_get.
  eapply sval_refine_trans; eauto.
Qed.

Definition mem_implies_simplify (a a' : mem_assertion) : option (list (Sval * Sval)) :=
  lift_option (map (mem_simplify_aux a) a').

Lemma mem_implies_simplify_sound : forall a a' svps,
  mem_implies_simplify a a' = Some svps ->
  Forall (uncurry sval_refine) svps ->
  forall m, mem_denote a m -> mem_denote a' m.
Proof.
  intros.
  unfold mem_implies_simplify in *.
  apply lift_option_inv in H.
  unfold mem_denote, mem_satisfies.
  rewrite fold_right_and_True in *.
  list_simplify.
  apply mem_simplify_aux_sound with a (Znth i svps).
  - list_simplify.
    (* list_solve cannot perform this simplification because the implicit type mem_unit and (path * Sval)
      are not converted automatically. *)
    rewrite Znth_map in H12 by auto. list_solve.
  - list_solve.
  - auto.
Qed.

Definition ext_implies (a a' : ext_assertion) : Prop :=
  forall es, ext_denote a es -> ext_denote a' es.

Lemma ext_implies_nil: forall a, ext_implies a [].
Proof. repeat intro. red. red. easy. Qed.

Lemma ext_implies_cons: forall (a c: ext_assertion) b,
    ext_implies a (b :: c) <-> (ext_implies a [b] /\ ext_implies a c).
Proof.
  intros. unfold ext_implies, ext_denote. split; intros.
  - split; intros; apply H in H0; red in H0; simpl in H0; red; simpl; destruct H0; auto.
  - destruct H. specialize (H _ H0). specialize (H1 _ H0). clear H0.
    unfold ext_satisfies in *. simpl in *. destruct H. split; auto.
Qed.

Ltac simpl_ext_implies :=
  repeat match goal with
    | |- ext_implies _ [] => apply ext_implies_nil
    | |- ext_implies _ (_ :: _ :: _) => apply ext_implies_cons; split
    | |- ext_implies _ [_] =>
        try (let es := fresh "es" in
             let H := fresh "H" in
             unfold ext_implies, ext_denote, ext_satisfies;
             intros es H;
             simpl in H |- *;
             intuition; easy)
  end.

Section SIMPL_EXT_IMPLIES_TEST.

  Variable P Q R S: ext_pred.

  Goal ext_implies [P; Q; R; S] [].
  Proof. simpl_ext_implies. Qed.

  (* Rearrange order doesn't matter *)
  Goal ext_implies [P; Q; R; S] [R; S; Q; P].
  Proof. simpl_ext_implies. Qed.

  (* It will leave unsolved goals *)
  Goal ext_implies [P; Q; S] [R; S; Q].
  Proof. simpl_ext_implies. Abort.

  (* If we have additional rules, the tactic can solve the goal *)
  Goal (forall es, P es -> R es) -> ext_implies [P; Q; S] [R; S; Q].
  Proof. intros. simpl_ext_implies. Qed.

End SIMPL_EXT_IMPLIES_TEST.

(* Definition ext_simplify_aux (a : ext_assertion) '((p, eo) : path * extern_object) : option (extern_object * extern_object) :=
  match AList.get a p with
  | Some eo' => Some (eo, eo')
  | None => None
  end.

Lemma ext_simplify_aux_sound : forall a peo eop,
  ext_simplify_aux a peo = Some eop ->
  uncurry eq eop ->
  forall es, ext_denote a es -> ext_satisfies_unit es peo.
Proof.
  intros.
  destruct peo as [p eo].
  unfold ext_simplify_aux in *.
  destruct (AList.get a p) eqn:H_get; inv H.
  eapply ext_denote_get in H_get; eauto.
  inv H0.
  auto.
Qed.

Definition ext_implies_simplify (a a' : ext_assertion) : option (list (extern_object * extern_object)) :=
  lift_option (map (ext_simplify_aux a) a').

Lemma ext_implies_simplify_sound : forall a a' eops,
  ext_implies_simplify a a' = Some eops ->
  Forall (uncurry eq) eops ->
  forall m, ext_denote a m -> ext_denote a' m.
Proof.
  intros.
  unfold ext_implies_simplify in *.
  apply lift_option_inv in H.
  unfold ext_denote, ext_satisfies.
  rewrite fold_right_and_True in *.
  (* Cannot use list_solve because there's no Inhabitant for extern_object. *)
  generalize dependent a'.
  induction H0; intros.
  - destruct a'; inv H.
    constructor.
  - destruct a'; inv H2.
    constructor.
    + eapply ext_simplify_aux_sound; eauto.
    + eauto.
Qed. *)

Lemma implies_simplify : forall pre_mem pre_ext post_mem post_ext svps,
  mem_implies_simplify pre_mem post_mem = Some svps ->
  Forall (uncurry sval_refine) svps ->
  ext_implies pre_ext post_ext ->
  implies (MEM pre_mem (EXT pre_ext)) (MEM post_mem (EXT post_ext)).
Proof.
  unfold implies; intros.
  destruct st as [m es].
  destruct H2; split.
  - eapply mem_implies_simplify_sound; eauto.
  - apply H1. auto.
Qed.

Lemma arg_implies_simplify : forall pre_arg pre_mem pre_ext post_arg post_mem post_ext svps,
  Forall2 sval_refine post_arg pre_arg ->
  mem_implies_simplify pre_mem post_mem = Some svps ->
  Forall (uncurry sval_refine) svps ->
  ext_implies pre_ext post_ext ->
  arg_implies (ARG pre_arg (MEM pre_mem (EXT pre_ext))) (ARG post_arg (MEM post_mem (EXT post_ext))).
Proof.
  unfold implies; intros.
  unfold arg_implies; intros.
  destruct H3.
  split. 2 : { eapply implies_simplify; eauto. }
  eapply Forall2_trans. 1 : { unfold rel_trans. apply sval_refine_trans. }
  all : eauto.
Qed.

(* Lemma implies_simplify_ret : forall pre_mem pre_ext post_ret post_mem post_ext retv svps eops,
  ret_denote post_ret retv ->
  mem_implies_simplify pre_mem post_mem = Some svps ->
  Forall (uncurry sval_refine) svps ->
  ext_implies_simplify pre_ext post_ext = Some eops ->
  Forall (uncurry eq) eops ->
  implies (MEM pre_mem (EXT pre_ext)) (RET post_ret (MEM post_mem (EXT post_ext)) retv).
Proof.
  unfold implies; intros.
  destruct st as [m es].
  destruct H4; split; only 2 : split.
  - eauto.
  - eapply mem_implies_simplify_sound; eauto.
  - eapply ext_implies_simplify_sound; eauto.
Qed. *)

End Implies.
