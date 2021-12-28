Require Import Coq.ZArith.ZArith.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Hoare.
Require Import Poulet4.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Section Implies.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

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

Lemma fold_right_and_True : forall l,
  fold_right and True l <-> Forall id l.
Proof.
  intros; induction l; only 2 : destruct IHl; split; intros.
  - constructor.
  - constructor.
  - constructor; sfirstorder.
  - inv H1; sfirstorder.
Qed.

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

Definition ext_simplify_aux (a : ext_assertion) '((p, eo) : path * extern_object) : option (extern_object * extern_object) :=
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
Qed.

Lemma implies_simplify : forall pre_mem pre_ext post_mem post_ext svps eops,
  mem_implies_simplify pre_mem post_mem = Some svps ->
  Forall (uncurry sval_refine) svps ->
  ext_implies_simplify pre_ext post_ext = Some eops ->
  Forall (uncurry eq) eops ->
  implies (MEM pre_mem (EXT pre_ext)) (MEM post_mem (EXT post_ext)).
Proof.
  unfold implies; intros.
  destruct st as [m es].
  destruct H3; split.
  - eapply mem_implies_simplify_sound; eauto.
  - eapply ext_implies_simplify_sound; eauto.
Qed.

Lemma implies_simplify_ret : forall pre_mem pre_ext post_ret post_mem post_ext retv svps eops,
  (forall sv' : Sval, val_to_sval retv sv' -> ret_denote post_ret sv') ->
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
Qed.

End Implies.
