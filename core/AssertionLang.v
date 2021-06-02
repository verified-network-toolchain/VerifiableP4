Require Import Coq.ssr.ssrbool.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section AssertionLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition assertion := list (@Locator tags_t * Val).

Variable this : path.

Definition satisfies_unit (st : state) (a_unit : @Locator tags_t * Val) : Prop :=
  let (loc, v) := a_unit in
  loc_to_val this loc st = Some v.

Definition satisfies (st : state) (a : assertion) : Prop :=
  fold_right and True (map (satisfies_unit st) a).

Definition to_shallow_assertion (a : assertion) : state -> Prop :=
  fun st => satisfies st a.

Definition no_overlapping_unit (loc1 : @Locator tags_t) (a_unit2 : @Locator tags_t * Val) : bool :=
  (* let (loc1, _) := a_unit1 in *)
  let (loc2, _) := a_unit2 in
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => ~~ (path_equivb p1 p2)
  | _, _ => false
  end.

Fixpoint no_overlapping (loc : @Locator tags_t) (a : assertion) : bool :=
  match a with
  | hd :: tl => no_overlapping_unit loc hd && no_overlapping loc tl
  | [] => true
  end.

Definition is_instance (loc : @Locator tags_t) : bool :=
  match loc with
  | LInstance _ => true
  | LGlobal _ => false
  end.

Fixpoint wellformed (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      let (loc, _) := hd in
      is_instance loc && no_overlapping loc tl && wellformed tl
  | [] => true
  end.

Definition locator_equivb (loc1 loc2 : @Locator tags_t) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_equivb p1 p2
  | LGlobal p1, LGlobal p2 => path_equivb p1 p2
  | _, _ => false
  end.

Fixpoint update_val_by_loc (a : assertion) (loc : Locator) (v : Val) : assertion :=
  match a with
  | hd :: tl =>
      let (hd_loc, hd_v) := hd in
      if locator_equivb loc hd_loc then
        (hd_loc, v) :: tl
      else
        hd :: update_val_by_loc tl loc v
  | [] => [(loc, v)]
  end.

Axiom loc_to_val_update_val_by_loc_same : forall st p1 p2 v,
  path_equivb p1 p2 ->
  loc_to_val this (LInstance p1) (Semantics.update_val_by_loc this st (LInstance p2) v) = Some v.

Axiom loc_to_val_update_val_by_loc_different : forall st p1 p2 v,
  ~~ path_equivb p1 p2 ->
  loc_to_val this (LInstance p1) (Semantics.update_val_by_loc this st (LInstance p2) v) =
    loc_to_val this (LInstance p1) st.

Axiom path_equivb_refl : forall (p : path),
  path_equivb p p.

Axiom path_equivb_symm : forall (p1 p2 : path),
  path_equivb p1 p2 = path_equivb p2 p1.

Axiom path_equivb_trans : forall (p1 p2 p3 : path),
  path_equivb p1 p2 -> path_equivb p2 p3 -> path_equivb p1 p3.

Lemma update_val_by_loc_different st a loc v :
  no_overlapping loc a ->
  to_shallow_assertion a st ->
  to_shallow_assertion a (Semantics.update_val_by_loc this st loc v).
Proof.
  intros H_no_overlapping H_pre.
  induction a; intros.
  - sfirstorder.
  - split.
    + destruct a as [a_loc a_v]. simpl in *. destruct loc; destruct a_loc; only 1-3 : sfirstorder.
      rewrite loc_to_val_update_val_by_loc_different by (hauto use: path_equivb_symm unfold: negb, is_true, andb).
      sfirstorder.
    + apply IHa; [hauto b: on | sfirstorder].
Qed.

Lemma update_val_by_loc_different' st a loc v loc' :
  locator_equivb loc loc' ->
  no_overlapping loc' a ->
  to_shallow_assertion a st ->
  to_shallow_assertion a (Semantics.update_val_by_loc this st loc v).
Proof.
  intros H_equiv H_no_overlapping H_pre.
  induction a; intros.
  - sfirstorder.
  - split.
    + destruct a as [a_loc a_v]. simpl in *. destruct loc; destruct loc'; destruct a_loc; only 1-7 : sfirstorder.
      rewrite loc_to_val_update_val_by_loc_different by (
        simpl in H_equiv; hfcrush brefl: on use: path_equivb_symm, Reflect.negE, path_equivb_trans unfold: andb, is_true, negb).
      sfirstorder.
    + apply IHa; [hauto b: on | sfirstorder].
Qed.

Lemma update_val_by_loc_add st a loc v loc' :
  is_instance loc ->
  no_overlapping loc' a ->
  locator_equivb loc loc' ->
  to_shallow_assertion a st ->
  to_shallow_assertion ((loc', v) :: a) (Semantics.update_val_by_loc this st loc v).
Proof.
  intros H_no_overlapping H_pre.
  split; only 2 : (eapply update_val_by_loc_different'; hauto).
  destruct loc; destruct loc'; only 1-3 : sfirstorder.
  apply loc_to_val_update_val_by_loc_same; unfold locator_equivb in H0; srun eauto use: path_equivb_symm.
Qed.

Lemma update_val_by_loc_sound : forall st a loc v,
  wellformed a ->
  is_instance loc ->
  to_shallow_assertion a st ->
  to_shallow_assertion (update_val_by_loc a loc v) (Semantics.update_val_by_loc this st loc v).
Proof.
  intros * H_wellformed H_is_instance H_pre.
  destruct loc; only 1 : inversion H_is_instance.
  unfold to_shallow_assertion in *.
  induction a; intros.
  - unfold satisfies. repeat split.
    apply loc_to_val_update_val_by_loc_same. srun eauto use: path_equivb_refl.
  - destruct a as [hd_loc hd_v]. simpl. destruct hd_loc; only 1 : hauto lq: on.
    destruct (path_equivb p p0) eqn:H_path_equivb.
    + apply update_val_by_loc_add; only 2 : hauto b: on; sfirstorder.
    + split.
      * simpl. rewrite loc_to_val_update_val_by_loc_different by (hauto use: path_equivb_symm unfold: negb, is_true).
        sfirstorder.
      * apply IHa; [hauto b: on | sfirstorder].
Qed.

Fixpoint get_val (a : assertion) (loc : Locator) : option Val :=
  match a with
  | (hd_loc, hd_v) :: tl =>
      if locator_equivb hd_loc loc then Some hd_v else get_val tl loc
  | [] => None
  end.

(* This axiom is provable if tags_t is a unit type. *)
Axiom locator_equivb_eq : forall loc1 loc2, locator_equivb loc1 loc2 -> loc1 = loc2.

Lemma get_val_sound : forall st a loc v,
  wellformed a ->
  to_shallow_assertion a st ->
  get_val a loc = Some v ->
  loc_to_val this loc st = Some v.
Proof.
  intros * H_wellformed H_pre H_get_val.
  induction a as [ |hd tl].
  - inversion H_get_val.
  - destruct hd as [hd_loc hd_v].
    simpl in H_wellformed, H_get_val, H_pre.
    destruct (locator_equivb hd_loc loc) eqn:H_locator_equivb.
    + hnf in H_pre. erewrite <- (locator_equivb_eq _ loc) by (apply H_locator_equivb).
      sfirstorder.
    + apply IHtl; only 1: hauto b: on; sfirstorder.
Qed.

Definition eval_expr (a : assertion) (expr : Expression) :=
  eval_expr_gen (fun _ loc => get_val a loc) expr.

Definition eval_expr_gen_refine_statement get_val1 get_val2 (expr : @Expression tags_t) v :=
  (forall name loc v, get_val1 name loc = Some v -> get_val2 name loc = Some v) ->
  eval_expr_gen get_val1 expr = Some v ->
  eval_expr_gen get_val2 expr = Some v.

Lemma eval_expr_gen_refine get_val1 get_val2 (expr : @Expression tags_t) v :
  eval_expr_gen_refine_statement get_val1 get_val2 expr v
with eval_expr_gen_refine_preT get_val1 get_val2 tags expr typ dir v :
  eval_expr_gen_refine_statement get_val1 get_val2 (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_gen_refine_preT.
  - unfold eval_expr_gen_refine_statement. intros H_refine H_eval_expr_gen.
    destruct expr; inversion H_eval_expr_gen.
    + reflexivity.
    + hauto lq: on.
    + destruct (eval_expr_gen get_val1 arg) eqn:H_eval_arg; only 2 : inversion H1.
      assert (eval_expr_gen get_val2 arg = Some v0) by (eapply eval_expr_gen_refine; eauto).
      hauto lq: on.
    + destruct args as [larg rarg].
      destruct (eval_expr_gen get_val1 larg) eqn:H_eval_larg; only 2 : inversion H1.
      destruct (eval_expr_gen get_val1 rarg) eqn:H_eval_rarg; only 2 : inversion H1.
      assert (eval_expr_gen get_val2 larg = Some v0) by (eapply eval_expr_gen_refine; eauto).
      assert (eval_expr_gen get_val2 rarg = Some v1) by (eapply eval_expr_gen_refine; eauto).
      hauto lq: on.
Qed.

Lemma eval_expr_sound : forall ge_typ ge_senum st a expr v,
  wellformed a ->
  to_shallow_assertion a st ->
  eval_expr a expr = Some v ->
  exec_expr ge_typ ge_senum this st expr v.
Proof.
  intros * H_wellformed H_pre H_get_val.
  apply eval_expr_gen_sound.
  eapply eval_expr_gen_refine; only 2 : eassumption.
  intros *. simpl.
  apply get_val_sound; assumption.
Qed.

End AssertionLang.

