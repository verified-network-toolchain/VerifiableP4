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
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition assertion := list (Lval * Val).

Variable this : path.

Definition sem_eval_read (st : state) (lv : Lval) : option Val :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ =>
      loc_to_val this loc st
  | _ => None
  end.

Lemma sem_eval_read_sound : forall st lv v,
  sem_eval_read st lv = Some v ->
  forall v', exec_read this st lv v' ->
    v' = v.
Admitted.

Definition satisfies_unit (st : state) (a_unit : Lval * Val) : Prop :=
  let (lv, v) := a_unit in
  sem_eval_read st lv = Some v.

Definition satisfies (st : state) (a : assertion) : Prop :=
  fold_right and True (map (satisfies_unit st) a).

Definition to_shallow_assertion (a : assertion) : state -> Prop :=
  fun st => satisfies st a.

Definition loc_no_overlapping (loc1 : Locator) (loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => ~~ (path_equivb p1 p2)
  | _, _ => false
  end.

Definition lval_no_overlapping (lv1 : Lval) (lv2 : Lval) : bool :=
  match lv1, lv2 with
  | MkValueLvalue (ValLeftName _ loc1) _, MkValueLvalue (ValLeftName _ loc2) _ =>
      loc_no_overlapping loc1 loc2
  | _, _ => false
  end.

Fixpoint no_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl => lval_no_overlapping lv (fst hd) && no_overlapping lv tl
  | [] => true
  end.

Definition is_instance (loc : Locator) : bool :=
  match loc with
  | LInstance _ => true
  | LGlobal _ => false
  end.

Definition is_lval_loc_instance (lv : Lval) : bool :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ =>
      is_instance loc
  | _ => false
  end.

Fixpoint wellformed (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      let (lv, _) := hd in
      is_lval_loc_instance lv && no_overlapping lv tl && wellformed tl
  | [] => true
  end.

Definition locator_equivb (loc1 loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_equivb p1 p2
  | LGlobal p1, LGlobal p2 => path_equivb p1 p2
  | _, _ => false
  end.

Definition lval_equivb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | MkValueLvalue (ValLeftName _ loc1) _, MkValueLvalue (ValLeftName _ loc2) _ =>
      locator_equivb loc1 loc2
  | _, _ => false
  end.

Fixpoint eval_write (a : assertion) (lv : Lval) (v : Val) : assertion :=
  match a with
  | hd :: tl =>
      let (hd_lv, hd_v) := hd in
      if lval_equivb lv hd_lv then
        (lv, v) :: tl
      else
        hd :: eval_write tl lv v
  | [] => [(lv, v)]
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

Axiom loc_no_overlapping_symm : forall (loc1 loc2 : Locator),
  loc_no_overlapping loc1 loc2 = loc_no_overlapping loc2 loc1.

Axiom lval_no_overlapping_symm : forall (lv1 lv2 : Lval),
  lval_no_overlapping lv1 lv2 = lval_no_overlapping lv2 lv1.

Lemma exec_write_no_overlapping_unit st lv1 v1 lv2 v2 st' :
  lval_no_overlapping lv1 lv2 ->
  satisfies_unit st (lv1, v1) ->
  exec_write this st lv2 v2 st' ->
  satisfies_unit st' (lv1, v1).
Proof.
  intros H_no_overlapping H_pre H_exec.
  destruct lv1 as [[? loc1 | | |] ?]; only 2-4 : sfirstorder.
  destruct lv2 as [[? loc2 | | |] ?]; only 2-4 : sfirstorder.
  inversion H_exec; subst. simpl.
  destruct loc1; only 1 : sfirstorder.
  destruct loc2; only 1 : sfirstorder.
  rewrite loc_to_val_update_val_by_loc_different by sfirstorder.
  apply H_pre.
Qed.

Lemma exec_write_no_overlapping st a lv v st' :
  no_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st lv v st' ->
  to_shallow_assertion a st'.
Proof.
  intros H_no_overlapping H_pre H_exec.
  induction a as [ | hd tl]; intros.
  - sfirstorder.
  - split.
    + destruct hd as [a_lv a_v].
      eapply (exec_write_no_overlapping_unit st _ _ lv v).
      * rewrite lval_no_overlapping_symm. hauto b: on.
      * sfirstorder.
      * sfirstorder.
    + apply IHtl.
      * hauto b: on.
      * sfirstorder.
Qed.

Lemma exec_write_same st lv v st' :
  is_lval_loc_instance lv ->
  exec_write this st lv v st' ->
  satisfies_unit st' (lv, v).
Proof.
  intros H_is_lval_loc_instance H_exec_write.
  simpl. destruct lv as [[? loc | | |] ?]; only 2-4 : sfirstorder.
  inversion H_exec_write; subst.
  simpl. destruct loc; only 1 : sfirstorder.
  apply loc_to_val_update_val_by_loc_same.
  apply path_equivb_refl.
Qed.

Lemma eval_write_add st a lv v st':
  is_lval_loc_instance lv ->
  no_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st lv v st' ->
  to_shallow_assertion ((lv, v) :: a) st'.
Proof.
  intros H_is_lval_loc_instance H_no_overlapping H_pre H_exec_write.
  split.
  - eapply exec_write_same; eassumption.
  - apply (exec_write_no_overlapping st _ lv v); sfirstorder.
Qed.

Fixpoint no_nequiv_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      if lval_equivb lv (fst hd) then
        no_overlapping lv tl
      else
        lval_no_overlapping lv (fst hd) && no_nequiv_overlapping lv tl
  | [] => true
  end.

Lemma eval_write_sound : forall st a lv v st',
  wellformed a ->
  is_lval_loc_instance lv ->
  no_nequiv_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st lv v st' ->
  to_shallow_assertion (eval_write a lv v) st'.
Proof.
  intros * H_wellformed H_is_lval_loc_instance H_no_nequiv_overlapping H_pre H_exec_write.
  induction a as [ | hd tl]; intros.
  - eapply eval_write_add; eassumption.
  - destruct hd as [hd_lv hd_v].
    simpl in H_no_nequiv_overlapping |- *. destruct (lval_equivb lv hd_lv) eqn:H_lval_equivb.
    + eapply eval_write_add with (st := st); sfirstorder.
    + split.
      * refine (exec_write_no_overlapping_unit _ _ _ _ _ _ _ _ H_exec_write); only 2 : sfirstorder.
        hauto use: lval_no_overlapping_symm unfold: is_true, andb.
      * apply IHtl; only 3 : sfirstorder; hauto b: on.
Qed.

Fixpoint eval_read (a : assertion) (lv : Lval) : option Val :=
  match a with
  | (hd_lv, hd_v) :: tl =>
      if lval_equivb hd_lv lv then Some hd_v else eval_read tl lv
  | [] => None
  end.

(* This axiom is provable if tags_t is a unit type. *)
Axiom locator_equivb_eq : forall loc1 loc2, locator_equivb loc1 loc2 -> loc1 = loc2.

Axiom lval_equivb_eq : forall lv1 lv2, lval_equivb lv1 lv2 -> lv1 = lv2.

Lemma eval_read_sound : forall st a lv v,
  to_shallow_assertion a st ->
  eval_read a lv = Some v ->
  sem_eval_read st lv = Some v.
Proof.
  intros * H_pre H_eval_read.
  induction a as [ | hd tl].
  - inversion H_eval_read.
  - destruct hd as [hd_lv hd_v].
    simpl in H_pre, H_eval_read.
    destruct (lval_equivb hd_lv lv) eqn:H_lval_equivb.
    + erewrite <- (lval_equivb_eq _ lv) by (apply H_lval_equivb).
      sfirstorder.
    + apply IHtl; sfirstorder.
Qed.

End AssertionLang.

