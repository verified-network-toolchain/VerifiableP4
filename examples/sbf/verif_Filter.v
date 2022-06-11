Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import ProD3.examples.sbf.verif_Win1.
Require Import ProD3.examples.sbf.verif_Win2.
Require Import ProD3.examples.sbf.verif_Win3.
Require Import ProD3.examples.sbf.verif_Win4.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "bf2_ds"].

Definition Filter_fundef :=
  ltac:(get_fd ["Bf2BloomFilter"; "apply"] ge).

Definition regact_clear_index_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_index"; "apply"]) ge).

Definition regact_clear_index_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear_index"]) (fun i => ValBaseBit (P4Arith.to_lbool 32 i))
    (fun i => i + 1) (fun i => P4Bit 32 i).

Lemma regact_clear_index_apply_body :
  func_sound am_ge regact_clear_index_apply_fd nil regact_clear_index_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
  { red.
    fold abs_plus.
    unfold eval_p4int_sval.
    cbn [width_signed].
    change (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 32 old_value)))
      with (ValBaseBit (P4Arith.to_loptbool 32 old_value)).
    rewrite abs_plus_bit.
    apply sval_refine_refl.
  }
Qed.

Definition regact_clear_index_execute_body :=
  ltac:(build_execute_body ge regact_clear_index_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_clear_index_execute_body) : func_specs.

Definition act_clear_index_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_clear_index"] ge).

Definition act_clear_index_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_clear_index"; "t'3"]]) [p ++ ["reg_clear_index"]]
    WITH (i : Z) (ds_md : Sval)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [fil_clear_index_repr p 18 i])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "clear_index_1" (P4Bit 18 i) ds_md)]
        (EXT [fil_clear_index_repr p 18 (update_clear_index (num_slots := num_slots) i)]))).

Lemma in_scopes_split : forall ps1 ps2 ps3 ps4,
  forallb (fun p : path => in_scopes p ps1) ps3 ->
  forallb (fun p : path => in_scopes p ps2) ps4 ->
  forallb (fun p : path => in_scopes p (ps1 ++ ps2)) (ps3 ++ ps4).
Proof.
  intros.
  rewrite forallb_app, Reflect.andE; split.
Admitted.

Lemma in_scopes_refl : forall ps,
  forallb (fun p : path => in_scopes p ps) ps.
Proof.
Admitted.

Lemma ex_and_l : forall {A} (ep1 : A -> ext_pred) ps H ep2,
  ExtPred.equiv
    (ExtPred.and (ExtPred.ex ep1 ps H) ep2)
    (ExtPred.ex (fun x => ExtPred.and (ep1 x) ep2) (ps ++ ep_paths ep2) (fun x => in_scopes_split _ _ _ _ (H x) (in_scopes_refl _))).
Proof.
  intros. red. simpl. clear H.
  apply functional_extensionality; intros.
  apply prop_ext.
  sauto.
Qed.

Lemma ex_and_3 : forall {A} ep1 (ep2 : A -> ext_pred) ps H,
  ExtPred.equiv
    (ExtPred.and ep1 (ExtPred.ex ep2 ps H))
    (ExtPred.ex (fun x => ExtPred.and ep1 (ep2 x)) (ep_paths ep1 ++ ps) (fun x => in_scopes_split _ _ _ _ (in_scopes_refl _) (H x))).
Proof.
  intros. red. simpl. clear H.
  apply functional_extensionality; intros.
  apply prop_ext.
  sauto.
Qed.

Fixpoint replace_nth {A} (n : nat) (al : list A) (x : A) {struct n} : list A :=
  match n, al with
  | O, a :: al => x :: al
  | S n', a :: al' => a :: replace_nth n' al' x
  | _, nil => nil
  end.

Lemma extract_nth_ext_ex : forall n a_mem a_ext {A} (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  MEM a_mem (EXT a_ext) =
    (EX (x : A), MEM a_mem (EXT (replace_nth n a_ext (S x))))%assr.
Proof.
  intros.
  transitivity (MEM a_mem (fun es => exists x, EXT (replace_nth n a_ext (S x)) es)).
  - f_equal.
    clear -H0.
    generalize dependent n; induction a_ext; intros.
    + extensionality es.
      apply prop_ext.
      split; only 2 : hauto lq: on.
      intros _.
      replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H0. 2 : {
        destruct n; auto.
      }
      assert (exists x, S x es). {
        change (ExtPred.ex S ep H es).
        rewrite <- H0.
        exact I.
      }
      destruct H1 as [x ?].
      exists x. unfold replace_nth; destruct n; sauto q: on.
    + destruct n.
      * simpl in H0. rewrite H0.
        clear.
        extensionality es.
        apply prop_ext.
        simpl.
        sauto.
      * specialize (IHa_ext _ H0).
        change (EXT (a :: a_ext)) with (fun es => a es /\ EXT a_ext es).
        rewrite IHa_ext.
        clear.
        extensionality es.
        apply prop_ext.
        simpl. fcrush.
  - clear.
    extensionality s.
    apply prop_ext.
    sauto.
Qed.

Ltac extract_ex_in_EXT a :=
  lazymatch a with
  | MEM _ (EXT ?a_ext) =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_ext_ex n' _ a_ext A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Ltac Intros' x :=
  lazymatch goal with
  | |- hoare_block _ _ ?pre _ _ =>
      extract_ex_in_EXT pre;
      eapply hoare_block_pre_ex;
      intro x
  end.

Lemma act_clear_index_body :
  func_sound ge act_clear_index_fd nil act_clear_index_spec.
Proof.
  start_function.
  unfold fil_clear_index_repr.
  Intros' i'.
  normalize_EXT.
  step_call regact_clear_index_execute_body.
  { entailer. }
  { reflexivity. }
  { simpl; lia. }
  { simpl. list_solve. }
  cbn.
  eapply hoare_block_cons.
  { eapply hoare_stmt_assign'.
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { Fail reflexivity.
Abort.
