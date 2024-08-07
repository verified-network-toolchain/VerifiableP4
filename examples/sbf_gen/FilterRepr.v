Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf_gen.Utils.
Require Import ProD3.examples.sbf_gen.ConFilter.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Import ListNotations.
Open Scope list_scope.

Section FilterRepr.

Notation ident := string.
Notation path := (list ident).

Context {num_frames num_rows num_slots frame_tick_tocks : Z}.

Definition bool_to_val (b : bool) : ValueBase :=
  ValBaseBit (P4Arith.to_lbool 8 (Z.b2z b)).

Definition row_reg_repr (p : path) (cr : ConFilter.row num_slots) : ext_pred :=
  ExtPred.singleton (p ++ ["reg_row"]) (Tofino.ObjRegister (map bool_to_val (proj1_sig cr))).

Program Definition row_repr (p : path) (cr : ConFilter.row num_slots) : ext_pred :=
  ExtPred.wrap [p] [row_reg_repr p cr] _.
Next Obligation.
  unfold in_scope.
  rewrite <- (app_nil_r p) at 1.
  rewrite is_prefix_cancel. auto.
Qed.

Program Definition frame_repr (p : path) (rows : list string) (cf : ConFilter.frame num_rows num_slots) : ext_pred :=
  ExtPred.wrap [p] (map2 (fun row cr => row_repr (p ++ [row]) cr) rows cf) _.
Next Obligation.
  unfold map2. generalize (combine rows (proj1_sig cf)) as rows_cf.
  clear; intros.
  induction rows_cf; auto.
  destruct a.
  simpl.
  rewrite IHrows_cf.
  unfold in_scope.
  rewrite <- (app_nil_r p) at 1.
  rewrite is_prefix_cancel. auto.
Qed.

Program Definition fil_clear_index_repr (p : path) (w : N) (i : Z) : ext_pred :=
  ExtPred.ex (fun i' =>
    ExtPred.and
      (ExtPred.singleton (p ++ ["reg_clear_index"])
        (Tofino.ObjRegister [ValBaseBit (P4Arith.to_lbool 32 i')]))
      (ExtPred.prop (i' mod (2 ^ (Z.of_N w)) = i)))
    [p ++ ["reg_clear_index"]] _.
Next Obligation.
  unfold in_scope.
  rewrite is_prefix_refl.
  auto.
Qed.

Definition timer_repr_sval (t : Z * bool) :=
  ValBaseStruct [("lo", P4Bit 16 (Z.b2z (snd t)));
                 ("hi", P4Bit 16 (fst t))].

Definition timer_repr_val (t : Z * bool) :=
  force_sval_to_val (timer_repr_sval t).

Definition timer_repr (p : path) (t : Z * bool) : ext_pred :=
  ExtPred.and
    (ExtPred.prop (timer_wf num_frames frame_tick_tocks t))
    (ExtPred.singleton (p ++ ["reg_clear_window"])
          (Tofino.ObjRegister [timer_repr_val t])).

Program Definition filter_repr (p : path) (w : N) (panes : list string) (rows : list string) (cf : ConFilter.filter num_frames num_rows num_slots) : ext_pred :=
  ExtPred.wrap [p] (
    let 'mk_filter pns clear_index timer := cf in
    map2 (fun pane cpa => frame_repr (p ++ [pane]) rows cpa) panes pns ++
    [fil_clear_index_repr p w clear_index] ++
    [timer_repr p timer]) _.
Next Obligation.
  destruct cf as [pns clear_index timer].
  rewrite forallb_app, Reflect.andE; split.
  2 : simpl; rewrite Reflect.andE; split.
  - unfold map2. generalize (combine panes (proj1_sig pns)) as panes_pns.
    clear; intros.
    induction panes_pns; auto.
    destruct a.
    simpl.
    rewrite IHpanes_pns.
    unfold in_scope.
    rewrite <- (app_nil_r p) at 1.
    rewrite is_prefix_cancel. auto.
  - unfold in_scope.
    rewrite <- (app_nil_r p) at 1.
    rewrite is_prefix_cancel. auto.
  - unfold in_scope.
    rewrite <- (app_nil_r p) at 1.
    rewrite is_prefix_cancel. auto.
Qed.

End FilterRepr.
