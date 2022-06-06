Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.UseTofino.
Require ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.ExtPred.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Section FilterRepr.

Context {num_rows num_slots : Z}.

Definition bool_to_val (b : bool) : ValueBase :=
  ValBaseBit [b; false; false; false; false; false; false; false].

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

End FilterRepr.
