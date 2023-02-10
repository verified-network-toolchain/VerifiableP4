Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Import ListNotations.
Open Scope list_scope.


Notation ident := string.
Notation path := (list ident).

Definition Z_to_val (i: Z): ValueBase := ValBaseBit (P4Arith.to_lbool 32 i).

Definition counter_reg_repr (p : path) (counter : Z) : ext_pred :=
  ExtPred.and
    (ExtPred.singleton (p ++ ["reg_counter"])
       (Tofino.ObjRegister [Z_to_val counter]))
    (ExtPred.prop (0 <= counter)).

Program Definition counter_repr (p : path) (counter : Z) : ext_pred :=
  ExtPred.wrap [p] [counter_reg_repr p counter] _.
Next Obligation.
  unfold in_scope.
  rewrite <- (app_nil_r p) at 1.
  rewrite is_prefix_cancel. auto.
Qed.
