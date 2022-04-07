Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.UseTofino.
Require ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.AbsFilter.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.ExtPred.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Section FilterRepr.

Variable (p : path).

Definition row_ge : genv -> Prop.
Admitted.

Definition row_inv_bare : extern_state -> Prop.
Admitted.

Lemma row_inv_wellformed : ep_wellformed_prop [p] row_inv_bare.
Admitted.

Definition row_inv : ext_pred :=
  mk_ext_pred' row_inv_bare [p] row_inv_wellformed.

Definition bool_to_val (b : bool) : ValueBase :=
  ValBaseBit [b; false; false; false; false; false; false; false].

Definition row_reg_repr (cr : ConFilter.row) : ext_pred :=
  ExtPred.singleton (p ++ ["reg_row"]) (Tofino.ObjRegister (map bool_to_val cr)).

Program Definition row_repr (cr : ConFilter.row) : ext_pred :=
  ExtPred.wrap [p] (ExtPred.and row_inv (row_reg_repr cr)) _.
Next Obligation.
Admitted.
