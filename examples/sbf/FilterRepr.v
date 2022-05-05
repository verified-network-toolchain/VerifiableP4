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

Variable (p : path).

(* This is probably computable from the program, but we manually write it now. *)
(* Definition row_ge (ge : genv) : Prop :=
  PathMap.get (p ++ ["reg_row"]) ge = EnvRegister. *)

(* It seems we don't need this part, because constant table entries are not in extern_state. *)
(* Definition row_inv_bare : extern_state -> Prop.
Admitted.

Lemma row_inv_wellformed : ep_wellformed_prop [p] row_inv_bare.
Admitted.

Definition row_inv : ext_pred :=
  mk_ext_pred' row_inv_bare [p] row_inv_wellformed. *)

Definition bool_to_val (b : bool) : ValueBase :=
  ValBaseBit [b; false; false; false; false; false; false; false].

Definition row_reg_repr (cr : ConFilter.row) : ext_pred :=
  ExtPred.singleton (p ++ ["reg_row"]) (Tofino.ObjRegister (map bool_to_val cr)).

Program Definition row_repr (cr : ConFilter.row) : ext_pred :=
  ExtPred.wrap [p] [row_reg_repr cr] _.
Next Obligation.
  unfold in_scope.
  rewrite <- (app_nil_r p) at 1.
  rewrite is_prefix_cancel. auto.
Qed.

End FilterRepr.
