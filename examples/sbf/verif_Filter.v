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
