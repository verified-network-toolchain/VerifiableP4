Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.count.common.
Require Import ProD3.examples.count.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"].

Open Scope func_spec.

Definition regact_counter_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_counter"])).

Definition regact_counter_execute_body :=
  ltac:(build_execute_body ge regact_counter_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_counter_execute_body) : func_specs.

Definition counter_act_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_counter"] ge).

Definition counter_act_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) [p]
    WITH (counter : Z),
      PRE
        (ARG []
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit_ 32)])]
        (EXT [counter_repr p counter])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit 32 (counter + 1))])]
        (EXT [counter_repr p (counter + 1)]))).

Lemma counter_act_body:
  func_sound ge counter_act_fundef nil counter_act_spec.
Proof.
  start_function.
  unfold counter_repr, counter_reg_repr.
  normalize_EXT.
  Intros_prop. simpl.
  step_call regact_counter_execute_body;
    [entailer | list_solve | lia | reflexivity |].
  step.
  entailer.
  repeat intro. hnf. simpl. lia.
Qed.

Definition tbl_counter_fd :=
  ltac:(get_fd ["SwitchIngress"; "tbl_counter"; "apply"] ge).

Definition tbl_counter_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) [p]
    WITH (counter : Z),
      PRE
        (ARG []
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit_ 32)])]
        (EXT [counter_repr p counter])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit 32 (counter + 1))])]
        (EXT [counter_repr p (counter + 1)]))))%arg_ret_assr.

Lemma tbl_counter_body:
  func_sound ge tbl_counter_fd nil tbl_counter_spec.
Proof.
  start_function.
  table_action counter_act_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_counter_body) : func_specs.


Definition Ingress_fd :=
  ltac:(get_fd ["SwitchIngress"; "apply"] ge).

Definition Ingress_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]; ["ig_intr_dprsr_md"]]) [p]
    WITH (counter : Z) (dprsr_md: Sval),
      PRE
        (ARG []
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit_ 32)]);
              (["ig_intr_dprsr_md"], dprsr_md)]
        (EXT [counter_repr p counter])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], ValBaseStruct [("num_pkt", P4Bit 32 (counter + 1))]);
              (["ig_intr_dprsr_md"],
                if (Z.eqb 0 ((counter + 1) mod 1024)) then dprsr_md
                else (update "digest_type" (P4Bit 3 1) dprsr_md))]
        (EXT [counter_repr p (counter + 1)]))).

Lemma Ingress_body:
  func_sound ge Ingress_fd nil Ingress_spec.
Proof.
  (* start_function. *)
Abort.
