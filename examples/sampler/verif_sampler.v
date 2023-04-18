Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"].

Open Scope func_spec.

Definition regact_count_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_count"])).

Definition regact_count_execute_body :=
  ltac:(build_execute_body ge regact_count_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_count_execute_body) : func_specs.

Definition act_count_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_count"] ge).

Definition act_count_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) [p]
    WITH (counter : Z),
      PRE
        (ARG []
        (MEM [(["ig_md"], ValBaseStruct [("num_pkts", P4Bit_ 32)])]
        (EXT [counter_repr p counter])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], ValBaseStruct [("num_pkts", P4Bit 32 (counter + 1))])]
        (EXT [counter_repr p (counter + 1)]))).

Lemma act_count_body:
  func_sound ge act_count_fundef nil act_count_spec.
Proof.
  start_function.
  unfold counter_repr, counter_reg_repr.
  normalize_EXT.
  Intros_prop. simpl.
  step_call regact_count_execute_body;
    [entailer | list_solve | lia | reflexivity |].
  step.
  entailer.
  repeat intro. hnf. simpl. lia.
Qed.

Definition act_sample_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_sample"] ge).

Definition act_sample_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_tm_md"]]) [p]
    WITH hdr,
      PRE
        (ARG []
        (MEM [(["hdr"], hdr)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], update "bridge" (bridge_repr 1) hdr)]
        (EXT []))).

Lemma act_sample_body:
  func_sound ge act_sample_fundef nil act_sample_spec.
Proof.
  start_function.
  do 7 step.
Abort.
