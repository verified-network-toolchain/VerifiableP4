Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "egress_parser"; "tofino_parser"].

Open Scope func_spec.

Definition tofino_parser_start_fundef :=
  ltac:(get_fd ["TofinoEgressParser"; "start"] ge).

Definition tofino_parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["eg_intr_md"]]) [["packet_in"]]
    WITH (pin: packet_in) eg_intr_md pin'
         (_: ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t)
         (_: pin ⫢ [⦑ encode eg_intr_md ⦒; ⦑pin'⦒]),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["eg_intr_md"], eval_val_to_sval eg_intr_md)]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma tofino_parser_start_body:
  func_sound ge tofino_parser_start_fundef nil
    tofino_parser_start_spec.
Proof.
  start_function.
  do 3 simpl_format_list.
  rewrite app_nil_r.
  step_call (@packet_in_extract_body Info);
    [entailer | apply extract_encode; [assumption | reflexivity] |].
  step_call (@parser_accept_body Info); [entailer |].
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tofino_parser_start_body) : func_specs.

Definition tofino_parser_fundef :=
  ltac:(get_fd ["TofinoEgressParser"; "apply"] ge).

Definition tofino_parser_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["eg_intr_md"]]) [["packet_in"]]
    WITH (pin: packet_in) eg_intr_md pin'
         (_: ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t)
         (_: pin ⫢ [⦑ encode eg_intr_md ⦒; ⦑pin'⦒]),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [eval_val_to_sval eg_intr_md] ValBaseNull
        (MEM []
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma tofino_parser_body:
  func_sound ge tofino_parser_fundef nil tofino_parser_spec.
Proof.
  start_function.
  step.
  step_call tofino_parser_start_body; [ entailer | apply H | apply H0 | ].
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tofino_parser_body) : func_specs.
