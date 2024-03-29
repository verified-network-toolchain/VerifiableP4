Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "ingress_deparser"].

Definition deparser_fundef :=
  ltac:(get_fd ["SwitchIngressDeparser"; "apply"] ge).

Definition deparser_spec: func_spec :=
  WITH,
    PATH p
    MOD None [["packet_out"]]
    WITH (pout : packet_out) hdr ig_md ig_intr_dpprsr_md
         (_: ⊢ᵥ hdr \: header_sample_t),
      PRE
        (ARG [val_to_sval_valid_only hdr; ig_md; ig_intr_dpprsr_md]
        (MEM []
        (EXT [ExtPred.singleton ["packet_out"] (ObjPout pout)])))
      POST
        (ARG_RET [val_to_sval_valid_only hdr] ValBaseNull
           (MEM []
              (EXT [ExtPred.singleton ["packet_out"]
                      (ObjPout (pout ++ encode hdr))]))).

Lemma ingress_deparser_body:
  func_sound ge deparser_fundef nil deparser_spec.
Proof.
  start_function.
  step_call (@packet_out_emit_body Info); [entailer | eapply emit_encode; eauto|].
  step. entailer.
Qed.
