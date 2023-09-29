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

Definition p := ["pipe"; "egress"].

Open Scope func_spec.

Definition invalidate_field (h: Sval) (fld: ident): Sval :=
  (update fld (EvalBuiltin.setInvalid (get fld h)) h).

Definition invalidate_fields (h: Sval) (flds: list ident): Sval :=
  fold_left invalidate_field flds h.

Definition act_delete_sample_hdrs_fundef :=
  ltac:(get_fd ["SwitchEgress"; "act_delete_sample_hdrs"] ge).

Definition act_delete_sample_hdrs_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]]) [p]
    WITH (hsample : header_sample_rec),
      PRE
        (ARG []
        (MEM [(["hdr"], hdr hsample)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], invalidate_fields (hdr hsample) ["bridge"; "sample"])]
        (EXT []))).

Lemma act_delete_sample_hdrs_body:
  func_sound ge act_delete_sample_hdrs_fundef nil act_delete_sample_hdrs_spec.
Proof.
  start_function.
  do 3 step.
  entailer.
Qed.

Definition act_delete_packet_hdrs_fundef :=
  ltac:(get_fd ["SwitchEgress"; "act_delete_packet_hdrs"] ge).

Definition act_delete_packet_hdrs_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]]) [p]
    WITH hsample,
      PRE
        (ARG []
        (MEM [(["hdr"], hdr hsample)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], invalidate_fields (hdr hsample) ["bridge"; "ethernet"; "ipv4"])]
        (EXT []))).

Lemma act_delete_packet_hdrs_body:
  func_sound ge act_delete_packet_hdrs_fundef nil act_delete_packet_hdrs_spec.
Proof.
  start_function.
  do 4 step.
  entailer.
Qed.

Record egress_intrinsic_metadata_rec := {
    eg_intr_md_pad0: Val;
    eg_intr_md_egress_port: Val;
    eg_intr_md_pad1: Val;
    eg_intr_md_enq_qdepth: Val;
    eg_intr_md_pad2: Val;
    eg_intr_md_enq_congest_stat: Val;
    eg_intr_md_pad3: Val;
    eg_intr_md_enq_tstamp: Val;
    eg_intr_md_pad4: Val;
    eg_intr_md_deq_qdepth: Val;
    eg_intr_md_pad5: Val;
    eg_intr_md_deq_congest_stat: Val;
    eg_intr_md_app_pool_congest_stat: Val;
    eg_intr_md_pad6: Val;
    eg_intr_md_deq_timedelta: Val;
    eg_intr_md_egress_rid: Val;
    eg_intr_md_pad7: Val;
    eg_intr_md_egress_rid_first: Val;
    eg_intr_md_pad8: Val;
    eg_intr_md_egress_qid: Val;
    eg_intr_md_pad9: Val;
    eg_intr_md_egress_cos: Val;
    eg_intr_md_pad10: Val;
    eg_intr_md_deflection_flag: Val;
    eg_intr_md_pkt_length: Val }.

Definition eg_intr_md_rep (eg_intr_md: egress_intrinsic_metadata_rec): Val  :=
  ValBaseHeader
    [("_pad0", eg_intr_md_pad0 eg_intr_md);
     ("egress_port", eg_intr_md_egress_port eg_intr_md);
     ("_pad1", eg_intr_md_pad1 eg_intr_md);
     ("enq_qdepth", eg_intr_md_enq_qdepth eg_intr_md);
     ("_pad2", eg_intr_md_pad2 eg_intr_md);
     ("enq_congest_stat", eg_intr_md_enq_congest_stat eg_intr_md);
     ("_pad3", eg_intr_md_pad3 eg_intr_md);
     ("enq_tstamp", eg_intr_md_enq_tstamp eg_intr_md);
     ("_pad4", eg_intr_md_pad4 eg_intr_md);
     ("deq_qdepth", eg_intr_md_deq_qdepth eg_intr_md);
     ("_pad5", eg_intr_md_pad5 eg_intr_md);
     ("deq_congest_stat", eg_intr_md_deq_congest_stat eg_intr_md);
     ("app_pool_congest_stat", eg_intr_md_app_pool_congest_stat eg_intr_md);
     ("_pad6", eg_intr_md_pad6 eg_intr_md);
     ("deq_timedelta", eg_intr_md_deq_timedelta eg_intr_md);
     ("egress_rid", eg_intr_md_egress_rid eg_intr_md);
     ("_pad7", eg_intr_md_pad7 eg_intr_md);
     ("egress_rid_first", eg_intr_md_egress_rid_first eg_intr_md);
     ("_pad8", eg_intr_md_pad8 eg_intr_md);
     ("egress_qid", eg_intr_md_egress_qid eg_intr_md);
     ("_pad9", eg_intr_md_pad9 eg_intr_md);
     ("egress_cos", eg_intr_md_egress_cos eg_intr_md);
     ("_pad10", eg_intr_md_pad10 eg_intr_md);
     ("deflection_flag", eg_intr_md_deflection_flag eg_intr_md);
     ("pkt_length", eg_intr_md_pkt_length eg_intr_md)] true.

Definition egress_fd :=
  ltac:(get_fd ["SwitchEgress"; "apply"] ge).

Definition egress_rid_zero eg_intr_md: bool :=
  Val_eqb (eg_intr_md_egress_rid eg_intr_md) (P4BitV 16 0).

Definition conditional_update
  (eg_intr_md: egress_intrinsic_metadata_rec) hsample: Sval :=
  if egress_rid_zero eg_intr_md
  then invalidate_fields (hdr hsample) ["bridge"; "sample"]
  else invalidate_fields (hdr hsample) ["bridge"; "ethernet"; "ipv4"].

Definition egress_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH hsample eg_md eg_intr_md eg_intr_from_prsr eg_intr_md_for_dprsr
         eg_intr_md_for_oport,
      PRE
        (ARG [hdr hsample;
              eg_md;
              eval_val_to_sval (eg_intr_md_rep eg_intr_md);
              eg_intr_from_prsr;
              eg_intr_md_for_dprsr;
              eg_intr_md_for_oport]
        (MEM []
        (EXT [])))
      POST
      (ARG_RET [conditional_update eg_intr_md hsample;
                eg_md; eg_intr_md_for_dprsr; eg_intr_md_for_oport]
           ValBaseNull
        (MEM []
        (EXT []))).

Lemma egress_body:
  func_sound ge egress_fd nil egress_spec.
Proof.
  start_function.
  step_if; change (P4Bit _ _) with (eval_val_to_sval (P4BitV 16 0)) in H;
    simpl get in H; unfold abs_eq, build_abs_binary_op in H;
    rewrite !eval_sval_to_val_eq in H.
  - apply is_sval_true_binary_op_eq in H.
    change (Val_eqb _ _) with (egress_rid_zero eg_intr_md) in H.
    unfold conditional_update. rewrite H.
    step.
    step_call act_delete_sample_hdrs_body; [entailer|].
    step. entailer.
  - apply is_sval_false_binary_op_eq in H.
    change (Val_eqb _ _) with (egress_rid_zero eg_intr_md) in H.
    unfold conditional_update. rewrite H.
    step.
    step_call act_delete_packet_hdrs_body; [entailer|].
    step. entailer.
Qed.
