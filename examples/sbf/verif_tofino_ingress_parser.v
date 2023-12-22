Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "ingress_parser"; "tofino_parser"].

Open Scope func_spec.

Definition tofino_parser_port_metadata_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_port_metadata"] ge).

Definition tofino_parser_port_metadata_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some []) [["packet_in"]]
    WITH (pin pin': packet_in) (_: pin ⫢ [⟨64⟩; ⦑pin'⦒]),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

(* Unset Printing Notations. *)

Lemma tofino_parser_port_metadata_body:
  func_sound ge tofino_parser_port_metadata_fundef nil
    tofino_parser_port_metadata_spec.
Proof.
  start_function.
  step_call (@packet_in_advance_body Info);
    [ entailer; instantiate (1 := 64); apply sval_refine_refl |
      lia | apply format_match_size in H; assumption | ].
  apply format_match_skipn in H. change (Z.to_nat 64) with 64%nat. rewrite H.
  step_call (@parser_accept_body Info); [entailer |].
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tofino_parser_port_metadata_body) : func_specs.

Definition tofino_parser_resubmit_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_resubmit"] ge).

Definition tofino_parser_resubmit_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some []) [["packet_in"]]
    WITH (pin: packet_in) (_: 64 <= Zlength pin) (_: False),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin (skipn 64 pin))]))).

Lemma tofino_parser_resubmit_body:
  func_sound ge tofino_parser_resubmit_fundef nil
    tofino_parser_resubmit_spec.
Proof.
  start_function.
  step_call (@packet_in_advance_body Info);
    [ entailer; instantiate (1 := 64); apply sval_refine_refl |
      lia | assumption | ].
  step_call (@parser_reject_body Info); [entailer | assumption |].
  step. entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tofino_parser_resubmit_body) : func_specs.

Definition tofino_parser_start_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "start"] ge).

Definition iimt_repr_sval (flag version port stamp: Z): Sval :=
  ValBaseHeader
    [("resubmit_flag", P4Bit 1 flag);
     ("_pad1", P4Bit 1 0);
     ("packet_version", P4Bit 2 version);
     ("_pad2", P4Bit 3 0);
     ("ingress_port", P4Bit 9 port);
     ("ingress_mac_tstamp", P4Bit 48 stamp)] (Some true).

Definition iimt_repr_val (flag version port stamp: Z) : Val :=
  ValBaseHeader
    [("resubmit_flag", P4BitV 1 flag);
     ("_pad1", P4BitV 1 0);
     ("packet_version", P4BitV 2 version);
     ("_pad2", P4BitV 3 0);
     ("ingress_port", P4BitV 9 port);
     ("ingress_mac_tstamp", P4BitV 48 stamp)] true.

Lemma iimt_repr_eq: forall flag ver port stamp,
    eval_val_to_sval (iimt_repr_val flag ver port stamp) =
      iimt_repr_sval flag ver port stamp.
Proof.
  intros. rewrite <- val_to_sval_iff.
  unfold iimt_repr_val, iimt_repr_sval.
  repeat constructor.
Qed.

Definition tofino_parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["ig_intr_md"]]) [["packet_in"]]
    WITH (pin: packet_in) ver port stamp pin'
         (_: ⊫ᵥ iimt_repr_val 0 ver port stamp \:
               ingress_intrinsic_metadata_t)
         (_: pin ⫢ [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒; ⟨64⟩; ⦑pin'⦒]),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_intr_md"], (iimt_repr_sval 0 ver port stamp))]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma tofino_parser_start_body:
  func_sound ge tofino_parser_start_fundef nil
    tofino_parser_start_spec.
Proof.
  start_function.
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [entailer | apply extract_encode; [assumption | reflexivity] |].
  step_if; simpl in H0. 1: exfalso; auto.
  clear H0. step_if; simpl in H0. 2: exfalso; auto.
  rewrite iimt_repr_eq.
  step_call tofino_parser_port_metadata_body; eauto. entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tofino_parser_start_body) : func_specs.

Definition tofino_parser_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "apply"] ge).

Definition tofino_parser_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["ig_intr_md"]]) [["packet_in"]]
    WITH (pin: packet_in) ver port stamp pin'
         (_: ⊫ᵥ iimt_repr_val 0 ver port stamp \: ingress_intrinsic_metadata_t)
         (_: pin ⫢ [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒; ⟨64⟩; ⦑pin'⦒]),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [iimt_repr_sval 0 ver port stamp] ValBaseNull
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
