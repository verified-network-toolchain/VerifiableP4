Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress_parser"].

Open Scope func_spec.

Definition tofino_parser_port_metadata_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_port_metadata"] ge).

Definition tofino_parser_port_metadata_spec: func_spec :=
  WITH,
    PATH p
    MOD None [["packet_in"]]
    WITH (pin: packet_in) (_: 64 < Zlength pin),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin (skipn 64 pin))]))).

(* Unset Printing Notations. *)

Lemma tofino_parser_port_metadata_body:
  func_sound ge tofino_parser_port_metadata_fundef nil
    tofino_parser_port_metadata_spec.
Proof.
  start_function.
  step_call (@packet_in_advance_body Info);
    [ entailer; instantiate (1 := 64); apply sval_refine_refl |
      lia | assumption | ].
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
    MOD None [["packet_in"]]
    WITH (pin: packet_in) (_: 64 < Zlength pin) (_: False),
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
  step_call (parser_reject_body ge ge); [entailer | assumption |].
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

Definition P4BitV (w : N) (v : Z) : Val :=
  ValBaseBit (P4Arith.to_lbool w v).

Definition iimt_repr_val (flag version port stamp: Z) : Val :=
  ValBaseHeader
    [("resubmit_flag", P4BitV 1 flag);
     ("_pad1", P4BitV 1 0);
     ("packet_version", P4BitV 2 version);
     ("_pad2", P4BitV 3 0);
     ("ingress_port", P4BitV 9 port);
     ("ingress_mac_tstamp", P4BitV 48 stamp)] true.

Definition tofino_parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD None [["packet_in"]]
    WITH (pin: packet_in) ver port stamp pin'
         (_: extract ingress_intrinsic_metadata_t pin =
             Some (iimt_repr_val 0 ver port stamp, SReturnNull, pin'))
         (_: 64 < Zlength pin'),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin (skipn 64 pin'))]))).

Lemma tofino_parser_start_body:
  func_sound ge tofino_parser_start_fundef nil
    tofino_parser_start_spec.
Proof.
  start_function.
  - step_call (@packet_in_extract_body Info); [entailer | apply H |].
    step_if.
    + simpl get in H1. exfalso; auto.
    + simpl Ops.eval_cast in H1.
      simpl get in H1. simpl build_abs_unary_op in H1.
      unfold build_abs_unary_op in H1. simpl eval_sval_to_val in H1.
      simpl in H1. exfalso. assumption.
  - apply func_modifies_internal.
    apply Forall_nil.
    simple apply @block_modifies_cons.
    + eauto 300 with nocore modifies.
    + simple apply @block_modifies_cons.
      simple apply @stmt_modifies_if.
      simple eapply @stmt_modifies_method_call.
      simple eapply @call_modifies_func; try eauto 300 with nocore modifies.
      simpl.
(*
 simple eapply @stmt_modifies_assign
 simple eapply @stmt_modifies_assign_call
 simple apply @eq_refl
 simple eapply @call_modifies_func
 simple apply @eq_refl
 (*external*) reflexivity
 (*external*) (apply Forall2_cons)
 simple apply @out_arg_In_vars_in
 (*external*) (apply Forall2_nil)
 (*external*) reflexivity

 (*external*) (eapply func_modifies_frame; only 1: solve
                            [ eauto  15 with nocore func_specs ])
 (*external*) (apply incl_vars_None_None)
 (*external*) (apply Forall_cons)
 (*external*) reflexivity
 (*external*) (apply Forall_nil)
 (*external*) reflexivity

 (*external*) (apply In_vars_Some)
 simple apply in_eq
 simple apply @block_modifies_nil *)
Abort.

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition parser_parse_ethernet_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ethernet"] ge).
