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

Definition tofino_parser_start_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "start"] ge).

Definition tofino_parser_resubmit_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_resubmit"] ge).

Definition tofino_parser_port_metadata_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_port_metadata"] ge).

Definition test :=
  ltac:(get_fd ["TofinoIngressParser"; "accept"] ge).

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

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition parser_parse_ethernet_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ethernet"] ge).
