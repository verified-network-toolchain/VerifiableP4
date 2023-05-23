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

Definition tofino_parse_resubmit_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_resubmit"] ge).

Definition tofino_parse_port_metadata_fundef :=
  ltac:(get_fd ["TofinoIngressParser"; "parse_port_metadata"] ge).

Definition tofino_parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH,
      PRE
        (ARG []
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
           (EXT []))).

(* Unset Printing Notations. *)

Lemma tofino_parser_start_body:
  func_sound ge tofino_parser_start_fundef nil tofino_parser_start_spec.
Proof.
  start_function.
Qed.

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition parser_parse_ethernet_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ethernet"] ge).
