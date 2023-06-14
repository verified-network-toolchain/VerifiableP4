Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.p4ast.

Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition am_ge := ltac:(get_am_ge prog).
Definition ge := ltac:(get_ge am_ge prog).

Definition header_sample_t: P4Type := ltac:(get_type "header_sample_t" ge).
Definition metadata_t: P4Type := ltac:(get_type "metadata_t" ge).
Definition ingress_intrinsic_metadata_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_t" ge).
Definition ingress_intrinsic_metadata_from_parser_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_from_parser_t" ge).
Definition ingress_intrinsic_metadata_for_deparser_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_for_deparser_t" ge).
Definition ingress_intrinsic_metadata_for_tm_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_for_tm_t" ge).
Definition tcp_h: P4Type := ltac:(get_type "tcp_h" ge).
Definition udp_h: P4Type := ltac:(get_type "udp_h" ge).
