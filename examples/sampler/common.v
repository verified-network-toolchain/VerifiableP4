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
Notation Val_eqb := (val_eqb Bool.eqb).

Lemma Val_eqb_eq_iff: forall (v1 v2: Val), Val_eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros. split; intros.
  - apply val_eqb_eq in H; auto. intros. apply Bool.eqb_prop; auto.
  - subst. apply val_eqb_refl. exact Bool.eqb_reflx.
Qed.

Lemma Val_eqb_neq_iff: forall (v1 v2: Val), Val_eqb v1 v2 = false <-> v1 <> v2.
Proof.
  intros. split; intros.
  - intro. rewrite <- Val_eqb_eq_iff, H in H0. discriminate.
  - rewrite <- Bool.not_true_iff_false. intro. rewrite Val_eqb_eq_iff in H0.
    apply H. assumption.
Qed.

Definition P4BitV (w : N) (v : Z) : Val := ValBaseBit (P4Arith.to_lbool w v).

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
Definition ipv4_h: P4Type := ltac:(get_type "ipv4_h" ge).
Definition ethernet_h: P4Type := ltac:(get_type "ethernet_h" ge).
Definition MeterColor_t: P4Type := ltac:(get_type "MeterColor_t" ge).
