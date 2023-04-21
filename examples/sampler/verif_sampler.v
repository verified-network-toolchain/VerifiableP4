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

Definition set_field_valid (h: Sval) (fld: ident): Sval :=
  (update fld (EvalBuiltin.setValid (get fld h)) h).

Record ipv4_rec := {
    ipv4_version: Sval;
    ipv4_ihl: Sval;
    ipv4_diffserv: Sval;
    ipv4_total_len: Sval;
    ipv4_identification: Sval;
    ipv4_flags: Sval;
    ipv4_frag_offset: Sval;
    ipv4_ttl: Sval;
    ipv4_protocol: Sval;
    ipv4_hdr_checksum: Sval;
    ipv4_src_addr: Sval;
    ipv4_dst_addr: Sval;
  }.

Definition hdr (ethernet tcp udp: Sval) (ipv4: ipv4_rec): Sval :=
  ValBaseStruct
    [("bridge",
       ValBaseHeader
         [("contains_sample", P4Bit_ 8)] (Some true));
     ("sample",
       ValBaseHeader
         [("dmac", P4Bit_ 48);
          ("smac", P4Bit_ 48);
          ("etype", P4Bit_ 16);
          ("srcip", P4Bit_ 32);
          ("dstip", P4Bit_ 32);
          ("num_pkts", P4Bit_ 32)] None);
     ("ethernet", ethernet);
     ("ipv4",
       ValBaseHeader
         [("version", ipv4_version ipv4);
          ("ihl", ipv4_ihl ipv4);
          ("diffserv", ipv4_diffserv ipv4);
          ("total_len", ipv4_total_len ipv4);
          ("identification", ipv4_identification ipv4);
          ("flags", ipv4_flags ipv4);
          ("frag_offset", ipv4_frag_offset ipv4);
          ("ttl", ipv4_ttl ipv4);
          ("protocol", ipv4_protocol ipv4);
          ("hdr_checksum", ipv4_hdr_checksum ipv4);
          ("src_addr", ipv4_src_addr ipv4);
          ("dst_addr", ipv4_dst_addr ipv4)] (Some true));
     ("tcp", tcp);
     ("udp", udp)].

Definition ig_md (num_pkts: Z) := ValBaseStruct [("num_pkts", P4Bit 32 num_pkts)].

Definition act_sample_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_tm_md"]]) [p]
    WITH ethernet tcp udp ipv4 ig_intr_tm_md num_pkts,
      PRE
        (ARG []
        (MEM [(["hdr"], hdr ethernet tcp udp ipv4);
              (["ig_md"], ig_md num_pkts);
              (["ig_intr_tm_md"], ig_intr_tm_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], update "sample"
                          (sample_repr (ipv4_src_addr ipv4)
                             (ipv4_dst_addr ipv4) num_pkts)
                          (update "bridge" (bridge_repr 1)
                             (hdr ethernet tcp udp ipv4)));
              (["ig_md"], ig_md num_pkts);
              (["ig_intr_tm_md"], update "mcast_grp_a" (P4Bit 16 1) ig_intr_tm_md)]
        (EXT []))).

Lemma act_sample_body:
  func_sound ge act_sample_fundef nil act_sample_spec.
Proof.
  start_function.
  unfold hdr.
  simpl.
  do 10 step.
  entailer.
Qed.
