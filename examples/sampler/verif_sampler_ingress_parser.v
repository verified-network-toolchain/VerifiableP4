Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.verif_sampler_tofino_parser.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "ingress_parser"].

Definition parser_parse_udp_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_udp"] ge).

Definition parser_parse_udp_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hdr udp pin'
         (_: extract udp_h pin =
             Some (udp, SReturnNull, pin')),
      PRE
        (ARG []
        (MEM [(["hdr"], hdr)]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], update "udp" (eval_val_to_sval udp) hdr)]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_parse_udp_body:
  func_sound ge parser_parse_udp_fundef nil parser_parse_udp_spec.
Proof.
  start_function.
  step_call (@packet_in_extract_body Info); [ entailer | apply H |].
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_parse_tcp_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_tcp"] ge).

Definition parser_parse_tcp_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hdr tcp pin'
         (_: extract tcp_h pin =
             Some (tcp, SReturnNull, pin')),
      PRE
        (ARG []
        (MEM [(["hdr"], hdr)]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], update "tcp" (eval_val_to_sval tcp) hdr)]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_parse_tcp_body:
  func_sound ge parser_parse_tcp_fundef nil parser_parse_tcp_spec.
Proof.
  start_function.
  step_call (@packet_in_extract_body Info); [ entailer | apply H |].
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_parse_ipv4_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ipv4"] ge).

Definition IP_PROTOCOLS_TCP: Z := 6.
Definition IP_PROTOCOLS_UDP: Z := 17.

Record ipv4_rec := {
    ipv4_version: Val;
    ipv4_ihl: Val;
    ipv4_diffserv: Val;
    ipv4_total_len: Val;
    ipv4_identification: Val;
    ipv4_flags: Val;
    ipv4_frag_offset: Val;
    ipv4_ttl: Val;
    ipv4_protocol: Val;
    ipv4_hdr_checksum: Val;
    ipv4_src_addr: Val;
    ipv4_dst_addr: Val;
  }.

Definition ipv4_repr_val (ipv4: ipv4_rec): Val :=
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
     ("dst_addr", ipv4_dst_addr ipv4)] true.

Definition protocol_extract_cond
  (ipv4: ipv4_rec) (pin pin': packet_in) (result: Val): Prop :=
  if Val_eqb (ipv4_protocol ipv4) (P4BitV 8 IP_PROTOCOLS_TCP)
  then extract tcp_h pin = Some (result, SReturnNull, pin')
  else if Val_eqb (ipv4_protocol ipv4) (P4BitV 8 IP_PROTOCOLS_UDP)
       then extract udp_h pin = Some (result, SReturnNull, pin')
       else result = ValBaseNull /\ pin = pin'.

Definition protocol_extract_result
  (ipv4: ipv4_rec) (result: Val) (header: Sval): Sval :=
  if Val_eqb (ipv4_protocol ipv4) (P4BitV 8 IP_PROTOCOLS_TCP)
  then update "tcp" (eval_val_to_sval result) header
  else if Val_eqb (ipv4_protocol ipv4) (P4BitV 8 IP_PROTOCOLS_UDP)
       then update "udp" (eval_val_to_sval result) header
       else header.

Record header_sample_rec := {
    header_sample_bridge: Sval;
    header_sample_sample: Sval;
    header_sample_ethernet: Sval;
    header_sample_ipv4: Sval;
    header_sample_tcp: Sval;
    header_sample_udp: Sval;
  }.

Definition hdr (hsample: header_sample_rec) :=
  ValBaseStruct
    [("bridge", header_sample_bridge hsample);
     ("sample", header_sample_sample hsample);
     ("ethernet", header_sample_ethernet hsample);
     ("ipv4", header_sample_ipv4 hsample);
     ("tcp", header_sample_tcp hsample);
     ("udp", header_sample_udp hsample)].

Definition parser_parse_ipv4_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hsample ipv4 pin2 result pin3
         (_: extract ipv4_h pin =
               Some (ipv4_repr_val ipv4, SReturnNull, pin2))
         (_: protocol_extract_cond ipv4 pin2 pin3 result),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr hsample))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], protocol_extract_result ipv4 result
                             (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
                                (hdr hsample)))]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin3)]))).

Lemma force_cast_P4BitV_eq: forall w v,
    force ValBaseNull (@Ops.eval_cast Info (TypBit w) (P4BitV w v)) = P4BitV w v.
Proof.
  intros. unfold P4BitV. simpl. f_equal. rewrite P4Arith.bit_to_lbool_back.
  unfold P4Arith.BitArith.mod_bound. rewrite Zmod_mod.
  change (v mod _) with (P4Arith.BitArith.mod_bound w v).
  rewrite P4Arith.to_lbool_bit_mod. reflexivity.
Qed.

Lemma abs_ipv4_hdr_eq_eq: forall ipv4 hsample w v,
    abs_eq
      (get "protocol"
         (get "ipv4"
            (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
               (hdr hsample))))
      (build_abs_unary_op (@Ops.eval_cast Info (TypBit w))
         (eval_val_to_sval (P4BitV w v))) =
      eval_val_to_sval
        (force ValBaseNull
           (Ops.eval_binary_op Eq (ipv4_protocol ipv4) (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ipv4_repr_val. simpl get. unfold abs_eq.
  unfold build_abs_binary_op. rewrite !eval_sval_to_val_eq. reflexivity.
Qed.

Lemma is_sval_true_binary_op_eq: forall v1 v2,
  is_sval_true
    (eval_val_to_sval (force ValBaseNull (Ops.eval_binary_op Eq v1 v2))) ->
  Val_eqb v1 v2 = true.
Proof.
  intros. unfold Ops.eval_binary_op in H.
  remember (Ops.eval_binary_op_eq _ _).
  destruct o eqn:?H; simpl in H; [destruct b|]; [|exfalso; auto..].
  symmetry in Heqo. apply Ops.eval_binary_op_eq_eq in Heqo.
  rewrite <- Val_eqb_eq_iff in Heqo. assumption.
Qed.

Lemma is_sval_false_binary_op_eq: forall v1 v2,
  is_sval_false
    (eval_val_to_sval (force ValBaseNull (Ops.eval_binary_op Eq v1 v2))) ->
  Val_eqb v1 v2 = false.
Proof.
  intros. unfold Ops.eval_binary_op in H.
  remember (Ops.eval_binary_op_eq _ _).
  destruct o eqn:?H; simpl in H; [destruct b|]. 1, 3: exfalso; assumption.
  symmetry in Heqo. apply Ops.eval_binary_op_neq_neq in Heqo.
  rewrite <- Val_eqb_eq_iff in Heqo. apply Bool.not_true_is_false in Heqo.
  assumption.
Qed.

Lemma parser_parse_ipv4_body:
  func_sound ge parser_parse_ipv4_fundef nil parser_parse_ipv4_spec.
Proof.
  start_function.
  step_call (@packet_in_extract_body Info); [ entailer | apply H |].
  step_if; change (ValBaseBit _) with (P4BitV 8 IP_PROTOCOLS_TCP) in H1;
    rewrite abs_ipv4_hdr_eq_eq in H1.
  - apply is_sval_true_binary_op_eq in H1. red in H0. rewrite H1 in H0.
    unfold protocol_extract_result. rewrite !H1.
    step_call parser_parse_tcp_body. 2: apply H0. entailer.
  - apply is_sval_false_binary_op_eq in H1. red in H0. rewrite H1 in H0.
    unfold protocol_extract_result. rewrite !H1.
    step_if; change (ValBaseBit _) with (P4BitV 8 IP_PROTOCOLS_UDP) in H2;
      rewrite abs_ipv4_hdr_eq_eq in H2.
    + apply is_sval_true_binary_op_eq in H2. rewrite H2 in H0.
      rewrite !H2. step_call parser_parse_udp_body. 2: apply H0. entailer.
    + apply is_sval_false_binary_op_eq in H2. rewrite H2 in H0.
      destruct H0. subst. rewrite !H2.
      step_call (@parser_accept_body Info). entailer.
Qed.

Definition parser_parse_ethernet_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ethernet"] ge).

Record ethernet_rec := {
    ethernet_dst_addr: Val;
    ethernet_src_addr: Val;
    ethernet_ether_type: Val;
  }.

Definition ethernet_repr_val (ether: ethernet_rec) : Val :=
  ValBaseHeader
    [("dst_addr", ethernet_dst_addr ether);
     ("src_addr", ethernet_src_addr ether);
     ("ether_type", ethernet_ether_type ether)] true.

Definition ethernet_extract_result
  (hsample: header_sample_rec) (ether: ethernet_rec) (ipv4: ipv4_rec)
  (result: Val): Sval :=
  protocol_extract_result ipv4 result
    (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
       (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
          (hdr hsample))).

Definition ETHERTYPE_IPV4: Z := 0x800.

Definition parser_parse_ethernet_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin pin2 pin3 pin4: packet_in) ether ipv4 hsample result
         (_: extract ethernet_h pin =
               Some (ethernet_repr_val ether, SReturnNull, pin2))
         (_: extract ipv4_h pin2 =
               Some (ipv4_repr_val ipv4, SReturnNull, pin3))
         (_: protocol_extract_cond ipv4 pin3 pin4 result)
         (_: ethernet_ether_type ether = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr hsample))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], ethernet_extract_result hsample ether ipv4 result)]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin4)]))).

Lemma abs_ether_eq_eq: forall ether hsample w v,
    abs_eq
      (get "ether_type"
         (get "ethernet"
            (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
               (hdr hsample))))
      (build_abs_unary_op (@Ops.eval_cast Info (TypBit w))
         (eval_val_to_sval (P4BitV w v))) =
      eval_val_to_sval
        (force ValBaseNull
           (Ops.eval_binary_op Eq (ethernet_ether_type ether) (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ethernet_repr_val. simpl get. unfold abs_eq.
  unfold build_abs_binary_op. rewrite !eval_sval_to_val_eq. reflexivity.
Qed.

Lemma parser_parse_ethernet_body:
  func_sound ge parser_parse_ethernet_fundef nil parser_parse_ethernet_spec.
Proof.
  start_function.
  step_call (@packet_in_extract_body Info); [ entailer | apply H |].
  step_if; change (ValBaseBit _) with (P4BitV 16 ETHERTYPE_IPV4) in H3;
    rewrite abs_ether_eq_eq in H3.
  - unfold ethernet_extract_result.
    remember (Build_header_sample_rec
                (header_sample_bridge hsample)
                (header_sample_sample hsample)
                (eval_val_to_sval (ethernet_repr_val ether))
                (header_sample_ipv4 hsample)
                (header_sample_tcp hsample)
                (header_sample_udp hsample)) as new_hdr.
    assert (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
              (hdr hsample) = hdr new_hdr) by (rewrite Heqnew_hdr; reflexivity).
    rewrite H4.
    step_call parser_parse_ipv4_body; [entailer| apply H0 | apply H1].
  - apply is_sval_false_binary_op_eq in H3.
    rewrite Val_eqb_neq_iff in H3. exfalso. apply H3. assumption.
Qed.

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition sample_invalid_bridge
  (hsample: header_sample_rec) (has_sample: Sval) : header_sample_rec :=
  Build_header_sample_rec
    (ValBaseHeader [("contains_sample", has_sample)] (Some false))
    (header_sample_sample hsample)
    (header_sample_ethernet hsample)
    (header_sample_ipv4 hsample)
    (header_sample_tcp hsample)
    (header_sample_udp hsample).

Definition sample_valid_bridge
  (hsample: header_sample_rec) (has_sample: Sval) : header_sample_rec :=
  Build_header_sample_rec
    (ValBaseHeader [("contains_sample", has_sample)] (Some true))
    (header_sample_sample hsample)
    (header_sample_ethernet hsample)
    (header_sample_ipv4 hsample)
    (header_sample_tcp hsample)
    (header_sample_udp hsample).

Definition parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_md"]]) [["packet_in"]]
    WITH (pin pin2 pin3 pin4 pin5: packet_in) ver port stamp
         ether ipv4 hsample has_sample result
         (_: extract ingress_intrinsic_metadata_t pin =
             Some (iimt_repr_val 0 ver port stamp, SReturnNull, pin2))
         (_: 64 < Zlength pin2)
         (_: extract ethernet_h (skipn 64 pin2) =
               Some (ethernet_repr_val ether, SReturnNull, pin3))
         (_: extract ipv4_h pin3 =
               Some (ipv4_repr_val ipv4, SReturnNull, pin4))
         (_: protocol_extract_cond ipv4 pin4 pin5 result)
         (_: ethernet_ether_type ether = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr (sample_invalid_bridge hsample has_sample)))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], ethernet_extract_result
                             ((sample_valid_bridge hsample has_sample))
                             ether ipv4 result);
                 (["ig_intr_md"], (iimt_repr_sval 0 ver port stamp))]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin5)]))).

Lemma parser_start_body:
  func_sound ge parser_start_fundef nil parser_start_spec.
Proof.
  start_function.
  step_call tofino_parser_body; [entailer | eauto.. |].
  step. simpl eval_write_var.
  change (ValBaseStruct _) with (hdr (sample_valid_bridge hsample has_sample)).
  step_call parser_parse_ethernet_body;
    [entailer | eauto.. |].
  step. entailer.
Qed.

Definition parser_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "apply"] ge).

Definition has_sample_init := P4Bit_ 8.

Definition hdr_init: header_sample_rec :=
  Build_header_sample_rec
    (ValBaseHeader
       [("contains_sample", P4Bit_ 8)] (Some false))
    (ValBaseHeader
       [("dmac", P4Bit_ 48);
        ("smac", P4Bit_ 48);
        ("etype", P4Bit_ 16);
        ("srcip", P4Bit_ 32);
        ("dstip", P4Bit_ 32);
        ("num_pkts", P4Bit_ 32)] (Some false))
    (ValBaseHeader
       [("dst_addr", P4Bit_ 48);
        ("src_addr", P4Bit_ 48);
        ("ether_type", P4Bit_ 16)] (Some false))
    (ValBaseHeader
       [("version", P4Bit_ 4);
        ("ihl", P4Bit_ 4);
        ("diffserv", P4Bit_ 8);
        ("total_len", P4Bit_ 16);
        ("identification", P4Bit_ 16);
        ("flags", P4Bit_ 3);
        ("frag_offset", P4Bit_ 13);
        ("ttl", P4Bit_ 8);
        ("protocol", P4Bit_ 8);
        ("hdr_checksum", P4Bit_ 16);
        ("src_addr", P4Bit_ 32);
        ("dst_addr", P4Bit_ 32)]
       (Some false))
    (ValBaseHeader
       [("src_port", P4Bit_ 16);
        ("dst_port", P4Bit_ 16);
        ("seq_no", P4Bit_ 32);
        ("ack_no", P4Bit_ 32);
        ("data_offset", P4Bit_ 4);
        ("res", P4Bit_ 4);
        ("flags", P4Bit_ 8);
        ("window", P4Bit_ 16);
        ("checksum", P4Bit_ 16);
        ("urgent_ptr", P4Bit_ 16)]
       (Some false))
    (ValBaseHeader
        [("src_port", P4Bit_ 16);
         ("dst_port", P4Bit_ 16);
         ("hdr_length", P4Bit_ 16);
         ("checksum", P4Bit_ 16)]
        (Some false)).

Definition parser_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["ig_md"]; ["ig_intr_md"]]) [["packet_in"]]
    WITH (pin pin2 pin3 pin4 pin5: packet_in) ver port stamp
         ether ipv4 result
         (_: extract ingress_intrinsic_metadata_t pin =
             Some (iimt_repr_val 0 ver port stamp, SReturnNull, pin2))
         (_: 64 < Zlength pin2)
         (_: extract ethernet_h (skipn 64 pin2) =
               Some (ethernet_repr_val ether, SReturnNull, pin3))
         (_: extract ipv4_h pin3 =
               Some (ipv4_repr_val ipv4, SReturnNull, pin4))
         (_: protocol_extract_cond ipv4 pin4 pin5 result)
         (_: ethernet_ether_type ether = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr (sample_invalid_bridge hdr_init has_sample_init)))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [(ethernet_extract_result
                     ((sample_valid_bridge hdr_init has_sample_init))
                     ether ipv4 result);
                  (ValBaseStruct [("num_pkts", P4Bit_ 32)]);
                  (iimt_repr_sval 0 ver port stamp)] ValBaseNull
           (MEM []
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin5)]))).

Lemma parser_body:
  func_sound ge parser_fundef nil parser_spec.
Proof.
  start_function.
  step.
  replace (ValBaseStruct _) with
    (hdr (sample_invalid_bridge hdr_init has_sample_init)) by
    (unfold hdr; reflexivity).
  step.
  step.
  step_call parser_start_body; [entailer | eauto..].
  step. entailer.
Qed.
