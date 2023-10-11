Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.p4ast.

Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Val_eqb := (val_eqb Bool.eqb).

Lemma extract_encode: forall {tags_t: Type} (typ: @P4Type tags_t) (val: Val) pkt,
    ext_val_typ val typ  ->
    is_packet_typ typ = true ->
    Tofino.extract typ (encode val ++ pkt) = Some (val, SReturnNull, pkt).
Proof. intros. unfold Tofino.extract. rewrite extract_encode_raw; auto. Qed.

Lemma emit_encode: forall {tags_t: Type} (typ: @P4Type tags_t) (val: Val) pkt,
    ⊢ᵥ val \: typ  ->
    is_packet_typ typ = true ->
    Tofino.emit val pkt = (inl (app pkt (encode val)), app pkt (encode val)).
Proof.
  intros. unfold Tofino.emit. simpl.
  unfold ExceptionState.get_state, Packet.packet_bind, ExceptionState.state_bind.
  erewrite emit_encode_raw; eauto.
Qed.

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

Definition am_ge := ltac:(get_am_ge prog).
Definition ge := ltac:(get_ge am_ge prog).

Definition header_sample_t: P4Type := ltac:(get_type "header_sample_t" ge).
Definition metadata_t: P4Type := ltac:(get_type "metadata_t" ge).
Definition bridge_t: P4Type := ltac:(get_type "bridge_t" ge).
Definition sample_t: P4Type := ltac:(get_type "sample_t" ge).
Definition tcp_h: P4Type := ltac:(get_type "tcp_h" ge).
Definition udp_h: P4Type := ltac:(get_type "udp_h" ge).
Definition ipv4_h: P4Type := ltac:(get_type "ipv4_h" ge).
Definition ethernet_h: P4Type := ltac:(get_type "ethernet_h" ge).
Definition MeterColor_t: P4Type := ltac:(get_type "MeterColor_t" ge).

Definition IP_PROTOCOLS_TCP: Z := 6.
Definition IP_PROTOCOLS_UDP: Z := 17.

Record ipv4_rec := {
    ipv4_version: Z;
    ipv4_ihl: Z;
    ipv4_diffserv: Z;
    ipv4_total_len: Z;
    ipv4_identification: Z;
    ipv4_flags: Z;
    ipv4_frag_offset: Z;
    ipv4_ttl: Z;
    ipv4_protocol: Z;
    ipv4_hdr_checksum: Z;
    ipv4_src_addr: Z;
    ipv4_dst_addr: Z;
  }.

Definition ipv4_repr_val (ipv4: ipv4_rec): Val :=
  ValBaseHeader
    [("version", P4BitV 4 (ipv4_version ipv4));
     ("ihl", P4BitV 4 (ipv4_ihl ipv4));
     ("diffserv", P4BitV 8 (ipv4_diffserv ipv4));
     ("total_len", P4BitV 16 (ipv4_total_len ipv4));
     ("identification", P4BitV 16 (ipv4_identification ipv4));
     ("flags", P4BitV 3 (ipv4_flags ipv4));
     ("frag_offset", P4BitV 13 (ipv4_frag_offset ipv4));
     ("ttl", P4BitV 8 (ipv4_ttl ipv4));
     ("protocol", P4BitV 8 (ipv4_protocol ipv4));
     ("hdr_checksum", P4BitV 16 (ipv4_hdr_checksum ipv4));
     ("src_addr", P4BitV 32 (ipv4_src_addr ipv4));
     ("dst_addr", P4BitV 32 (ipv4_dst_addr ipv4))] true.

Definition is_tcp ipv4: bool :=
  Val_eqb (P4BitV 8 (ipv4_protocol ipv4)) (P4BitV 8 IP_PROTOCOLS_TCP).

Definition is_udp ipv4: bool :=
  Val_eqb (P4BitV 8 (ipv4_protocol ipv4)) (P4BitV 8 IP_PROTOCOLS_UDP).

Definition protocol_extract_result
  (ipv4: ipv4_rec) (result: Val) (header: Sval): Sval :=
  if is_tcp ipv4 then update "tcp" (eval_val_to_sval result) header
  else if is_udp ipv4 then update "udp" (eval_val_to_sval result) header
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
           (Ops.eval_binary_op Eq (P4BitV 8 (ipv4_protocol ipv4)) (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ipv4_repr_val.
  Opaque P4BitV. simpl get. Transparent P4BitV. unfold abs_eq.
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

Record ethernet_rec := {
    ethernet_dst_addr: Z;
    ethernet_src_addr: Z;
    ethernet_ether_type: Z;
  }.

Definition ethernet_repr_val (ether: ethernet_rec) : Val :=
  ValBaseHeader
    [("dst_addr", P4BitV 48 (ethernet_dst_addr ether));
     ("src_addr", P4BitV 48 (ethernet_src_addr ether));
     ("ether_type", P4BitV 16 (ethernet_ether_type ether))] true.

Definition ethernet_extract_result
  (header: Sval) (ether: ethernet_rec) (ipv4: ipv4_rec)
  (result: Val): Sval :=
  protocol_extract_result ipv4 result
    (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
       (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
          header)).

Definition ETHERTYPE_IPV4: Z := 0x800.

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
           (Ops.eval_binary_op Eq (P4BitV 16 (ethernet_ether_type ether))
              (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ethernet_repr_val.
  Opaque P4BitV. simpl get. Transparent P4BitV. unfold abs_eq.
  unfold build_abs_binary_op. rewrite !eval_sval_to_val_eq. reflexivity.
Qed.

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

Lemma ext_val_typ_ipv4: forall ipv4, ⊫ᵥ ipv4_repr_val ipv4 \: ipv4_h.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.

Lemma ext_val_typ_ethernet: forall ether, ⊫ᵥ ethernet_repr_val ether \: ethernet_h.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.
