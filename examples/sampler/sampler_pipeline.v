Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.Queue.
Require Import Poulet4.P4light.Architecture.TrafficManager.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.TofinoPipeline.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.verif_ingress_parser.
Require Import ProD3.examples.sampler.verif_ingress.
Require Import ProD3.examples.sampler.verif_ingress_deparser.
Require Import ProD3.examples.sampler.verif_egress_parser.
Require Import ProD3.examples.sampler.verif_egress.
Require Import ProD3.examples.sampler.verif_egress_deparser.
Require Import ProD3.examples.sampler.traffic_manager.
Require Import ProD3.core.ProgNotations.
Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition extern_contains (es: extern_state) (p: path) (counter: Z): Prop :=
  PathMap.get (p ++ ["reg_count"]) es =
    Some (ObjRegister [Z_to_val counter]) /\ 0 <= counter.

Lemma extern_contains_congruence: forall es p z1 z2,
    extern_contains es p z1 -> extern_contains es p z2 ->
    P4Arith.BitArith.mod_bound 32 z1 = P4Arith.BitArith.mod_bound 32 z2 /\
      0 <= z1 /\ 0 <= z2.
Proof.
  unfold extern_contains. intros es p z1 z2 [] []. rewrite H in H1.
  unfold Z_to_val in H1. split; [|split]; auto.
  apply P4Arith.to_lbool_inj_bit_mod. congruence.
Qed.

Lemma congruence_extern_contains:
  forall es p z1 z2,
    P4Arith.BitArith.mod_bound 32 z1 = P4Arith.BitArith.mod_bound 32 z2 ->
    0 <= z2 ->
    extern_contains es p z1 -> extern_contains es p z2.
Proof.
  unfold extern_contains. intros. split; auto. destruct H1. rewrite H1.
  unfold Z_to_val. do 4 f_equal. apply P4Arith.bit_mod_inj_to_lbool. assumption.
Qed.

Lemma extern_contains_trans: forall es1 es2 p z1 z2,
    extern_contains es1 p z1 -> extern_contains es1 p z2 ->
    extern_contains es2 p z2 -> extern_contains es2 p z1.
Proof.
  intros. destruct (extern_contains_congruence _ _ _ _ H H0) as [? []].
  symmetry in H2. eapply congruence_extern_contains; eauto.
Qed.

Lemma extern_contains_diff: forall es p1 p2 o z,
    p1 <> p2 ++ ["reg_count"] ->
    extern_contains (PathMap.set p1 o es) p2 z <-> extern_contains es p2 z.
Proof.
  intros. split; unfold extern_contains; intros;
    rewrite PathMap.get_set_diff in *; auto.
Qed.

Inductive inprsr_block: programmable_block_sem :=
| inprsr_block_intro:
  forall inst_path m m' es es' fd (pin pin': packet_in) ver port stamp ether ipv4 result
    hdr ig_md ig_intr_md signal,
    ⊫ᵥ iimt_repr_val 0 ver port stamp \: ingress_intrinsic_metadata_t ->
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h else
      (if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull)) ->
    P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 ->
    pin ⫢ [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒;
           ⟨64⟩;
           ⦑ encode (ethernet_repr_val ether) ⦒;
           ⦑ encode (ipv4_repr_val ipv4) ⦒;
           ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
             ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] ->
    PathMap.get ["hdr"] m = Some (common.hdr hdr_init) ->
    PathMap.get ["packet_in"] es = Some (ObjPin pin) ->
    programmable_block ge inst_path "ingress_parser" fd ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil [] (m', es')
      [hdr; ig_md; ig_intr_md] signal ->
    inprsr_block es [] es' [hdr; ig_md; ig_intr_md] signal.

Inductive ingress_block: programmable_block_sem :=
| ingress_block_intro:
  forall inst_path m m' es es' fd hdr1 hdr2 ig_md1 ig_md2 ig_intr_md
    ig_intr_dprsr_md2 ig_intr_tm_md2 signal,
    programmable_block ge inst_path "ingress" fd ->
    let ig_intr_prsr_md :=
      force ValBaseNull
        (uninit_sval_of_typ None ingress_intrinsic_metadata_from_parser_t) in
    let ig_intr_dprsr_md1 :=
      force ValBaseNull
        (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t) in
    exec_func ge read_ndetbit inst_path (m, es) fd nil
      [hdr1; ig_md1; ig_intr_md; ig_intr_prsr_md;
       ig_intr_dprsr_md1; ig_intr_tm_md] (m', es')
      [hdr2; ig_md2; ig_intr_dprsr_md2; ig_intr_tm_md2] signal ->
    ingress_block es
      [hdr1; ig_md1; ig_intr_md; ig_intr_prsr_md; ig_intr_dprsr_md1; ig_intr_tm_md]
      es' [hdr2; ig_md2; ig_intr_dprsr_md2; ig_intr_tm_md2] signal.

Inductive indeprsr_block: programmable_block_sem :=
| indeprsr_block_intro:
  forall inst_path m m' es es' fd hdr1 hdr2 ig_md ig_intr_dprsr_md signal,
    programmable_block ge inst_path "ingress_deparser" fd ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil
      [hdr1; ig_md; ig_intr_dprsr_md] (m', es') [hdr2] signal ->
    indeprsr_block es [hdr1; ig_md; ig_intr_dprsr_md] es' [hdr2] signal.

Inductive parser_ingress_cond: list Sval -> list Sval -> Prop :=
| parser_ingress_cond_intro:
  forall ig_intr_md ig_intr_prsr_md ig_intr_dprsr_md ig_intr_tm_md,
    parser_ingress_cond [ig_intr_md]
      [ig_intr_md; ig_intr_prsr_md; ig_intr_dprsr_md; ig_intr_tm_md].

Inductive ingress_deprsr_cond: list Sval -> list Sval -> Prop :=
| ingress_deprsr_cond_intro:
  forall ig_intr_dprsr_md ig_intr_tm_md,
    ingress_deprsr_cond [ig_intr_dprsr_md; ig_intr_tm_md] [ig_intr_dprsr_md].

Inductive ingress_tm_cond: list Sval -> Sval -> Prop :=
| ingress_tm_cond_intro:
  forall ig_intr_dprsr_md ig_intr_tm_md,
    ingress_tm_cond [ig_intr_dprsr_md; ig_intr_tm_md] ig_intr_tm_md.

Lemma get_packet: forall v1 v2 (es: extern_state),
    PathMap.get ["packet_in"]
      (PathMap.set ["packet_out"] v1 (PathMap.set ["packet_in"] v2 es)) = Some v2.
Proof.
  intros. rewrite PathMap.get_set_diff; [| discriminate].
  rewrite PathMap.get_set_same. reflexivity.
Qed.

Lemma hdr_init_bridge_type:
  ⊢ᵥ common.hdr (sample_valid_bridge hdr_init) \: header_sample_t.
Proof. vm_compute. repeat constructor. Qed.

Lemma hdr_init_type:
  ⊢ᵥ common.hdr hdr_init \: header_sample_t.
Proof. vm_compute. repeat constructor. Qed.

Lemma protocol_extract_result_typ: forall ipv4 result header,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h
          else result = ValBaseNull) ->
    ⊢ᵥ header \: header_sample_t ->
    ⊢ᵥ protocol_extract_result ipv4 result header \: header_sample_t.
Proof.
  intros. unfold protocol_extract_result.
  destruct (is_tcp ipv4).
  - apply update_struct_typ with tcp_h; auto.
    apply ValueBaseMap_preserves_type. apply H.
  - destruct (is_udp ipv4); auto.
    apply update_struct_typ with udp_h; auto.
    apply ValueBaseMap_preserves_type. apply H.
Qed.

Lemma ethernet_extract_result_typ:
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val),
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h
          else result = ValBaseNull) ->
    ⊢ᵥ ethernet_extract_result
      (common.hdr (sample_valid_bridge hdr_init)) ether ipv4 result
      \: header_sample_t.
Proof.
  intros. unfold ethernet_extract_result.
  apply protocol_extract_result_typ; auto.
  apply update_struct_typ with ipv4_h; auto.
  - apply ValueBaseMap_preserves_type. apply ext_val_typ_ipv4.
  - apply update_struct_typ with ethernet_h; auto.
    + apply ValueBaseMap_preserves_type. apply ext_val_typ_ethernet.
    + apply hdr_init_bridge_type.
Qed.

Lemma ethernet_extract_result_hdr:
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val),
  exists (ethernet tcp udp : Sval) (ip4 : ipv4_rec),
    ethernet_extract_result
      (common.hdr (sample_valid_bridge hdr_init)) ether ipv4
      result = hdr ethernet tcp udp ip4.
Proof.
  intros ether ipv4 result.
  unfold ethernet_extract_result. unfold protocol_extract_result.
  unfold sample_valid_bridge, hdr_init. simpl common.hdr. unfold hdr.
  destruct (is_tcp ipv4); [do 4 eexists; reflexivity |].
  destruct (is_udp ipv4); [do 4 eexists; reflexivity |].
  do 4 eexists; reflexivity.
Qed.

Definition empty_header : Val :=
  ValBaseStruct
    [("bridge", ValBaseHeader [("contains_sample", P4BitV 8 0)] false);
     ("sample",
       ValBaseHeader
         [("dmac", P4BitV 48 0); ("smac", P4BitV 48 0); ("etype", P4BitV 16 0);
          ("srcip", P4BitV 32 0); ("dstip", P4BitV 32 0); ("num_pkts", P4BitV 32 0)]
         false);
     ("ethernet",
       ValBaseHeader
         [("dst_addr", P4BitV 48 0); ("src_addr", P4BitV 48 0); ("ether_type", P4BitV 16 0)]
         false);
     ("ipv4",
       ValBaseHeader
         [("version", P4BitV 4 0); ("ihl", P4BitV 4 0); ("diffserv", P4BitV 8 0);
          ("total_len", P4BitV 16 0); ("identification", P4BitV 16 0);
          ("flags", P4BitV 3 0); ("frag_offset", P4BitV 13 0); ("ttl", P4BitV 8 0);
          ("protocol", P4BitV 8 0); ("hdr_checksum", P4BitV 16 0);
          ("src_addr", P4BitV 32 0); ("dst_addr", P4BitV 32 0)] false);
     ("tcp",
       ValBaseHeader
         [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0); ("seq_no", P4BitV 32 0);
          ("ack_no", P4BitV 32 0); ("data_offset", P4BitV 4 0); ("res", P4BitV 4 0);
          ("flags", P4BitV 8 0); ("window", P4BitV 16 0); ("checksum", P4BitV 16 0);
          ("urgent_ptr", P4BitV 16 0)] false);
     ("udp",
       ValBaseHeader
         [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0); ("hdr_length", P4BitV 16 0);
          ("checksum", P4BitV 16 0)] false)].

Opaque eval_val_to_sval ipv4_repr_val ethernet_repr_val bridge_repr_val.

Lemma hdr_init_valid_only: common.hdr hdr_init = val_to_sval_valid_only empty_header.
Proof. unfold hdr_init, common.hdr. reflexivity. Qed.

Lemma hdr_init_bridge_valid_only:
  common.hdr (sample_valid_bridge hdr_init) =
    val_to_sval_valid_only
      (updatev "bridge" (bridge_repr_val 0) empty_header).
Proof. unfold sample_valid_bridge, hdr_init, common.hdr. reflexivity. Qed.

Lemma ethernet_extract_result_valid_only:
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val) header vh,
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
    ⊢ᵥ header \: header_sample_t ->
    header = val_to_sval_valid_only vh ->
    exists h, ethernet_extract_result header ether ipv4 result = val_to_sval_valid_only h /\
           h = let ieh := updatev "ipv4" (ipv4_repr_val ipv4)
                            (updatev "ethernet" (ethernet_repr_val ether) vh) in
               if is_tcp ipv4
               then updatev "tcp" result ieh
               else if is_udp ipv4 then updatev "udp" result ieh else ieh.
Proof.
  intros. subst. pose proof H0.
  rewrite to_sval_valid_only_typ_iff in H1.
  unfold ethernet_extract_result, protocol_extract_result.
  assert (⊢ᵥ updatev "ethernet" (ethernet_repr_val ether) vh \: header_sample_t). {
    eapply updatev_struct_typ; eauto; [reflexivity | apply ext_val_typ_ethernet]. }
  assert (⊢ᵥ updatev "ipv4" (ipv4_repr_val ipv4)
            (updatev "ethernet" (ethernet_repr_val ether) vh) \: header_sample_t). {
    eapply updatev_struct_typ; eauto; [reflexivity | apply ext_val_typ_ipv4 ]. }
  remember (updatev "ipv4" (ipv4_repr_val ipv4)
              (updatev "ethernet" (ethernet_repr_val ether) vh)) as ieh.
  assert (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
            (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
               (val_to_sval_valid_only vh)) = val_to_sval_valid_only ieh). {
    rewrite Heqieh; rewrite (ext_val_typ_to_sval_eq (ethernet_repr_val ether) ethernet_h);
      [|apply ext_val_typ_ethernet | reflexivity].
    erewrite <- (update_struct_valid_only "ethernet"); eauto. 2: reflexivity.
    rewrite (ext_val_typ_to_sval_eq (ipv4_repr_val ipv4) ipv4_h);
      [|apply ext_val_typ_ipv4 | reflexivity].
    erewrite <- (update_struct_valid_only "ipv4"); eauto. reflexivity. } rewrite H4.
  destruct (is_tcp ipv4).
  - erewrite ext_val_typ_to_sval_eq with (typ := tcp_h); [| assumption | reflexivity ].
    erewrite <- (update_struct_valid_only "tcp"); eauto. reflexivity.
  - destruct (is_udp ipv4).
    + erewrite ext_val_typ_to_sval_eq with (typ := udp_h); [| assumption | reflexivity ].
      erewrite <- (update_struct_valid_only "udp"); eauto. reflexivity.
    + eexists. split; reflexivity.
Qed.

Lemma ethernet_extract_result_valid_only':
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val) header vh,
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
    ⊢ᵥ header \: header_sample_t ->
    header = val_to_sval_valid_only vh ->
    exists h, ethernet_extract_result header ether ipv4 result = val_to_sval_valid_only h.
Proof.
  intros. pose proof (ethernet_extract_result_valid_only ether _ _ _ _ H H0 H1).
  destruct H2 as [h [? ?]]. exists h. assumption.
Qed.

Lemma ethernet_extract_result_valid_only_vb:
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val),
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
  exists h, ethernet_extract_result
         (common.hdr (sample_valid_bridge hdr_init)) ether ipv4 result =
         val_to_sval_valid_only h /\
         h = let ieh := updatev "ipv4" (ipv4_repr_val ipv4)
                          (updatev "ethernet" (ethernet_repr_val ether)
                             (updatev "bridge" (bridge_repr_val 0) empty_header)) in
             if is_tcp ipv4
             then updatev "tcp" result ieh
             else if is_udp ipv4 then updatev "udp" result ieh else ieh.
Proof.
  intros. apply ethernet_extract_result_valid_only; auto. apply hdr_init_bridge_type.
Qed.

Transparent eval_val_to_sval ipv4_repr_val ethernet_repr_val bridge_repr_val.

Lemma sval_refine_iimt_repr_sval: forall ver port stamp,
  sval_refine
    (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_t))
    (iimt_repr_sval 0 ver port stamp).
Proof.
  intros. unfold iimt_repr_sval. simpl. constructor. constructor.
  do 6 (constructor; [simpl; split; [reflexivity | repeat constructor]|]).
  constructor.
Qed.

Lemma counter_iff:
  forall (s : extern_state) (counter : Z) pa,
    extern_contains s pa counter <-> counter_repr pa counter s.
Proof.
  intros. unfold counter_repr. split; intros.
  - hnf. split; [|simpl; auto]. destruct H. hnf. split; simpl; assumption.
  - hnf in H. destruct H as [H _]. hnf in H. simpl in H.
    destruct H. split; assumption.
Qed.

Definition encode_out_md (port rid: Z): packet :=
  encode
    (output_md_to_egress_intr_md
        {| out_meta_egress_port := port; out_meta_egress_rid := rid |}).

Opaque encode.

Lemma sampler_tofino_tm:
  forall (for_tm : Sval) (counter : Z) (pkt : packet),
    sval_refine
      (if (counter + 1) mod 1024 =? 0
       then
         update "mcast_grp_a" (P4Bit 16 COLLECTOR_MULTICAST_GROUP)
           (update_outport OUT_PORT ig_intr_tm_md)
       else update_outport OUT_PORT ig_intr_tm_md) for_tm ->
    list_rep (tofino_tm for_tm pkt) =
      if (counter + 1) mod 1024 =? 0 then
        [encode_out_md 129 123 ++ pkt; encode_out_md 128 0 ++ pkt]
      else [encode_out_md 128 0 ++ pkt].
Proof.
  intros. unfold update_outport in H. destruct ((counter + 1) mod 1024 =? 0).
  - assert (intr_tm_md_to_input_md for_tm =
              Build_InputMetadata (Some OUT_PORT)
                (Some COLLECTOR_MULTICAST_GROUP) None 0 0 0). {
      unfold intr_tm_md_to_input_md. f_equal.
      + apply sval_refine_get with (f := "ucast_egress_port") in H.
        rewrite get_update_diff in H; [| repeat constructor | discriminate].
        rewrite get_update_same in H; [| repeat constructor].
        unfold P4Bit in H. inv H. apply Forall2_bit_refine_Some_same' in H2.
        subst lb'. reflexivity.
      + apply sval_refine_get with (f := "mcast_grp_a") in H.
        rewrite get_update_same in H; [| repeat constructor].
        unfold P4Bit in H. inv H. apply Forall2_bit_refine_Some_same' in H2.
        subst lb'. reflexivity.
      + apply sval_refine_get with (f := "mcast_grp_b") in H.
        rewrite get_update_diff in H; [| repeat constructor | discriminate].
        rewrite get_update_diff in H; [| repeat constructor | discriminate].
        simpl in H.
        change (ValBaseBit _) with (ValBaseBit (map Some (repeat false 16))) in H.
        remember (repeat false 16) as l. inv H.
        apply Forall2_bit_refine_Some_same' in H2. subst lb'. reflexivity. }
    unfold tofino_tm. rewrite H0. simpl. rewrite rev'_eq. reflexivity.
  - assert (intr_tm_md_to_input_md for_tm =
              Build_InputMetadata (Some OUT_PORT) None None 0 0 0). {
      unfold intr_tm_md_to_input_md. f_equal.
      + apply sval_refine_get with (f := "ucast_egress_port") in H.
        rewrite get_update_same in H; [| repeat constructor].
        unfold P4Bit in H. inv H. apply Forall2_bit_refine_Some_same' in H2.
        subst lb'. reflexivity.
      + apply sval_refine_get with (f := "mcast_grp_a") in H.
        rewrite get_update_diff in H; [| repeat constructor | discriminate].
        simpl in H.
        change (ValBaseBit _) with (ValBaseBit (map Some (repeat false 16))) in H.
        remember (repeat false 16) as l. inv H.
        apply Forall2_bit_refine_Some_same' in H2. subst lb'. reflexivity.
      + apply sval_refine_get with (f := "mcast_grp_b") in H.
        rewrite get_update_diff in H; [| repeat constructor | discriminate].
        simpl in H.
        change (ValBaseBit _) with (ValBaseBit (map Some (repeat false 16))) in H.
        remember (repeat false 16) as l. inv H.
        apply Forall2_bit_refine_Some_same' in H2. subst lb'. reflexivity. }
    unfold tofino_tm. rewrite H0. simpl. reflexivity.
Qed.

Transparent encode.

Lemma sampler_tofino_tm_qlen:
  forall (for_tm : Sval) (counter : Z) (pkt : packet),
    sval_refine
      (if (counter + 1) mod 1024 =? 0
       then
         update "mcast_grp_a" (P4Bit 16 COLLECTOR_MULTICAST_GROUP)
           (update_outport OUT_PORT ig_intr_tm_md)
       else update_outport OUT_PORT ig_intr_tm_md) for_tm ->
    qlength (tofino_tm for_tm pkt) =
      (if (counter + 1) mod 1024 =? 0 then 2 else 1).
Proof.
  intros. apply sampler_tofino_tm with (pkt := pkt) in H.
  rewrite qlength_eq, H. destruct ((counter + 1) mod 1024 =? 0); reflexivity.
Qed.

Opaque ig_intr_tm_md ipv4_repr_val ethernet_repr_val bridge_repr_val sample_repr_val.

Definition empty_sample : sample_rec := Build_sample_rec 0 0 0 0 0 0.

Definition ingress_counter (st: pipeline_state) (counter: Z) : Prop :=
  extern_contains st.(control_state) ["pipe"; "ingress"] counter.

Definition packet_ingress_relation (pin pout: packet) (counter: Z) : Prop :=
  let has_sample := if (counter + 1) mod 1024 =? 0 then 1 else 0 in
  (exists sample ether ipv4 result payload meta,
      ((if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
        else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull)) /\
        P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
        pout ⫢ [⦑ encode (bridge_repr_val has_sample) ⦒;
                ⦃ contains_sample has_sample ? ⦑ encode (sample_repr_val sample) ⦒| ε ⦄;
                ⦑ encode (ethernet_repr_val ether) ⦒;
                ⦑ encode (ipv4_repr_val ipv4) ⦒;
                ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                  ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
        pin ⫢ [ ⦑ meta ⦒;
                ⦑ encode (ethernet_repr_val ether) ⦒;
                ⦑ encode (ipv4_repr_val ipv4) ⦒;
                ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                  ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
        Zlength meta = 128).

Lemma process_packet_ingress:
  forall st st' pin pout for_tm counter,
    ingress_counter st counter ->
    ingress_pipeline
      inprsr_block ingress_block indeprsr_block parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond st pin st' pout for_tm ->
    ingress_counter st' (counter + 1) /\
        sval_refine
          (if (counter + 1) mod 1024 =? 0
           then update "mcast_grp_a" (P4Bit 16 COLLECTOR_MULTICAST_GROUP)
                  (update_outport OUT_PORT ig_intr_tm_md)
           else update_outport OUT_PORT ig_intr_tm_md) for_tm /\
      packet_ingress_relation pin pout counter.
Proof.
  intros st st' pin pout for_tm counter Hext H. unfold ingress_counter in Hext. simpl in Hext.
  inversion H. subst. clear H.
  inv H0. rewrite PathMap.get_set_same in H16. inversion H16. subst pin0; clear H16.
  inv H18. inv H. inv H0. inv H8.
  eapply (proj1 ingress_parser_body) in H20; eauto.
  2: { hnf. split. 1: constructor. hnf. split.
       - hnf. simpl. rewrite H14. split; auto. apply sval_refine_refl.
       - hnf. simpl. rewrite PathMap.get_set_same. intuition. }
  destruct H20. hnf in H. inv H. inv H18. inv H19. clear H20.
  destruct H0 as [_ [_ [H0 _]]]. hnf in H0. rewrite H0 in H1.
  inv H1. inv H3. inv H2. inv H23. inv H. inv H1. inv H2.
  destruct (ethernet_extract_result_hdr ether ipv4 result) as
    [ethernet [tcp [udp [ip4 ?H]]]]. rewrite H in H16.
  eapply (proj1 ingress_body counter ethernet
            tcp udp ip4) in H24; eauto.
  2: { split.
       - hnf. do 2 (constructor; [assumption |]).
         constructor.
         1: { apply sval_refine_trans with (iimt_repr_sval 0 ver port stamp).
              2: assumption. apply sval_refine_iimt_repr_sval. }
         subst ig_intr_prsr_md. constructor; [apply sval_refine_refl|].
         subst ig_intr_dprsr_md1. constructor; [apply sval_refine_refl|].
         constructor; [apply sval_refine_refl | constructor].
       - split. hnf. auto. hnf. split. 2: simpl; auto.
         rewrite <- counter_iff. assumption. }
  destruct H24. hnf in H1. inv H1. inv H20. inv H21. inv H22. clear H23.
  destruct H2 as [_ [_ [H2 _]]]. rewrite <- counter_iff in H2.
  inv H5. inv H4. inv H25. inv H1. inv H3. inv H4.
  remember (if (counter + 1) mod 1024 =? 0
            then update_hdr ethernet tcp udp ip4 (counter + 1)
            else hdr ethernet tcp udp ip4) as igrs_hdr.
  assert (⊢ᵥ hdr ethernet tcp udp ip4 \: header_sample_t). {
    rewrite <- H. apply ethernet_extract_result_typ; assumption. }
  assert (⊢ᵥ igrs_hdr \: header_sample_t). {
    subst igrs_hdr. destruct ((counter + 1) mod 1024 =? 0); [|assumption].
    unfold update_hdr.
    apply update_struct_typ with sample_t; [reflexivity | repeat constructor |].
    apply update_struct_typ with bridge_t; [reflexivity | repeat constructor |].
    apply H1. }
  assert (Hv: exists h, igrs_hdr = val_to_sval_valid_only h /\
                     h = let orig_h :=
                           (let ieh :=
                              updatev "ipv4" (ipv4_repr_val ipv4)
                                (updatev "ethernet" (ethernet_repr_val ether)
                                   (updatev "bridge" (bridge_repr_val 0)
                                      empty_header)) in
                            if is_tcp ipv4
                            then updatev "tcp" result ieh
                            else if is_udp ipv4 then updatev "udp" result ieh else ieh) in
                         if (counter + 1) mod 1024 =? 0 then
                           (updatev "sample"
                              (sample_reprv (P4BitV 32 (ipv4_src_addr ip4))
                                 (P4BitV 32 (ipv4_dst_addr ip4))
                                 (counter + 1)) (updatev "bridge" (bridge_repr_val 1) orig_h))
                         else orig_h). {
    pose proof (ethernet_extract_result_valid_only_vb ether _ _ H11).
    rewrite H in H4. destruct H4 as [orig_h [? ?]]. subst igrs_hdr.
    destruct ((counter + 1) mod 1024 =? 0). 2: (exists orig_h; split; assumption).
    rewrite <- H5. unfold update_hdr.
    assert (⊢ᵥ orig_h \: header_sample_t). {
      apply to_sval_valid_only_typ_iff. rewrite H4 in H1. assumption. }
    assert (⊢ᵥ updatev "bridge" (bridge_repr_val 1) orig_h \: header_sample_t). {
      Transparent bridge_repr_val.
      eapply updatev_struct_typ; eauto; [reflexivity | repeat constructor].
      Opaque bridge_repr_val. }
    exists (updatev "sample"
             (sample_reprv (P4BitV 32 (ipv4_src_addr ip4))
                (P4BitV 32 (ipv4_dst_addr ip4))
                (counter + 1)) (updatev "bridge" (bridge_repr_val 1) orig_h)).
    erewrite !update_struct_valid_only; eauto; [|reflexivity..].
    rewrite H4. split; reflexivity. } destruct Hv as [h [Hv Heqh]].
  assert (⊢ᵥ h \: header_sample_t). {
    apply to_sval_valid_only_typ_iff. rewrite Hv in H3; assumption. }
  eapply (proj1 ingress_deparser_body [] h) in H26; eauto.
  2: { split.
       - hnf. constructor.
         apply sval_refine_trans with igrs_hdr;
           [rewrite Hv; apply sval_refine_refl | assumption].
         constructor. apply H9. constructor. apply H19. constructor.
       - split. 1: hnf; auto. hnf. split. 2: simpl; auto. simpl.
         rewrite PathMap.get_set_same. reflexivity. }
  destruct H26. hnf in H5. inversion H5. subst x l y l'. clear H5 H26.
  destruct H8 as [_ [_ ?]]. simpl in H5. hnf in H5. destruct H5 as [? _]. hnf in H5.
  rewrite H6 in H5. inversion H5. subst pout0. clear H5. split; [|split].
  - apply H2.
  - inv H7. assumption.
  - exists (if (counter + 1) mod 1024 =? 0
       then Build_sample_rec COLLECTOR_MAC MY_MAC SAMPLE_ETYPE (ipv4_src_addr ip4)
              (ipv4_dst_addr ip4) (counter + 1)
       else empty_sample).
    exists ether, ipv4, result, payload.
    cut_list_n_in H13 2%nat. rewrite format_match_app_iff_front in H13.
    destruct H13 as [p1 [p2 [? [? ?]]]]. simpl app in H13.
    exists p1. do 3 (split; auto).
    2: { split; auto. apply format_match_size in H8. simpl in H8.
         rewrite Zlength_correct. rewrite H8. reflexivity. }
    replace (sample_repr_val _) with
      (if (counter + 1) mod 1024 =? 0 then
         (sample_reprv (P4BitV 32 (ipv4_src_addr ip4)) (P4BitV 32 (ipv4_dst_addr ip4))
            (counter + 1)) else
         (sample_repr_val empty_sample)) by (destruct ((counter + 1) mod 1024 =? 0); auto).
    remember (sample_reprv _ _ _) as sample_r.
    cut_list_n 8%nat. rewrite format_match_app_iff. exists (encode h), payload.
    split; [|split]; [reflexivity | | apply format_match_singleton].
    destruct ((counter + 1) mod 1024 =? 0), (is_tcp ipv4), (is_udp ipv4);
      unfold contains_sample; simpl Val_eqb; subst h; simpl; format_match_solve.
Qed.

Lemma process_packet_ingress_tm:
  forall st st' pin pout for_tm counter,
    ingress_counter st counter ->
    ingress_pipeline
      inprsr_block ingress_block indeprsr_block parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond st pin st' pout for_tm ->
    packet_ingress_relation pin pout counter /\
    list_rep (tofino_tm for_tm pout) =
      (if (counter + 1) mod 1024 =? 0 then
         [encode_out_md 129 123 ++ pout; encode_out_md 128 0 ++ pout]
       else [encode_out_md 128 0 ++ pout]).
Proof.
  intros. eapply process_packet_ingress in H0; eauto. destruct H0 as [? [? ?]].
  split; auto. apply sampler_tofino_tm. assumption.
Qed.

Transparent ig_intr_tm_md ipv4_repr_val ethernet_repr_val bridge_repr_val sample_repr_val.

Lemma process_packet_ingress_queue_len:
  forall st st' pin pout for_tm counter que,
    ingress_counter st counter ->
    ingress_pipeline
      inprsr_block ingress_block indeprsr_block parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond st pin st' pout for_tm ->
    que = tofino_tm for_tm pout ->
    qlength que = if ((counter + 1) mod 1024 =? 0) then 2 else 1.
Proof.
  intros. eapply process_packet_ingress in H0; eauto. destruct H0 as [? [? _]].
  subst que. apply sampler_tofino_tm_qlen. assumption.
Qed.

Inductive eprsr_block: programmable_block_sem :=
| eprsr_block_intro:
  forall inst_path m m' es es' fd (pin pin': packet_in) eg_intr_md has_sample sample
    ether ipv4 result hdr eg_md intr_md signal,
    ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t ->
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
    pin ⫢ [⦑ encode eg_intr_md ⦒;
           ⦑ encode (bridge_repr_val has_sample) ⦒;
           ⦃ contains_sample has_sample ? ⦑ encode (sample_repr_val sample) ⦒ | ε ⦄;
           ⦑ encode (ethernet_repr_val ether) ⦒;
           ⦑ encode (ipv4_repr_val ipv4) ⦒;
           ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
             ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] ->
    P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 ->
    PathMap.get ["hdr"] m = Some (common.hdr hdr_init) ->
    PathMap.get ["packet_in"] es = Some (ObjPin pin) ->
    programmable_block ge inst_path "egress_parser" fd ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil [] (m', es')
      [hdr; eg_md; intr_md] signal ->
    eprsr_block es [] es' [hdr; eg_md; intr_md] signal.

Inductive egress_block: programmable_block_sem :=
| egress_block_intro:
  forall inst_path m m' es es' fd hsample hdr1 hdr2 eg_md1 eg_md2 eg_intr_md
    eg_intr_from_prsr eg_intr_md_for_dprsr1 eg_intr_md_for_dprsr2
    eg_intr_md_for_oport1 eg_intr_md_for_oport2 signal,
    PathMap.get ["hdr"] m = Some (common.hdr hsample) ->
    programmable_block ge inst_path "egress" fd ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil
      [hdr1; eg_md1; eg_intr_md; eg_intr_from_prsr;
       eg_intr_md_for_dprsr1; eg_intr_md_for_oport1]
      (m', es') [hdr2; eg_md2; eg_intr_md_for_dprsr2; eg_intr_md_for_oport2] signal ->
    egress_block es
      [hdr1; eg_md1; eg_intr_md; eg_intr_from_prsr;
       eg_intr_md_for_dprsr1; eg_intr_md_for_oport1]
      es' [hdr2; eg_md2; eg_intr_md_for_dprsr2; eg_intr_md_for_oport2] signal.

Inductive edeprsr_block: programmable_block_sem :=
| edeprsr_block_intro:
  forall inst_path m m' es es' fd hdr1 hdr2 eg_md eg_intr_dprsr_md signal,
    programmable_block ge inst_path "egress_deparser" fd ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil
      [hdr1; eg_md; eg_intr_dprsr_md] (m', es') [hdr2] signal ->
    edeprsr_block es [hdr1; eg_md; eg_intr_dprsr_md] es' [hdr2] signal.

Inductive parser_egress_cond: list Sval -> list Sval -> Prop :=
| parser_egress_cond_intro:
  forall eg_intr_md eg_intr_from_prsr eg_intr_md_for_dprsr eg_intr_md_for_oport,
    parser_egress_cond [eg_intr_md]
      [eg_intr_md; eg_intr_from_prsr; eg_intr_md_for_dprsr; eg_intr_md_for_oport].

Inductive egress_deprsr_cond: list Sval -> list Sval -> Prop :=
| egress_deprsr_cond_intro:
  forall eg_intr_md_for_dprsr eg_intr_md_for_oport,
    egress_deprsr_cond [eg_intr_md_for_dprsr; eg_intr_md_for_oport] [eg_intr_md_for_dprsr].

Opaque hdr_init eval_val_to_sval.

Lemma start_extract_result_hdr: forall has_sample sample ether ipv4 result,
    start_extract_result has_sample hdr_init sample ether ipv4 result =
      common.hdr (Build_header_sample_rec
                    (eval_val_to_sval (bridge_repr_val has_sample))
                    (if contains_sample has_sample then eval_val_to_sval (sample_repr_val sample)
                     else (header_sample_sample hdr_init))
                    (eval_val_to_sval (ethernet_repr_val ether))
                    (eval_val_to_sval (ipv4_repr_val ipv4))
                    (if is_tcp ipv4 then eval_val_to_sval result else header_sample_tcp hdr_init)
                    (if is_udp ipv4 then eval_val_to_sval result else header_sample_udp hdr_init)).
Proof.
  intros. unfold start_extract_result. destruct (contains_sample has_sample).
  - unfold sample_extract_result, ethernet_extract_result, protocol_extract_result. simpl.
    destruct (is_tcp ipv4) eqn:?H.
    + apply is_tcp_not_udp in H. rewrite H. reflexivity.
    + destruct (is_udp ipv4); reflexivity.
  - unfold ethernet_extract_result, protocol_extract_result. simpl.
    destruct (is_tcp ipv4) eqn:?H.
    + apply is_tcp_not_udp in H. rewrite H. reflexivity.
    + destruct (is_udp ipv4); reflexivity.
Qed.

Transparent hdr_init eval_val_to_sval.

Lemma eg_intr_rep_exists: forall eg_intr_md,
    ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t -> exists md, eg_intr_md = eg_intr_md_rep md.
Proof.
  intros ? [? ?]. inv H. simpl in *. destruct b; [|discriminate]. clear H2.
  do 25 (inversion_clear H4 as [| [s ?] y ? ? Hr Ha]; simpl in *; destruct Hr as [Hs Hv];
         subst; inversion_clear Hv; rename Ha into H4; clear -H4). inversion H4.
  exists (Build_egress_intrinsic_metadata_rec
       (ValBaseBit v0) (ValBaseBit v1) (ValBaseBit v2) (ValBaseBit v3)
       (ValBaseBit v4) (ValBaseBit v5) (ValBaseBit v6) (ValBaseBit v7)
       (ValBaseBit v8) (ValBaseBit v9) (ValBaseBit v10) (ValBaseBit v11)
       (ValBaseBit v12) (ValBaseBit v13) (ValBaseBit v14) (ValBaseBit v15)
       (ValBaseBit v16) (ValBaseBit v17) (ValBaseBit v18) (ValBaseBit v19)
       (ValBaseBit v20) (ValBaseBit v21) (ValBaseBit v22) (ValBaseBit v23)
       (ValBaseBit v24)). reflexivity.
Qed.

Definition val_egress_rid_zero (eg_intr_md: Val) :=
  Val_eqb (getv "egress_rid" eg_intr_md) (P4BitV 16 0).

Lemma eg_intr_rep_zero: forall eg_intr_md md,
    eg_intr_md = eg_intr_md_rep md -> val_egress_rid_zero eg_intr_md = egress_rid_zero md.
Proof.
  intros. subst. unfold eg_intr_md_rep, val_egress_rid_zero, egress_rid_zero. simpl.
  reflexivity.
Qed.

Lemma start_extract_result_typ: forall has_sample sample ether ipv4 result,
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
    ⊢ᵥ start_extract_result has_sample hdr_init sample ether ipv4 result \: header_sample_t.
Proof.
  intros. unfold start_extract_result. destruct (contains_sample has_sample).
  - unfold sample_extract_result, ethernet_extract_result.
    apply protocol_extract_result_typ; auto.
    apply update_struct_typ with ipv4_h; [reflexivity | repeat constructor |].
    apply update_struct_typ with ethernet_h; [reflexivity | repeat constructor |].
    apply update_struct_typ with sample_t; [reflexivity | repeat constructor |].
    apply update_struct_typ with bridge_t; [reflexivity | repeat constructor |].
    apply hdr_init_type.
  - unfold ethernet_extract_result.
    apply protocol_extract_result_typ; auto.
    apply update_struct_typ with ipv4_h; [reflexivity | repeat constructor |].
    apply update_struct_typ with ethernet_h; [reflexivity | repeat constructor |].
    apply update_struct_typ with bridge_t; [reflexivity | repeat constructor |].
    apply hdr_init_type.
Qed.

Lemma start_extract_result_valid_only: forall has_sample sample ether ipv4 result,
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
    start_extract_result has_sample hdr_init sample ether ipv4 result =
      val_to_sval_valid_only (let ieh :=
                                updatev "ipv4" (ipv4_repr_val ipv4)
                                  (updatev "ethernet" (ethernet_repr_val ether)
                                     ((if contains_sample has_sample then
                                         updatev "sample" (sample_repr_val sample) else id)
                                        (updatev "bridge" (bridge_repr_val has_sample) empty_header))) in
                              if is_tcp ipv4
                              then updatev "tcp" result ieh
                              else if is_udp ipv4 then updatev "udp" result ieh else ieh).
Proof.
  intros. unfold start_extract_result. pose proof hdr_init_valid_only.
  assert (⊢ᵥ common.hdr hdr_init \: header_sample_t) by repeat constructor.
  rewrite H0 in *. pose proof H1. rewrite to_sval_valid_only_typ_iff in H2.
  assert (⊢ᵥ updatev "bridge" (bridge_repr_val has_sample) empty_header \: header_sample_t). {
    eapply updatev_struct_typ; eauto. reflexivity. apply ext_val_typ_bridge. }
  destruct (contains_sample has_sample).
  - unfold sample_extract_result. remember (update "sample" _ _) as v.
    assert (⊢ᵥ v \: header_sample_t). {
      subst v. apply update_struct_typ with sample_t. 1: reflexivity.
      - rewrite to_sval_typ_iff. apply ext_val_typ_sample.
      - apply update_struct_typ with bridge_t; [reflexivity | | assumption].
        rewrite to_sval_typ_iff. apply ext_val_typ_bridge. }
    assert (v = val_to_sval_valid_only
                  (updatev "sample" (sample_repr_val sample)
                     (updatev "bridge" (bridge_repr_val has_sample) empty_header))). {
      subst v. rewrite (ext_val_typ_to_sval_eq (bridge_repr_val has_sample) bridge_t);
        [|apply ext_val_typ_bridge | reflexivity].
      erewrite <- (update_struct_valid_only "bridge"); eauto. reflexivity. }
    destruct (ethernet_extract_result_valid_only ether ipv4 result v _ H H4 H5) as [h [? ?]].
    rewrite H6. f_equal. subst h. reflexivity.
  - remember (update "bridge" _ _) as v.
    assert (⊢ᵥ v \: header_sample_t). {
      subst v. apply update_struct_typ with bridge_t; [reflexivity | | assumption].
      rewrite to_sval_typ_iff. apply ext_val_typ_bridge. }
    assert (v = val_to_sval_valid_only
                  (updatev "bridge" (bridge_repr_val has_sample) empty_header)). {
      subst v. rewrite ext_val_typ_to_sval_eq with (typ := bridge_t);
        [|apply ext_val_typ_bridge | reflexivity].
      erewrite <- (update_struct_valid_only "bridge"); eauto. reflexivity. }
    destruct (ethernet_extract_result_valid_only ether ipv4 result v _ H H4 H5) as [h [? ?]].
    rewrite H6. f_equal. subst h. reflexivity.
Qed.

Lemma conditional_update_ex_valid_only: forall md h vh,
    ⊢ᵥ common.hdr h \: header_sample_t ->
    common.hdr h = val_to_sval_valid_only vh ->
    exists hd, sval_refine (val_to_sval_valid_only hd) (conditional_update md h) /\
            hd = invalidate_fieldsv vh (if egress_rid_zero md then ["bridge"; "sample"]
                                        else ["bridge"; "ethernet"; "ipv4"]).
Proof.
  intros. unfold conditional_update. rewrite H0.
  assert (⊢ᵥ vh \: header_sample_t). {
    rewrite <- to_sval_valid_only_typ_iff, <- H0. assumption. }
  destruct (egress_rid_zero md).
  - exists (invalidate_fieldsv vh ["bridge"; "sample"]). split; auto.
    eapply invalidate_fields_valid_only; eauto; reflexivity.
  - exists (invalidate_fieldsv vh ["bridge"; "ethernet"; "ipv4"]). split; auto.
    eapply invalidate_fields_valid_only; eauto; reflexivity.
Qed.

Lemma conditional_update_typ: forall md h,
    ⊢ᵥ common.hdr h \: header_sample_t -> ⊢ᵥ conditional_update md h \: header_sample_t.
Proof.
  intros. unfold conditional_update. destruct (egress_rid_zero md);
    apply invalidate_fields_typ; [reflexivity | assumption | reflexivity | assumption].
Qed.

Lemma encode_invalid_sample: forall sample, encode (setInvalidv (sample_repr_val sample)) = [].
Proof. intros. reflexivity. Qed.

Lemma encode_invalid_ether: forall ether, encode (setInvalidv (ethernet_repr_val ether)) = [].
Proof. intros. reflexivity. Qed.

Lemma encode_invalid_ipv4: forall ipv4, encode (setInvalidv (ipv4_repr_val ipv4)) = [].
Proof. intros. reflexivity. Qed.

Definition egress_packet_relation (pin pout: packet) : Prop :=
  exists eg_intr_md has_sample sample ether ipv4 result payload,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) /\
      P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
      pin
        ⫢ [⦑ encode eg_intr_md ⦒; ⦑ encode (bridge_repr_val has_sample) ⦒;
           ⦃ contains_sample has_sample ? ⦑ encode (sample_repr_val sample) ⦒ | ε ⦄;
           ⦑ encode (ethernet_repr_val ether) ⦒; ⦑ encode (ipv4_repr_val ipv4) ⦒;
           ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
           ⦑ payload ⦒] /\
      (if val_egress_rid_zero eg_intr_md then
         pout ⫢ [⦑ encode (ethernet_repr_val ether) ⦒; ⦑ encode (ipv4_repr_val ipv4) ⦒;
                 ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
                 ⦑ payload ⦒]
       else pout ⫢ [⦃ contains_sample has_sample ? ⦑ encode (sample_repr_val sample) ⦒ | ε ⦄;
                    ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
                    ⦑ payload ⦒]) /\
      ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t.

Lemma process_packet_egress:
  forall st st' pin pout,
    egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
      egress_deprsr_cond st pin st' pout -> egress_packet_relation pin pout.
Proof.
  intros. inv H. inv H0. rewrite PathMap.get_set_same in H15. inversion H15. subst pin0.
  clear H15. inv H17. inv H. inv H0. inv H7.
  eapply (proj1 egress_parser_body) in H19; eauto.
  2: { hnf. split. 1: constructor. hnf. split; hnf; simpl.
       - rewrite H13. split; auto. apply sval_refine_refl.
       - rewrite PathMap.get_set_same. intuition. }
  destruct H19. hnf in H. inv H. inv H17. inv H18. clear H19.
  destruct H0 as [_ [_ [H0 _]]]. hnf in H0. rewrite H0 in H1.
  inv H1. inv H3. inv H2. assert (eg_intr_md0 = eval_val_to_sval eg_intr_md). {
    apply exec_val_eval_val_to_sval_eq in H16; auto. intros. inv H. reflexivity. }
  subst eg_intr_md0. clear H16. inv H23. inv H. inv H1. inv H2.
  pose proof (start_extract_result_hdr has_sample sample ether ipv4 result).
  destruct (eg_intr_rep_exists _ H9) as [md ?H]. subst eg_intr_md.
  eapply (proj1 egress_body _ eg_md1 md) in H24; eauto.
  2: { split; [hnf | split; hnf; auto]. constructor; [rewrite <- H; assumption |].
       do 5 (constructor; [apply sval_refine_refl|]). constructor. }
  remember (Build_header_sample_rec _ _ _ _ _ _) as h.
  destruct H24 as [? _]. hnf in H1. inv H1. inv H17. inv H18. inv H19. clear H20.
  inv H5. inv H4. inv H23. inv H1. inv H2. inv H3.
  remember (Build_header_sample_rec _ _ _ _ _ _) as h.
  assert (⊢ᵥ common.hdr h \: header_sample_t). {
    rewrite <- H. apply start_extract_result_typ; assumption. }
  pose proof (start_extract_result_valid_only has_sample sample ether ipv4 result H10).
  rewrite H in H2.
  destruct (conditional_update_ex_valid_only md _ _ H1 H2) as [hd [?H Hhd]].
  assert (⊢ᵥ hd \: header_sample_t). {
    rewrite <- to_sval_valid_only_typ_iff. apply val_sim_on_top in H3.
    rewrite (val_sim_prsv_typ _ _ _ H3). apply conditional_update_typ. assumption. }
  eapply (proj1 egress_deparser_body _ hd eg_md1 eg_intr_md_for_dprsr1) in H24; eauto.
  2: { hnf. split.
       - constructor. eapply sval_refine_trans; eauto.
         do 2 (constructor; [assumption|]). constructor.
       - split; hnf; auto. split; simpl; auto. rewrite PathMap.get_set_same; reflexivity. }
  destruct H24. inversion H5. subst x l y l'. clear H5 H25. destruct H18 as [_ [_ ?]]. destruct H5 as [? _].
  simpl in H5. change (@extern_object Info (@Expression Info)
                         (@extern_sem Info (@Expression Info) target)) with
    (@object (@Expression Info)) in H6. rewrite H6 in H5. inversion H5. subst pout0. clear H5.
  exists (eg_intr_md_rep md), has_sample, sample, ether, ipv4, result, payload. do 4 (split; auto).
  erewrite eg_intr_rep_zero by reflexivity.
  Opaque P4BitV ethernet_repr_val ipv4_repr_val sample_repr_val.
  destruct (egress_rid_zero); rewrite Hhd; destruct (is_tcp ipv4),
    (contains_sample has_sample), (is_udp ipv4); simpl;
    rewrite app_nil_r, ?encode_invalid_sample, ?encode_invalid_ether,
    ?encode_invalid_ipv4; repeat rewrite <- app_assoc; simpl app; format_match_solve.
  Transparent P4BitV ethernet_repr_val ipv4_repr_val sample_repr_val.
Qed.

Lemma process_egress_packets_queue: forall est1 q1 est2 q2,
  process_egress_packets
    (egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
       egress_deprsr_cond) est1 q1 est2 q2 ->
  forall pin, In pin (list_rep q1) -> exists pout, In pout (list_rep q2) /\ egress_packet_relation pin pout.
Proof.
  intros. induction H. 1: simpl in H0; inversion H0. rewrite enque_eq, in_app_iff in H0.
  rename IHprocess_egress_packets into IH. destruct H0.
  - specialize (IH H0). destruct IH as [pout [? ?]]. exists pout. split; auto. rewrite enque_eq, in_app_iff.
    left; assumption.
  - simpl in H0. destruct H0; inversion H0. subst. clear H2 IH.
    apply process_packet_egress in H1. exists p'. split; auto. rewrite enque_eq, in_app_iff. right. left; reflexivity.
Qed.

Lemma process_egress_packets_queue_len: forall est1 q1 est2 q2,
  process_egress_packets
    (egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
       egress_deprsr_cond) est1 q1 est2 q2 -> qlength q1 = qlength q2.
Proof.
  intros. induction H. reflexivity.
  rewrite !qlength_enque. rewrite IHprocess_egress_packets. reflexivity.
Qed.

Lemma process_ingress_packets_counter: forall inst1 inst2 q1 q2 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    ingress_counter inst2 (counter + qlength q1).
Proof.
  intros. revert H. induction H0; intros.
  - simpl. rewrite Z.add_0_r. assumption.
  - apply IHprocess_ingress_packets in H1.
    eapply process_packet_ingress in H; eauto. destruct H as [? _].
    rewrite qlength_enque, Z.add_assoc. assumption.
Qed.


Lemma process_ingress_packets_queue_len: forall inst1 inst2 q1 q2 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    qlength q2 = qlength q1 + (counter mod 1024 + qlength q1) / 1024.
Proof.
  intros. assert (Hlt: 0 <= counter) by (destruct H; assumption).
  revert H. induction H0; intros.
  - simpl. rewrite Z.add_0_r, Z.div_small; auto. apply Z.mod_pos_bound. lia.
  - specialize (IHprocess_ingress_packets H1).
    rewrite qlength_concat, IHprocess_ingress_packets, qlength_enque.
    assert (ingress_counter st2 (counter + qlength ps)). {
        eapply process_ingress_packets_counter; eauto. }
    rewrite (process_packet_ingress_queue_len _ _ _ _ _ _ _ H2 H eq_refl).
    rewrite <- !Z.add_assoc. f_equal. rewrite !Z.add_assoc.
    remember (qlength ps) as n. pose proof (qlength_nonneg ps). rewrite <- Heqn in H3.
    clear -Hlt H3. pose proof (Z.div_mod counter 1024 ltac:(lia)).
    remember (counter / 1024) as q. remember (counter mod 1024) as m. rewrite H.
    replace (1024 * q + m + n + 1) with ((m + n + 1) + q * 1024) by lia.
    rewrite Z_mod_plus_full.
    pose proof (Z.mod_pos_bound counter 1024 ltac:(lia)). rewrite <- Heqm in H0.
    assert (0 <= m + n) by lia. remember (m + n) as a. clear -H1.
    pose proof (Z.div_mod (a + 1) 1024 ltac:(lia)). remember ((a + 1) mod 1024) as r.
    remember ((a + 1) / 1024) as q. replace a with (r - 1 + q * 1024) by lia.
    rewrite Z.div_add by lia. pose proof (Z.mod_pos_bound (a + 1) 1024 ltac:(lia)).
    rewrite <- Heqr in H0. clear -H0. destruct (r =? 0) eqn:?H.
    + rewrite Z.eqb_eq in H. subst. replace ((0 - 1) / 1024) with (-1) by reflexivity. lia.
    + rewrite Z.eqb_neq in H. rewrite Z.div_small by lia. lia.
Qed.

Lemma process_ingress_packets_queue_len_ugly: forall inst1 inst2 q1 q2 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    qlength q2 = if qlength q1 =? 0 then 0 else
                   qlength q1 + ((counter + 1) mod 1024 + qlength q1 - 1) / 1024 +
                     Z.b2z ((counter + 1) mod 1024 =? 0).
Proof.
  intros. assert (Hlt: 0 <= counter) by (destruct H; assumption).
  revert H. induction H0; intros. 1: simpl; reflexivity.
  rewrite qlength_enque. assert (qlength ps + 1 =? 0 = false). {
    rewrite Z.eqb_neq. pose proof (qlength_nonneg ps). lia. } rewrite H2. clear H2.
  specialize (IHprocess_ingress_packets H1). rewrite qlength_concat.
  rewrite IHprocess_ingress_packets. rewrite <- !Z.add_sub_assoc. simpl. rewrite Z.add_0_r.
  destruct (qlength ps =? 0) eqn:?.
  - rewrite Z.eqb_eq in Heqb. rewrite Heqb.
    apply qlength_0_iff in Heqb, IHprocess_ingress_packets. subst.
    inv H0. 2: destruct ps; simpl in H2; discriminate.
    rewrite (process_packet_ingress_queue_len _ _ _ _ _ _ _ H1 H eq_refl).
    rewrite Z.add_0_r, Z.div_small by (apply Z.mod_pos_bound; lia).
    destruct ((counter + 1) mod 1024 =? 0); simpl; reflexivity.
  - assert (ingress_counter st2 (counter + qlength ps)). {
        eapply process_ingress_packets_counter; eauto. }
    rewrite (process_packet_ingress_queue_len _ _ _ _ _ _ _ H2 H eq_refl).
    remember (qlength ps) as n.
    cut (((counter + 1) mod 1024 + (n - 1))/1024 +
           (if (counter + n + 1) mod 1024 =? 0 then 2 else 1) =
           1 + ((counter + 1) mod 1024 + n) / 1024). 1: intros; lia.
    rewrite Z.eqb_neq in Heqb.
    pose proof (qlength_nonneg ps). rewrite <- Heqn in H3. assert (1 <= n) by lia.
    clear -Hlt H4. pose proof (Z.div_mod (counter + 1) 1024 ltac:(lia)).
    remember ((counter + 1) / 1024) as q. remember ((counter + 1) mod 1024) as m.
    replace (counter + n + 1) with (counter + 1 + n) by lia. rewrite H.
    replace (1024 * q + m + n) with ((m + n) + q * 1024) by lia. rewrite Z_mod_plus_full.
    pose proof (Z.mod_pos_bound (counter + 1) 1024 ltac:(lia)). rewrite <- Heqm in H0.
    rewrite Z.add_sub_assoc. assert (0 <= m + n - 1) by lia.
    remember (m + n - 1) as a. replace (m + n) with (a + 1) by lia. clear -H1.
    pose proof (Z.div_mod (a + 1) 1024 ltac:(lia)). remember ((a + 1) mod 1024) as r.
    remember ((a + 1) / 1024) as q. replace a with (r - 1 + q * 1024) by lia.
    rewrite Z.div_add by lia. pose proof (Z.mod_pos_bound (a + 1) 1024 ltac:(lia)).
    rewrite <- Heqr in H0. clear -H0. destruct (r =? 0) eqn:?H.
    + rewrite Z.eqb_eq in H. subst. replace ((0 - 1) / 1024) with (-1) by reflexivity. lia.
    + rewrite Z.eqb_neq in H. rewrite Z.div_small by lia. lia.
Qed.

Definition ingress_normal_packet_relation (pin pout: packet): Prop :=
  exists has_sample sample ether ipv4 result payload meta,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) /\
      P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
      pout ⫢ [⦑ encode_out_md 128 0 ⦒;
              ⦑ encode (bridge_repr_val has_sample) ⦒;
              ⦃ contains_sample has_sample ?
                  ⦑ encode (sample_repr_val sample) ⦒| ε ⦄;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      pin ⫢ [ ⦑ meta ⦒;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      Zlength meta = 128.

Definition ingress_queue_property1 (q1 q2: queue packet): Prop :=
    forall pin, In pin (list_rep q1) ->
           exists pout, In pout (list_rep q2) /\ ingress_normal_packet_relation pin pout.

Definition ingress_special_packet_relation (pin pout: packet): Prop :=
  exists sample ether ipv4 result payload meta,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) /\
      P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
      pout ⫢ [⦑ encode_out_md 129 123 ⦒;
              ⦑ encode (bridge_repr_val 1) ⦒;
              ⦑ encode (sample_repr_val sample) ⦒;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      pin ⫢ [ ⦑ meta ⦒;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      Zlength meta = 128.

Definition ingress_queue_property2 (q1 q2: queue packet) (counter: Z): Prop :=
  forall i pin, 0 <= i < qlength q1 -> Znth i (list_rep q1) = pin ->
           (counter + i + 1) mod 1024 = 0 ->
           exists pout, In pout (list_rep q2) /\ ingress_special_packet_relation pin pout.

Lemma process_ingress_packets_queue: forall inst1 inst2 q1 q2 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    ingress_queue_property1 q1 q2 /\ ingress_queue_property2 q1 q2 counter.
Proof.
  intros. split.
  - hnf. intros. revert H. induction H0; intros. 1: simpl in H1; contradiction.
    rewrite enque_eq, in_app_iff in H1. destruct H1.
    + specialize (IHprocess_ingress_packets H1 H2).
      destruct IHprocess_ingress_packets as (pout & ? & ?).
      exists pout. split; auto. rewrite concat_queue_eq, in_app_iff. left; assumption.
    + clear IHprocess_ingress_packets. hnf in H1. destruct H1; [subst p | inversion H1].
      pose proof (process_ingress_packets_counter _ _ _ _ _ H2 H0).
      eapply process_packet_ingress_tm in H; eauto. destruct H as [? ?]. hnf in H.
      remember (if (counter + qlength ps + 1) mod 1024 =? 0  then _ else _) as has_sample.
      destruct H as (sample & ether & ipv4 & result & payload & meta & ? & ? & ? & ?).
      exists (encode_out_md 128 0 ++ p'). split.
      * rewrite concat_queue_eq, in_app_iff. right. rewrite H3.
        destruct ((counter + qlength ps + 1) mod 1024 =? 0); [right|]; left; reflexivity.
      * exists has_sample, sample, ether, ipv4, result, payload, meta. repeat (split; auto).
        format_match_solve. assumption.
  - hnf. intros. assert (0 <= i + 1 <= qlength q1) by lia.
    destruct (process_ingress_packets_split _ _ _ _ _ _ H0 _ H4) as
      [qin [qin_rest [qout [qout_rest [inst3 [? [? [? [? _]]]]]]]]].
    assert (Znth i (list_rep qin) = pin). {
      subst q1. rewrite concat_queue_eq in H2. rewrite qlength_eq in H5. list_solve. }
    cut (exists pout : packet, In pout (list_rep qout) /\
                            ingress_special_packet_relation pin pout). {
      intros. destruct H10 as (pout & ? & ?).
      exists pout. split; auto. subst q2. rewrite concat_queue_eq, in_app_iff. left; assumption. }
    destruct H1. clear dependent q1. clear dependent q2. clear qin_rest qout_rest inst2.
    revert dependent i. revert dependent counter. revert pin. inversion H8; subst; clear H8; intros.
    1: simpl in H5; lia. rewrite qlength_enque, qlength_eq in H5. rewrite enque_eq in H9.
    assert (p = pin) by list_solve. assert (Zlength (list_rep ps) = i) by lia. subst p. clear H5 H9.
    pose proof (process_ingress_packets_counter _ _ _ _ _ H1 H). rewrite qlength_eq, H6 in H4.
    eapply process_packet_ingress_tm in H0; eauto. destruct H0 as [? ?]. hnf in H0.
    rewrite H3, Z.eqb_refl in H0, H5. destruct H0 as (sample & ether & ipv4 & result & payload & meta & ? & ? & ? & ?).
    exists (encode_out_md 129 123 ++ p'). split.
    + rewrite concat_queue_eq, in_app_iff, H5. right. left. reflexivity.
    + exists sample, ether, ipv4, result, payload, meta.
      do 3 (split; auto). format_match_solve.
      assert (contains_sample 1 = true) by reflexivity.
      rewrite H10 in H8. eapply format_list_equiv_match; eauto.
      apply list_equiv_cons; [apply format_equiv_refl|].
      apply list_equiv_cons; [apply format_equiv_true|].
      apply format_list_equiv_refl.
Qed.

Definition switch_normal_packet_relation (pin pout: packet) : Prop :=
  exists ether ipv4 result payload meta,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) /\
      P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
      pout ⫢ [⦑ encode (ethernet_repr_val ether) ⦒; ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
              ⦑ payload ⦒] /\
      pin ⫢ [ ⦑ meta ⦒;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      Zlength meta = 128.

Definition switch_queue_property1 (q1 q2: queue packet): Prop :=
    forall pin, In pin (list_rep q1) ->
           exists pout, In pout (list_rep q2) /\ switch_normal_packet_relation pin pout.

Definition switch_special_packet_relation (pin pout: packet): Prop :=
  exists sample ether ipv4 result payload meta,
    (if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) /\
      P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4 /\
      pout ⫢ [⦑ encode (sample_repr_val sample) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      pin ⫢ [ ⦑ meta ⦒;
              ⦑ encode (ethernet_repr_val ether) ⦒;
              ⦑ encode (ipv4_repr_val ipv4) ⦒;
              ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ payload ⦒] /\
      Zlength meta = 128.

Definition switch_queue_property2 (q1 q2: queue packet) (counter: Z): Prop :=
  forall i pin, 0 <= i < qlength q1 -> Znth i (list_rep q1) = pin -> (counter + i + 1) mod 1024 = 0 ->
           exists pout, In pout (list_rep q2) /\ switch_special_packet_relation pin pout.

(* Print egress_packet_relation. *)

Opaque encode ig_intr_tm_md ipv4_repr_val ethernet_repr_val bridge_repr_val sample_repr_val.

Ltac remember_P4BitV :=
  lazymatch goal with
  | H: context [(P4BitV ?n ?V)] |- _ => remember (P4BitV n V)
  end.

Lemma normal_ingress_egress_switch: forall pin pmid pout : packet,
    ingress_normal_packet_relation pin pmid ->
    egress_packet_relation pmid pout -> switch_normal_packet_relation pin pout.
Proof.
  intros. destruct H as (has_sample & sample & ether & ipv4 & result &
                           payload & meta & ? & ? & ? & ? & ?).
  exists ether, ipv4, result, payload, meta. do 3 (split; auto).
  destruct H0 as (eg_intr_md & has_sample' & sample' & ether' & ipv4' &
                    result' & payload' & ? & ? & ? & ? & ?).
  clear pin H3. destruct H2 as [l1 [Hc1 ?]]. destruct H6 as [l2 [Hc2 ?]].
  inv H2. inv H10. inv H3. inv H9. simpl in Hc2.
  eapply encode_same_type_same_val_app in Hc2; eauto. 2: apply output_is_eg_intr_md.
  destruct Hc2. subst. clear H8. simpl in H7.
  inv H12. inv H8. inv H11. inv H8. simpl in H3.
  eapply encode_same_type_same_val_app in H3; [|apply ext_val_typ_bridge..|reflexivity].
  destruct H3. assert (contains_sample has_sample = contains_sample has_sample'). {
      Transparent bridge_repr_val. unfold bridge_repr_val in H2. do 2 remember_P4BitV.
      inv H2. unfold contains_sample. rewrite H8. Opaque bridge_repr_val. reflexivity. }
  rewrite <- H6 in *. clear H6 H2.
  inv H10. inv H12. simpl in H3. assert (concat l'1 = concat l'0). {
    clear H7 H11 H13. destruct (contains_sample has_sample).
    - inv H8. inv H9. inv H10. inv H8.
      eapply encode_same_type_same_val_app in H3; [|apply ext_val_typ_sample..|reflexivity].
      destruct H3; auto.
    - inv H8. inv H9. inv H10. inv H8. simpl in H3. assumption. }
  clear dependent y0. clear dependent y.
  inv H11. inv H13. inv H8. inv H9. simpl in H2.
  eapply encode_same_type_same_val_app in H2; [|apply ext_val_typ_ethernet..|reflexivity].
  destruct H2. rewrite H2 in *. clear H2. inv H10. inv H12. inv H8. inv H9. simpl in H3.
  eapply encode_same_type_same_val_app in H3; [|apply ext_val_typ_ipv4..|reflexivity].
  destruct H3. rewrite H2 in *.
  assert (is_tcp ipv4' = is_tcp ipv4). {
    Transparent ipv4_repr_val. unfold ipv4_repr_val in H2. unfold is_tcp.
    Opaque ipv4_repr_val. do 24 remember_P4BitV. inversion H2. reflexivity. }
  rewrite H6 in *. clear H6.
  assert (is_udp ipv4' = is_udp ipv4). {
    Transparent ipv4_repr_val. unfold ipv4_repr_val in H2. unfold is_udp.
    Opaque ipv4_repr_val. do 24 remember_P4BitV. inversion H2. reflexivity. }
  rewrite H6 in *. clear H6 H2. inv H11. inv H13. inv H10. inv H12. inv H14. inv H15.
  simpl in H3. assert (result = result' /\ y0 = y). {
    destruct (is_tcp ipv4).
    - inv H8; inv H9; inv H12; inv H13.
      eapply encode_same_type_same_val_app in H3; eauto. destruct H3.
      subst. split; auto.
    - inv H8. inv H9. destruct (is_udp ipv4); inv H12; inv H13.
      + inv H9; inv H12. eapply encode_same_type_same_val_app in H3; eauto.
        destruct H3. subst; split; auto.
      + inv H9. inv H6. split; auto. } destruct H2. subst result'. subst y0.
  apply app_inv_head in H3. inversion H11. subst p. subst y1. clear H11. inversion H10.
  subst p. subst y2. clear H10. rewrite !app_nil_r in H3. rewrite H3 in *. assumption.
Qed.

Lemma special_ingress_egress_switch: forall pin pmid pout : packet,
    ingress_special_packet_relation pin pmid ->
    egress_packet_relation pmid pout -> switch_special_packet_relation pin pout.
Proof.
  intros. destruct H as (sample & ether & ipv4 & result & payload &
                           meta & ? & ? & ? & ? & ?).
  exists sample, ether, ipv4, result, payload, meta. do 3 (split; auto).
  destruct H0 as (eg_intr_md & has_sample' & sample' & ether' & ipv4' &
                    result' & payload' & ? & ? & ? & ? & ?). clear pin H1 H3 H4 H5.
  destruct H2 as [l1 [Hc1 ?]]. destruct H6 as [l2 [Hc2 ?]].
  inv H1. inv H2. inv H4. inv H5. simpl in Hc2.
  eapply encode_same_type_same_val_app in Hc2; eauto. 2: apply output_is_eg_intr_md.
  destruct Hc2. subst. clear H8. simpl in H7. inv H9. inv H10. inv H4. inv H5. simpl in H2.
  eapply encode_same_type_same_val_app in H2; [|apply ext_val_typ_bridge..|reflexivity].
  destruct H2. assert (contains_sample has_sample' = true). {
    Transparent bridge_repr_val. unfold bridge_repr_val in H1. do 2 remember_P4BitV.
    inv H1. unfold contains_sample. rewrite H4. Opaque bridge_repr_val. reflexivity. }
  rewrite H3 in *. clear H1 H3. inv H6. inv H9. inv H4. inv H5. inv H6. simpl in H2.
  eapply encode_same_type_same_val_app in H2; [|apply ext_val_typ_sample..|reflexivity].
  destruct H2. rewrite H1 in *. clear H1. inv H8. inv H10. inv H4. inv H5. simpl in H2.
  eapply encode_same_type_same_val_app in H2; [|apply ext_val_typ_ethernet..|reflexivity].
  destruct H2. clear H1. inv H6. inv H9. inv H4. inv H5. simpl in H2.
  eapply encode_same_type_same_val_app in H2; [|apply ext_val_typ_ipv4..|reflexivity].
  destruct H2. assert (is_tcp ipv4' = is_tcp ipv4). {
    Transparent ipv4_repr_val. unfold ipv4_repr_val in H1. unfold is_tcp.
    Opaque ipv4_repr_val. do 24 remember_P4BitV. inversion H1. reflexivity. }
  rewrite H3 in *. assert (is_udp ipv4' = is_udp ipv4). {
    Transparent ipv4_repr_val. unfold ipv4_repr_val in H1. unfold is_udp.
    Opaque ipv4_repr_val. do 24 remember_P4BitV. inversion H1. reflexivity. }
  rewrite H4 in *. clear H1 H3 H4. inv H8. inv H10. inv H6. inv H9. inv H11. inv H12.
  simpl in H2. assert (result = result' /\ y0 = y). {
    destruct (is_tcp ipv4).
    - inv H4; inv H5; inv H9; inv H10. eapply encode_same_type_same_val_app in H2; eauto.
      destruct H2. subst. split; auto.
    - inv H4. inv H5. destruct (is_udp ipv4); inv H9; inv H10.
      + inv H5; inv H9. eapply encode_same_type_same_val_app in H2; eauto.
        destruct H2. subst; split; auto.
      + inv H3. inv H5. split; auto. } destruct H1. subst result'. subst y0.
  apply app_inv_head in H2. inversion H8. subst p. subst y1. clear H8. inversion H6.
  subst p. subst y2. clear H6. rewrite !app_nil_r in H2. rewrite H2 in *.
  eapply format_list_equiv_match; eauto.
  apply list_equiv_cons; [apply format_equiv_true | apply format_list_equiv_refl].
Qed.

Lemma switch_packets_queue: forall inst1 inst2 est1 est2 q1 q2 q3 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    process_egress_packets
      (egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
         egress_deprsr_cond) est1 q2 est2 q3 ->
    switch_queue_property1 q1 q3 /\ switch_queue_property2 q1 q3 counter.
Proof.
  intros. eapply process_ingress_packets_queue in H0; eauto. destruct H0.
  pose proof (process_egress_packets_queue _ _ _ _ H1). split.
  - repeat intro. specialize (H0 _ H4). destruct H0 as (pmid & ? & ?).
    specialize (H3 pmid H0). destruct H3 as [pout [? ?]].
    exists pout. split; auto. eapply normal_ingress_egress_switch; eauto.
  - repeat intro. specialize (H2 _ _ H4 H5 H6). clear i H4 H5 H6.
    destruct H2 as (pmid & ? & ?). specialize (H3 pmid H2). destruct H3 as [pout [? ?]].
    exists pout. split; auto. eapply special_ingress_egress_switch; eauto.
Qed.

Inductive ingress_ideal_property (counter: Z): queue packet -> queue packet -> Prop :=
| ingress_ideal_nil: ingress_ideal_property counter empty_queue empty_queue
| ingress_ideal_normal: forall q1 q2 pin pout,
    ingress_normal_packet_relation pin pout ->
    (counter + qlength q1 + 1) mod 1024 <> 0 ->
    ingress_ideal_property counter q1 q2 ->
    ingress_ideal_property counter (enque pin q1) (enque pout q2)
| ingress_ideal_special: forall q1 q2 pin pout1 pout2,
    ingress_normal_packet_relation pin pout1 ->
    ingress_special_packet_relation pin pout2 ->
    (counter + qlength q1 + 1) mod 1024 = 0 ->
    ingress_ideal_property counter q1 q2 ->
    ingress_ideal_property counter (enque pin q1) (enque pout1 (enque pout2 q2)).

Inductive egress_ideal_property: queue packet -> queue packet -> Prop :=
| egress_ideal_nil: egress_ideal_property empty_queue empty_queue
| egress_ideal_cons: forall q1 q2 pin pout,
    egress_packet_relation pin pout ->
    egress_ideal_property q1 q2 ->
    egress_ideal_property (enque pin q1) (enque pout q2).

Inductive switch_ideal_property (counter: Z): queue packet -> queue packet -> Prop :=
| switch_ideal_nil: switch_ideal_property counter empty_queue empty_queue
| switch_ideal_normal: forall q1 q2 pin pout,
    switch_normal_packet_relation pin pout ->
    (counter + qlength q1 + 1) mod 1024 <> 0 ->
    switch_ideal_property counter q1 q2 ->
    switch_ideal_property counter (enque pin q1) (enque pout q2)
| switch_ideal_special: forall q1 q2 pin pout1 pout2,
    switch_normal_packet_relation pin pout1 ->
    switch_special_packet_relation pin pout2 ->
    (counter + qlength q1 + 1) mod 1024 = 0 ->
    switch_ideal_property counter q1 q2 ->
    switch_ideal_property counter (enque pin q1) (enque pout1 (enque pout2 q2)).

Lemma ideal_property_ingress_egress_switch: forall qin qmid qout counter,
    ingress_ideal_property counter qin qmid ->
    egress_ideal_property qmid qout ->
    switch_ideal_property counter qin qout.
Proof.
  intros. revert dependent qout. induction H; intros.
  - inv H0. constructor. destruct q1; simpl in H; discriminate.
  - inv H2. 1: destruct q2; simpl in H4; discriminate.
    apply enque_eq_inv in H3. destruct H3. subst. constructor; auto.
    eapply normal_ingress_egress_switch; eauto.
  - inv H3. 1: remember (enque pout2 q2) as q; destruct q; simpl in H5; discriminate.
    apply enque_eq_inv in H4. destruct H4. subst. inv H6.
    1: destruct q2; simpl in H4; discriminate. apply enque_eq_inv in H3. destruct H3.
    subst. apply switch_ideal_special; auto.
    + eapply normal_ingress_egress_switch; eauto.
    + eapply special_ingress_egress_switch; eauto.
Qed.

Lemma switch_ideal_property_queue_property1: forall counter qin qout,
    switch_ideal_property counter qin qout ->
    switch_queue_property1 qin qout.
Proof.
  intros. induction H; repeat intro.
  - simpl in H. contradiction.
  - rename IHswitch_ideal_property into IH.
    rewrite enque_eq in *. rewrite in_app_iff in H2. destruct H2.
    + specialize (IH pin0 H2). destruct IH as [pout' [? ?]]. exists pout'. split; auto.
      rewrite in_app_iff. left; assumption.
    + simpl in H2. destruct H2; [|contradiction]. subst pin0. exists pout. split; auto.
      rewrite in_app_iff. right. left. reflexivity.
  - rename IHswitch_ideal_property into IH.
    rewrite !enque_eq in *. rewrite in_app_iff in H3. destruct H3.
    + specialize (IH pin0 H3). destruct IH as [pout' [? ?]]. exists pout'. split; auto.
      rewrite in_app_iff. left. rewrite in_app_iff. left. assumption.
    + simpl in H3. destruct H3; [|contradiction]. subst pin0. exists pout1. split; auto.
      rewrite in_app_iff. right. left. reflexivity.
Qed.

Lemma switch_ideal_property_form: forall counter qin qout,
    switch_ideal_property counter qin qout -> front_nil_form qin.
Proof. intros. induction H; simpl; auto; apply front_nil_form_enque; assumption. Qed.

Lemma switch_ideal_property_split: forall counter qin qout,
    switch_ideal_property counter qin qout ->
    forall len, 0 <= len <= qlength qin ->
           exists q1 q2 q3 q4,
             qlength q1 = len /\
               qin = concat_queue q1 q2 /\
               qout = concat_queue q3 q4 /\
               switch_ideal_property counter q1 q3 /\
               switch_ideal_property (counter + len) q2 q4.
Proof.
  intros. pose proof (switch_ideal_property_form _ _ _ H).
  destruct (front_nil_form_split _ H1 _ H0) as [q1 [q2 [? [? [? ?]]]]].
  exists q1, q2. revert dependent q2. revert dependent q1. induction H; intros.
  - symmetry in H3. apply concat_queue_eq_empty in H3.
    destruct H3. subst. exists empty_queue, empty_queue. unfold concat_queue. simpl.
    do 3 (split; auto). split; constructor.
  - rename IHswitch_ideal_property into IH. destruct (Z_le_gt_dec len (qlength q1)).
    + specialize (IH ltac:(lia) (front_nil_form_enque_inv _ _ H1) _ H4 H5).
      destruct (empty_queue_dec q3).
      1: subst; rewrite concat_queue_empty in H6; subst q0; rewrite qlength_enque in l; lia.
      destruct (enque_eq_concat_form _ _ _ _ H6 n H7) as [q4 [? [? ?]]].
      specialize (IH _ H8 H9). destruct IH as (q5 & q6 & ? & ? & ? & ? & ?).
      exists q5, (enque pout q6). subst. rewrite !enque_concat_queue.
      do 4 (split; auto). apply switch_ideal_normal; auto.
      rewrite qlength_concat, Z.add_assoc in H2. assumption.
    + rewrite qlength_enque in H0. assert (len = qlength q1 + 1) by lia. clear g H0 IH.
      pose proof (@eq_refl _ (qlength (enque pin q1))). rewrite H6 in H0 at 1.
      rewrite qlength_concat, qlength_enque in H0. assert (qlength q3 = 0) by lia.
      rewrite qlength_0_iff in H9. subst q3. rewrite concat_queue_empty in *.
      exists (enque pout q2), empty_queue. rewrite concat_queue_empty. subst q0.
      do 4 (split; auto).
      * econstructor; eauto.
      * constructor.
  - rename IHswitch_ideal_property into IH. destruct (Z_le_gt_dec len (qlength q1)).
    + specialize (IH ltac:(lia) (front_nil_form_enque_inv _ _ H1) _ H5 H6).
      destruct (empty_queue_dec q3).
      1: subst; rewrite concat_queue_empty in H7; subst q0; rewrite qlength_enque in l; lia.
      destruct (enque_eq_concat_form _ _ _ _ H7 n H8) as [q4 [? [? ?]]].
      specialize (IH _ H9 H10). destruct IH as (q5 & q6 & ? & ? & ? & ? & ?).
      exists q5, (enque pout1 (enque pout2 q6)). subst. rewrite !enque_concat_queue.
      do 4 (split; auto). apply switch_ideal_special; auto.
      rewrite qlength_concat, Z.add_assoc in H3. assumption.
    + rewrite qlength_enque in H0. assert (len = qlength q1 + 1) by lia. clear g H0 IH.
      pose proof (@eq_refl _ (qlength (enque pin q1))). rewrite H7 in H0 at 1.
      rewrite qlength_concat, qlength_enque in H0. assert (qlength q3 = 0) by lia.
      rewrite qlength_0_iff in H10. subst q3. rewrite concat_queue_empty in *.
      exists (enque pout1 (enque pout2 q2)), empty_queue. rewrite concat_queue_empty. subst q0.
      do 4 (split; auto).
      * apply switch_ideal_special; auto.
      * constructor.
Qed.

Lemma switch_ideal_property_queue_property2: forall counter qin qout,
    switch_ideal_property counter qin qout ->
    switch_queue_property2 qin qout counter.
Proof.
  repeat intro. apply switch_ideal_property_split with (len := i + 1) in H. 2: lia.
  destruct H as [q1 [q2 [q3 [q4 [? [? [? [? _]]]]]]]].
  assert (Znth i (list_rep q1) = pin). {
    subst qin. rewrite concat_queue_eq in H1. rewrite qlength_eq in H. list_solve. }
  cut (exists pout : packet, In pout (list_rep q3) /\
                          switch_special_packet_relation pin pout). {
    intros. destruct H7 as (pout & ? & ?).
    exists pout. split; auto. subst qout. rewrite concat_queue_eq, in_app_iff. left; assumption. }
  destruct H0. clear dependent qin. clear dependent qout. clear q2 q4.
  revert dependent i. revert pin. inversion H5; subst; clear H5; intros.
  - simpl in H. lia.
  - rewrite qlength_enque in H2. assert (qlength q0 = i) by lia. rewrite H5 in *.
    rewrite H4 in H0. contradiction.
  - rewrite enque_eq in H6. rewrite qlength_enque in H3. rewrite qlength_eq in H3.
    rewrite Znth_app1 in H6 by lia. subst pin0. rewrite !enque_eq. exists pout2. split; auto.
    rewrite !in_app_iff. left. right. simpl. left. reflexivity.
Qed.

Opaque encode_out_md.

Lemma process_ingress_packets_ideal: forall inst1 inst2 q1 q2 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    ingress_ideal_property counter q1 q2.
Proof.
  intros. revert dependent counter. induction H0; intros. 1: constructor.
  rename IHprocess_ingress_packets into IH. specialize (IH _ H1).
  pose proof (process_ingress_packets_counter _ _ _ _ _ H1 H0). clear H1 H0.
  eapply process_packet_ingress_tm in H; eauto. destruct H.
  destruct ((counter + qlength ps + 1) mod 1024 =? 0) eqn: HS.
  - unfold concat_queue. rewrite H0. simpl. unfold flip.
    apply ingress_ideal_special; auto; clear -H HS.
    + destruct H as (sample & ether & ipv4 & result & payload & meta & ? & ? & ? & ?).
      rewrite HS in *. simpl in H1. exists 1, sample, ether, ipv4, result, payload, meta.
      do 3 (split; auto). format_match_solve. assumption.
    + destruct H as (sample & ether & ipv4 & result & payload & meta & ? & ? & ? & ?).
      rewrite HS in *. simpl in H1. exists sample, ether, ipv4, result, payload, meta.
      do 3 (split; auto). format_match_solve.
      assert (contains_sample 1 = true) by reflexivity.
      rewrite H3 in H1. eapply format_list_equiv_match; eauto.
      apply list_equiv_cons; [apply format_equiv_refl|].
      apply list_equiv_cons; [apply format_equiv_true|].
      apply format_list_equiv_refl.
    + rewrite Z.eqb_eq in HS. assumption.
  - unfold concat_queue. rewrite H0. simpl. unfold flip.
    apply ingress_ideal_normal; auto; clear -H HS.
    + destruct H as (sample & ether & ipv4 & result & payload & meta & ? & ? & ? & ?).
      rewrite HS in *. simpl in H1. exists 0, sample, ether, ipv4, result, payload, meta.
      do 3 (split; auto). format_match_solve. assumption.
    + rewrite Z.eqb_neq in HS. assumption.
Qed.

Lemma process_egress_packets_ideal: forall est1 q1 est2 q2,
  process_egress_packets
    (egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
       egress_deprsr_cond) est1 q1 est2 q2 -> egress_ideal_property q1 q2.
Proof.
  intros. induction H; constructor; auto. apply process_packet_egress in H0. assumption.
Qed.

Lemma switch_packets_ideal_property: forall inst1 inst2 est1 est2 q1 q2 q3 counter,
    ingress_counter inst1 counter ->
    process_ingress_packets
      (ingress_pipeline inprsr_block ingress_block indeprsr_block parser_ingress_cond
         ingress_deprsr_cond ingress_tm_cond) tofino_tm inst1 q1 inst2 q2 ->
    process_egress_packets
      (egress_pipeline eprsr_block egress_block edeprsr_block parser_egress_cond
         egress_deprsr_cond) est1 q2 est2 q3 ->
    switch_ideal_property counter q1 q3.
Proof.
  intros. eapply process_ingress_packets_ideal in H0; eauto.
  apply process_egress_packets_ideal in H1.
  eapply ideal_property_ingress_egress_switch; eauto.
Qed.

Transparent encode ig_intr_tm_md ipv4_repr_val ethernet_repr_val bridge_repr_val sample_repr_val.
