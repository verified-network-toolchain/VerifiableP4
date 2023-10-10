Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
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
Require Import ProD3.core.ProgNotations.
Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition extern_contains (es: extern_state) (p: path) (counter: Z) :=
  PathMap.get (p ++ ["reg_count"]) es =
      Some (ObjRegister [Z_to_val counter]) /\ 0 <= counter.

Inductive inprsr_block: programmable_block_sem :=
| parser_block_intro:
  forall inst_path m m' es es' fd (pin pin': packet_in) ver port stamp ether ipv4 result
    hdr ig_md ig_intr_md signal counter,
    extern_contains es ["pipe"; "ingress"] counter ->
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
    PathMap.get ["hdr"] m =
      Some (common.hdr hdr_init) ->
    PathMap.get ["packet_in"] es = Some (ObjPin pin) ->
    programmable_block ge inst_path "ingress_parser" fd ->
    extern_contains es' ["pipe"; "ingress"] counter ->
    exec_func ge read_ndetbit inst_path (m, es) fd nil [] (m', es')
      [hdr; ig_md; ig_intr_md] signal ->
    inprsr_block es [] es' [hdr; ig_md; ig_intr_md] signal.

Inductive ingress_block: programmable_block_sem :=
| ingress_block_intro:
  forall inst_path m m' es es' fd hdr1 hdr2 ig_md1 ig_md2 ig_intr_md
    ig_intr_dprsr_md2 ig_intr_tm_md1 ig_intr_tm_md2 signal,
    programmable_block ge inst_path "ingress" fd ->
    let ig_intr_prsr_md :=
      force ValBaseNull
        (uninit_sval_of_typ None ingress_intrinsic_metadata_from_parser_t) in
    let ig_intr_dprsr_md1 :=
      force ValBaseNull
        (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t) in
    exec_func ge read_ndetbit inst_path (m, es) fd nil
      [hdr1; ig_md1; ig_intr_md; ig_intr_prsr_md;
       ig_intr_dprsr_md1; ig_intr_tm_md1] (m', es')
      [hdr2; ig_md2; ig_intr_dprsr_md2; ig_intr_tm_md2] signal ->
    ingress_block es
      [hdr1; ig_md1; ig_intr_md; ig_intr_prsr_md; ig_intr_dprsr_md1; ig_intr_tm_md1]
      es' [hdr2; ig_md2; ig_intr_dprsr_md2; ig_intr_tm_md2] signal.

Inductive indeprsr_block: programmable_block_sem :=
| indeprsr_block_intro:
  forall inst_path m m' es es' fd hdr1 hdr2 ig_md ig_intr_dprsr_md signal,
    PathMap.get ["packet_out"] es = Some (ObjPout []) ->
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

Lemma get_packet: forall v1 v2 (es: extern_state),
    PathMap.get ["packet_in"]
      (PathMap.set ["packet_out"] v1 (PathMap.set ["packet_in"] v2 es)) = Some v2.
Proof.
  intros. rewrite PathMap.get_set_diff; [|intro HS; inversion HS].
  rewrite PathMap.get_set_same. reflexivity.
Qed.

Lemma hdr_init_type:
  ⊢ᵥ common.hdr (sample_valid_bridge hdr_init) \: header_sample_t.
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
    + apply hdr_init_type.
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

Opaque eval_val_to_sval ipv4_repr_val ethernet_repr_val.

Lemma ethernet_extract_result_valid_only:
  forall (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val),
    (if is_tcp ipv4
     then ⊫ᵥ result \: tcp_h
     else if is_udp ipv4 then ⊫ᵥ result \: udp_h else result = ValBaseNull) ->
  exists h, ethernet_extract_result
         (common.hdr (sample_valid_bridge hdr_init)) ether ipv4 result =
         val_to_sval_valid_only h.
Proof.
  intros. unfold ethernet_extract_result, protocol_extract_result.
  unfold sample_valid_bridge, hdr_init.
  simpl. destruct (is_tcp ipv4).
  - exists (ValBaseStruct
         [("bridge", ValBaseHeader [("contains_sample", P4BitV 8 0)] true);
          ("sample",
            ValBaseHeader
              [("dmac", P4BitV 48 0); ("smac", P4BitV 48 0);
               ("etype", P4BitV 16 0); ("srcip", P4BitV 32 0);
               ("dstip", P4BitV 32 0); ("num_pkts", P4BitV 32 0)]
              false);
          ("ethernet", ethernet_repr_val ether);
          ("ipv4", ipv4_repr_val ipv4);
          ("tcp", result);
          ("udp",
            ValBaseHeader
              [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0);
               ("hdr_length", P4BitV 16 0); ("checksum", P4BitV 16 0)]
              false)]). simpl. erewrite (ext_val_typ_to_sval_eq result); eauto.
  - destruct (is_udp ipv4).
    + exists (ValBaseStruct
         [("bridge", ValBaseHeader [("contains_sample", P4BitV 8 0)] true);
          ("sample",
            ValBaseHeader
              [("dmac", P4BitV 48 0); ("smac", P4BitV 48 0);
               ("etype", P4BitV 16 0); ("srcip", P4BitV 32 0);
               ("dstip", P4BitV 32 0); ("num_pkts", P4BitV 32 0)]
              false);
          ("ethernet", ethernet_repr_val ether);
          ("ipv4", ipv4_repr_val ipv4);
          ("tcp", ValBaseHeader
                    [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0);
                     ("seq_no", P4BitV 32 0); ("ack_no", P4BitV 32 0);
                     ("data_offset", P4BitV 4 0); ("res", P4BitV 4 0);
                     ("flags", P4BitV 8 0); ("window", P4BitV 16 0);
                     ("checksum", P4BitV 16 0); ("urgent_ptr", P4BitV 16 0)]
                    false);
          ("udp", result)]). simpl. erewrite (ext_val_typ_to_sval_eq result); eauto.
    + exists (ValBaseStruct
         [("bridge", ValBaseHeader [("contains_sample", P4BitV 8 0)] true);
          ("sample",
            ValBaseHeader
              [("dmac", P4BitV 48 0); ("smac", P4BitV 48 0);
               ("etype", P4BitV 16 0); ("srcip", P4BitV 32 0);
               ("dstip", P4BitV 32 0); ("num_pkts", P4BitV 32 0)]
              false);
          ("ethernet", ethernet_repr_val ether);
          ("ipv4", ipv4_repr_val ipv4);
          ("tcp", ValBaseHeader
                    [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0);
                     ("seq_no", P4BitV 32 0); ("ack_no", P4BitV 32 0);
                     ("data_offset", P4BitV 4 0); ("res", P4BitV 4 0);
                     ("flags", P4BitV 8 0); ("window", P4BitV 16 0);
                     ("checksum", P4BitV 16 0); ("urgent_ptr", P4BitV 16 0)]
                    false);
          ("udp",
            ValBaseHeader
              [("src_port", P4BitV 16 0); ("dst_port", P4BitV 16 0);
               ("hdr_length", P4BitV 16 0); ("checksum", P4BitV 16 0)]
              false)]). reflexivity.
Qed.

Transparent eval_val_to_sval ipv4_repr_val ethernet_repr_val.

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

Lemma process_packet_ingress:
  forall es es' pin pout for_tm,
    ingress_pipeline
      inprsr_block ingress_block indeprsr_block parser_ingress_cond
      ingress_deprsr_cond es pin es' pout for_tm -> False.
Proof.
  intros. inversion H. subst. inv H1. rewrite get_packet in H16.
  inversion H16. subst pin0; clear H16. inv H18. inv H0. inv H1. inv H8.
  eapply (proj1 ingress_parser_body) in H22; eauto.
  2: { hnf. split. 1: constructor. hnf. split.
       - hnf. simpl. rewrite H15. split; auto. apply sval_refine_refl.
       - hnf. simpl. rewrite get_packet. intuition. }
  destruct H22. hnf in H0. inv H0. inv H19. inv H21. clear H22.
  destruct H1 as [_ [_ [H1 _]]]. hnf in H1. rewrite H1 in H2.
  inv H2. inv H4. inv H3. inv H25. inv H0. inv H2. inv H3.
  destruct (ethernet_extract_result_hdr ether ipv4 result) as
    [ethernet [tcp [udp [ip4 ?H]]]]. rewrite H0 in H17.
  eapply (proj1 ingress_body counter ethernet
            tcp udp ip4 ig_intr_tm_md1) in H26; eauto.
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
  destruct H26. hnf in H2. inv H2. inv H22. inv H23. inv H24. clear H25.
  destruct H3 as [_ [_ [H3 _]]]. rewrite <- counter_iff in H3.
  inv H6. inv H5. inv H28. inv H2. inv H4. inv H5.
  assert (Hv: exists h, (if counter mod 1024 =? 0
                then update_hdr ethernet tcp udp ip4 (counter + 1)
                else hdr ethernet tcp udp ip4) = val_to_sval_valid_only h /\
                 ⊢ᵥ h \: header_sample_t). {
    unfold update_hdr. remember (hdr ethernet tcp udp ip4) as header.
    pose proof (ethernet_extract_result_typ ether _ _ H12). rewrite H0 in H2.
    pose proof (ethernet_extract_result_valid_only ether _ _ H12).
    rewrite H0 in H4. destruct H4 as [orig_h ?]. rewrite H4 in H2.
    assert (⊢ᵥ orig_h \: header_sample_t) by
      (apply to_sval_valid_only_typ_inv; assumption).
    destruct (counter mod 1024 =? 0). 2: (exists orig_h; split; assumption).
    admit.
  }
  eapply (proj1 ingress_deparser_body []) in H29; eauto.
  3: { split.
       - hnf. constructor.
         apply sval_refine_trans with
           (if counter mod 1024 =? 0
           then update_hdr ethernet tcp udp ip4 (counter + 1)
           else hdr ethernet tcp udp ip4). 2: assumption.
         admit. constructor. apply H9.
         constructor. apply H21. constructor.
       - split. 1: hnf; auto. hnf. split. 2: simpl; auto. simpl. assumption. }
Abort.
