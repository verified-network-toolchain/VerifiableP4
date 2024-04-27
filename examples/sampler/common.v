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

Definition ig_intr_tm_md := Eval vm_compute in
    update "mcast_grp_a" (P4Bit 16 0)
      (update "mcast_grp_b" (P4Bit 16 0)
         (update "ucast_egress_port" (P4Bit 9 0)
            (force ValBaseNull
               (uninit_sval_of_typ None
                  Tofino.ingress_intrinsic_metadata_for_tm_t)))).

Record sample_rec := {
    sample_dmac: Z;
    sample_smac: Z;
    sample_etype: Z;
    sample_srcip: Z;
    sample_dstip: Z;
    sample_num_pkts: Z;
  }.

Definition sample_repr_val (smpl: sample_rec): Val :=
  ValBaseHeader
    [("dmac", P4BitV 48 (sample_dmac smpl));
     ("smac", P4BitV 48 (sample_smac smpl));
     ("etype", P4BitV 16 (sample_etype smpl));
     ("srcip", P4BitV 32 (sample_srcip smpl));
     ("dstip", P4BitV 32 (sample_dstip smpl));
     ("num_pkts", P4BitV 32 (sample_num_pkts smpl))] true.

Lemma ext_val_typ_sample: forall sample, ⊫ᵥ sample_repr_val sample \: sample_t.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.

Definition invalidate_field (h: Sval) (fld: ident): Sval :=
  (update fld (EvalBuiltin.setInvalid (get fld h)) h).

Definition invalidate_fields (h: Sval) (flds: list ident): Sval :=
  fold_left invalidate_field flds h.

Definition setInvalidv (v : Val) : Val :=
  match v with
  | ValBaseHeader fields _ => ValBaseHeader fields false
  | _ => v
  end.

Definition invalidate_fieldv (h: Val) (fld: ident): Val :=
  (updatev fld (setInvalidv (getv fld h)) h).

Definition invalidate_fieldsv (h: Val) (flds: list ident): Val :=
  fold_left invalidate_fieldv flds h.

Lemma invalidate_field_valid_only: forall {tags_t: Type} h fld fields,
    is_some (AList.get (clear_AList_tags fields) fld) ->
    ⊢ᵥ h \: @TypStruct tags_t fields ->
    sval_refine (val_to_sval_valid_only (invalidate_fieldv h fld))
      (invalidate_field (val_to_sval_valid_only h) fld).
Proof.
  intros. inv H0. simpl. rewrite <- P4String.key_unique_clear_AList_tags in H2.
  remember (P4String.clear_AList_tags fields) as flds. clear fields Heqflds.
  destruct (AList.get flds fld) eqn:?H. 2: discriminate. clear H.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H4 H0).
  destruct (AList.get vs fld) eqn:?H. 2: discriminate. clear H.
  rewrite AList_get_kv_map with (v := v) by assumption. simpl.
  apply AListUtil.AList_get_some_split in H1. destruct H1 as [k [l1 [l2 [? [? ?]]]]].
  hnf in H. subst k. subst vs. rewrite kv_map_app. simpl kv_map.
  rewrite !AListUtil.AList_set_app_cons_some; [|reflexivity| |reflexivity|assumption].
  2: { apply AListUtil.not_in_fst_get_none. intros.
       rewrite kv_map_fst. eapply AListUtil.get_none_not_in_fst; eauto. }
  simpl. constructor. rewrite kv_map_app. apply AListUtil.all_values_app_inv.
  - apply exec_val_refl_case2. rewrite Forall_forall. intros. destruct x.
    apply sval_refine_refl.
  - simpl. constructor.
    + simpl. split; auto. clear.
      induction v using custom_ValueBase_ind; simpl; try solve [constructor].
      * constructor. apply read_some.
      * constructor. apply Forall2_refl. intros. apply bit_refine_refl.
      * constructor. apply Forall2_refl. intros. apply bit_refine_refl.
      * constructor. apply Forall2_refl. intros. apply bit_refine_refl.
      * constructor. apply Forall2_refl. intros. apply sval_refine_refl.
      * constructor. apply Forall2_refl. intros. split; auto. apply sval_refine_refl.
      * destruct b; simpl; constructor; try apply bit_refine_refl.
        -- clear. induction vs; simpl; constructor; auto. destruct a. simpl. split; auto.
           apply sval_refine_liberal_valid_only.
        -- apply exec_val_refl_case2. rewrite Forall_forall. intros. destruct x.
           apply sval_refine_refl.
      * constructor. apply Forall2_refl. intros. split; auto. apply sval_refine_refl.
      * constructor. apply Forall2_refl. intros. apply sval_refine_refl.
      * constructor. apply sval_refine_refl.
    + apply exec_val_refl_case2. rewrite Forall_forall. intros. destruct x.
      apply sval_refine_refl.
Qed.

Lemma invalidate_field_typ: forall {tags_t: Type} h fld fields,
    is_some (AList.get (clear_AList_tags fields) fld) ->
    ⊢ᵥ h \: @TypStruct tags_t fields ->
    ⊢ᵥ invalidate_field h fld \: @TypStruct tags_t fields.
Proof.
  intros. inv H0. simpl. remember (P4String.clear_AList_tags fields) as flds.
  destruct (AList.get flds fld) eqn:?H. 2: discriminate. clear H.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H4 H0).
  destruct (AList.get vs fld) eqn:?H. 2: discriminate. clear H. simpl.
  constructor; auto. assert (⊢ᵥ v \: p) by (eapply all_values_get_some_rel; eauto).
  subst flds. eapply all_values_val_typ_set; eauto.
  induction H using custom_val_typ_ind; simpl; try constructor; try assumption.
Qed.

Lemma invalidate_fields_typ: forall {tags_t: Type} flds h fields,
    forallb (fun fld => is_some (AList.get (clear_AList_tags fields) fld)) flds ->
    ⊢ᵥ h \: @TypStruct tags_t fields ->
    ⊢ᵥ invalidate_fields h flds \: @TypStruct tags_t fields.
Proof.
  intros ? ?. induction flds; simpl; intros; auto.
  rewrite Reflect.andE in H. destruct H. apply IHflds; auto.
  eapply invalidate_field_typ; eauto.
Qed.

Lemma sval_refine_invalidate_field: forall {tags_t: Type} h1 h2 fld fields,
    is_some (AList.get (clear_AList_tags fields) fld) ->
    ⊢ᵥ h1 \: @TypStruct tags_t fields ->
    sval_refine h1 h2 ->
    sval_refine (invalidate_field h1 fld) (invalidate_field h2 fld).
Proof.
  intros. unfold invalidate_field. inv H0. inv H1. simpl.
  remember (P4String.clear_AList_tags fields) as flds.
  destruct (AList.get flds fld) eqn:?H. 2: discriminate. clear H.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H5 H0).
  destruct (AList.get vs fld) eqn:?H. 2: discriminate. clear H. simpl.
  pose proof (all_values_get_some_is_some _ _ _ _ _ H2 H1).
  destruct (AList.get kvs' fld) eqn:?H. 2: discriminate. clear H. simpl.
  constructor. erewrite !AList.get_some_set; eauto. simpl.
  eapply all_values_set_some_rel; [apply H2| eapply AList.get_some_set; eauto..|].
  assert (sval_refine v v0) by (eapply all_values_get_some_rel; eauto).
  induction H using custom_exec_val_ind; simpl; try constructor; try assumption. constructor.
Qed.

Lemma sval_refine_invalidate_fields: forall {tags_t: Type} flds h1 h2  fields,
    forallb (fun fld => is_some (AList.get (clear_AList_tags fields) fld)) flds ->
    ⊢ᵥ h1 \: @TypStruct tags_t fields ->
    sval_refine h1 h2 ->
    sval_refine (invalidate_fields h1 flds) (invalidate_fields h2 flds).
Proof.
  intros ? ?. induction flds; simpl; intros; auto.
  rewrite Reflect.andE in H. destruct H. eapply IHflds; eauto.
  - apply invalidate_field_typ; assumption.
  - eapply sval_refine_invalidate_field; eauto.
Qed.

Lemma invalidate_fields_valid_only: forall {tags_t: Type} flds h fields,
    forallb (fun fld => is_some (AList.get (clear_AList_tags fields) fld)) flds ->
    ⊢ᵥ h \: @TypStruct tags_t fields ->
    sval_refine (val_to_sval_valid_only (invalidate_fieldsv h flds))
      (invalidate_fields (val_to_sval_valid_only h) flds).
Proof.
  intros ? ?. induction flds; simpl; intros.
  - apply sval_refine_refl.
  - rewrite Reflect.andE in H. destruct H.
    pose proof (invalidate_field_valid_only _ _ _ H H0).
    remember (invalidate_fieldv h a) as mh.
    assert (⊢ᵥ mh \: TypStruct fields). {
      rewrite <- to_sval_valid_only_typ_iff in H0. eapply invalidate_field_typ in H0; eauto.
      apply val_sim_on_top, val_sim_sym in H2.
      rewrite <- to_sval_valid_only_typ_iff. erewrite val_sim_prsv_typ in H0; eauto. }
    specialize (IHflds _ _ H1 H3). eapply sval_refine_trans; eauto.
    eapply sval_refine_invalidate_fields; eauto.
    rewrite to_sval_valid_only_typ_iff. assumption.
Qed.

Definition encode_field (h: Val) (fld: ident): packet := encode (getv fld h).

Lemma map_encode_eq:
  forall (tags_t : Type) (fields : AList tags_t P4Type) (vs : AList.AList ident Val eq),
    AList.key_unique fields = true ->
    AList.all_values (@val_typ _ tags_t) vs (clear_AList_tags fields) ->
    concat (map (fun '(_, v) => encode v) vs) =
      flat_map (fun fld : ident => encode (force ValBaseNull (AList.get vs fld)))
        (map fst (clear_AList_tags fields)).
Proof.
  intros tags_t fields vs H1 H3. rewrite flat_map_concat_map, map_map. f_equal.
  rewrite <- key_unique_clear_AList_tags in H1. remember (clear_AList_tags fields) as flds.
  clear Heqflds. revert H1. induction H3; intros; try reflexivity.
  rewrite !map_cons. destruct x as [fx vx]. destruct y as [fld vy]. simpl in H |- *.
  destruct H. subst fx. rewrite AList.get_eq_cons by reflexivity. simpl. f_equal.
  simpl in H1. destruct (AList.get l' fld) eqn: ?. 1: discriminate.
  rewrite IHForall2 by assumption. rewrite map_ext_in_iff. intros.
  rewrite AList.get_neq_cons. 1: reflexivity. destruct a as [k v]. simpl in *. symmetry.
  intro. pose proof (AList.get_in_not_none _ _ _ _ H2 H). contradiction.
Qed.

Lemma encode_struct_encode_field: forall {tags_t: Type} {fields h},
    ⊢ᵥ h \: @TypStruct tags_t fields ->
    encode h = flat_map (encode_field h) (map fst (clear_AList_tags fields)).
Proof. intros. inv H. unfold encode_field. simpl. apply map_encode_eq; auto. Qed.

Definition header_is_valid (val: Val) : Prop :=
  match val with
  | ValBaseHeader _ false => False
  | ValBaseHeader fields true => True
  | _ => True
  end.

Lemma encode_header_encode_field: forall {tags_t: Type} {fields h},
    ⊢ᵥ h \: @TypHeader tags_t fields ->
    header_is_valid h ->
    encode h = flat_map (encode_field h) (map fst (clear_AList_tags fields)).
Proof.
  intros. inv H. simpl in H0. destruct b. 2: contradiction.
  unfold encode_field. simpl. apply map_encode_eq; auto.
Qed.

Lemma encode_field_updatev_eq: forall {tags_t: Type} fields f fv v,
    ⊢ᵥ v \: @TypStruct tags_t fields ->
    existsb (String.eqb f) (map fst (clear_AList_tags fields)) = true ->
    encode_field (updatev f fv v) f = encode fv.
Proof.
  intros. inv H. unfold encode_field. simpl.
  rewrite existsb_exists in H0. destruct H0 as [x []]. rewrite String.eqb_eq in H0.
  subst x. apply AList.in_fst_get_some in H. destruct H.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H4 H).
  destruct (AList.get vs f) eqn: ?. 2: discriminate.
  erewrite get_some_get_set_same; eauto.
Qed.

Lemma encode_field_updatev_neq: forall f1 f2 fv v,
    f1 <> f2 -> encode_field (updatev f1 fv v) f2 = encode_field v f2.
Proof.
  intros. unfold encode_field; destruct v; simpl; try reflexivity.
  all: rewrite get_set_diff; auto.
Qed.
