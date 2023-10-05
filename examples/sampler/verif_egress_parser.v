Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.verif_tofino_egress_parser.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "egress_parser"].

Definition parser_parse_udp_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "parse_udp"] ge).

Definition parser_parse_udp_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hdr udp pin'
         (_: ⊫ᵥ udp \: udp_h)
         (_: pin ⫢ [⦑ encode udp ⦒; ⦑ pin' ⦒]),
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
  do 3 simpl_format_list. rewrite app_nil_r.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [assumption | reflexivity] |].
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_parse_tcp_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "parse_tcp"] ge).

Definition parser_parse_tcp_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hdr tcp pin'
         (_: ⊫ᵥ tcp \: tcp_h)
         (_: pin ⫢ [⦑ encode tcp ⦒; ⦑ pin' ⦒]),
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
  do 3 simpl_format_list. rewrite app_nil_r.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [assumption | reflexivity] |].
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_parse_ipv4_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "parse_ipv4"] ge).

Definition parser_parse_ipv4_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin: packet_in) hsample ipv4 result pin'
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [ ⦑ encode (ipv4_repr_val ipv4) ⦒;
                     ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                       ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] ),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr hsample))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], protocol_extract_result ipv4 result
                             (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
                                (hdr hsample)))]
           (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_parse_ipv4_body:
  func_sound ge parser_parse_ipv4_fundef nil parser_parse_ipv4_spec.
Proof.
  start_function.
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [ apply ext_val_typ_ipv4 | reflexivity] |].
  step_if; change (ValBaseBit _) with (P4BitV 8 IP_PROTOCOLS_TCP) in H0;
    rewrite abs_ipv4_hdr_eq_eq in H0.
  - apply is_sval_true_binary_op_eq in H0.
    change (Val_eqb _ _) with (is_tcp ipv4) in H0. unfold protocol_extract_result.
    rewrite H0 in *. simpl_format_list.
    step_call parser_parse_tcp_body; [ entailer | assumption | apply H2 ].
  - apply is_sval_false_binary_op_eq in H0.
    change (Val_eqb _ _) with (is_tcp ipv4) in H0.
    unfold protocol_extract_result. rewrite H0 in *. simpl_format_list.
    step_if; change (ValBaseBit _) with (P4BitV 8 IP_PROTOCOLS_UDP) in H1;
      rewrite abs_ipv4_hdr_eq_eq in H1.
    + apply is_sval_true_binary_op_eq in H1.
      change (Val_eqb _ _) with (is_udp ipv4) in H1.
      rewrite H1 in *. simpl_format_list.
      step_call parser_parse_udp_body; [ entailer | assumption | apply H2 ].
    + apply is_sval_false_binary_op_eq in H1.
      change (Val_eqb _ _) with (is_udp ipv4) in H1.
      rewrite H1 in *. do 4 simpl_format_list. rewrite app_nil_r.
      step_call (@parser_accept_body Info). entailer.
Qed.

Definition parser_parse_ethernet_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "parse_ethernet"] ge).

Definition parser_parse_ethernet_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin pin': packet_in) ether ipv4 hsample result
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [ ⦑ encode (ethernet_repr_val ether) ⦒;
                     ⦑ encode (ipv4_repr_val ipv4) ⦒;
                     ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                       ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] )
         (_: P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr hsample))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], ethernet_extract_result (hdr hsample) ether ipv4 result)]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_parse_ethernet_body:
  func_sound ge parser_parse_ethernet_fundef nil parser_parse_ethernet_spec.
Proof.
  start_function.
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [entailer | apply extract_encode; [apply ext_val_typ_ethernet | reflexivity] |].
  step_if; change (ValBaseBit _) with (P4BitV 16 ETHERTYPE_IPV4) in H0;
    rewrite abs_ether_eq_eq in H0.
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
    rewrite H2. step_call parser_parse_ipv4_body; [entailer | apply H | apply H3].
  - apply is_sval_false_binary_op_eq in H0.
    rewrite Val_eqb_neq_iff in H0. exfalso. apply H0. assumption.
Qed.

Definition parser_parse_sample_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "parse_sample"] ge).

Definition sample_extract_result
  (header: Sval) (sample: Val) (ether: ethernet_rec)
  (ipv4: ipv4_rec) (result: Val): Sval :=
  ethernet_extract_result
    (update "sample" (eval_val_to_sval sample) header) ether ipv4 result.

Definition parser_parse_sample_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]]) [["packet_in"]]
    WITH (pin pin': packet_in) sample ether ipv4 hsample result
         (_: ⊫ᵥ sample \: sample_t)
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [ ⦑ encode sample ⦒;
                     ⦑ encode (ethernet_repr_val ether) ⦒;
                     ⦑ encode (ipv4_repr_val ipv4) ⦒;
                     ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                       ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] )
         (_: P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], (hdr hsample))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], sample_extract_result (hdr hsample) sample ether
                             ipv4 result)]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_parse_sample_body:
  func_sound ge parser_parse_sample_fundef nil parser_parse_sample_spec.
Proof.
  start_function.
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [assumption | reflexivity] |].
  unfold sample_extract_result.
  remember (Build_header_sample_rec
              (header_sample_bridge hsample)
              (eval_val_to_sval sample)
              (header_sample_ethernet hsample)
              (header_sample_ipv4 hsample)
              (header_sample_tcp hsample)
              (header_sample_udp hsample)) as new_hdr.
  replace (update "sample" (eval_val_to_sval sample) (hdr hsample)) with
    (hdr new_hdr) by (rewrite Heqnew_hdr; reflexivity).
  step_call parser_parse_ethernet_body; [entailer | eauto..].
  step. entailer.
Qed.

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "start"] ge).

Definition bridge_repr_val (has_sample: Z): Val :=
  ValBaseHeader [("contains_sample", P4BitV 8 has_sample)] true.

Lemma ext_val_typ_bridge: forall has_sample, ⊫ᵥ bridge_repr_val has_sample \: bridge_t.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.

Definition contains_sample (has_sample: Z): bool :=
  Val_eqb (P4BitV 8 has_sample) (P4BitV 8 1).

Definition start_extract_result (has_sample: Z) (hsample : header_sample_rec)
  (sample : Val) (ether : ethernet_rec) (ipv4 : ipv4_rec) (result : Val) :=
  let bridge := eval_val_to_sval (bridge_repr_val has_sample) in
  let header := update "bridge" bridge (hdr hsample) in
  if contains_sample has_sample
  then sample_extract_result header sample ether ipv4 result
  else ethernet_extract_result header ether ipv4 result.

Definition parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["eg_intr_md"]]) [["packet_in"]]
    WITH (pin pin': packet_in) eg_intr_md has_sample sample
         hsample ether ipv4 result
         (_: ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t)
         (_: if contains_sample has_sample then ⊫ᵥ sample \: sample_t
             else sample = ValBaseNull)
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [⦑ encode eg_intr_md ⦒;
                    ⦑ encode (bridge_repr_val has_sample) ⦒;
                    ⦃ contains_sample has_sample ? ⦑ encode sample ⦒ | ε ⦄;
                    ⦑ encode (ethernet_repr_val ether) ⦒;
                     ⦑ encode (ipv4_repr_val ipv4) ⦒;
                     ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                       ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] )
         (_: P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], hdr hsample)]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["eg_intr_md"], eval_val_to_sval eg_intr_md);
                 (["hdr"], start_extract_result has_sample hsample
                             sample ether ipv4 result)]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma abs_eq_eq: forall v1 v2,
    abs_eq (eval_val_to_sval v1) (eval_val_to_sval v2) =
      eval_val_to_sval (force ValBaseNull (Ops.eval_binary_op Eq v1 v2)).
Proof.
  intros. unfold abs_eq, build_abs_binary_op. simpl.
  rewrite !eval_sval_to_val_eq. reflexivity.
Qed.

Lemma parser_start_body:
  func_sound ge parser_start_fundef nil parser_start_spec.
Proof.
  start_function.
  remember [⦑ encode (bridge_repr_val has_sample) ⦒;
            ⦃ contains_sample has_sample ? ⦑ encode sample ⦒ | ε ⦄;
            ⦑ encode (ethernet_repr_val ether) ⦒; ⦑ encode (ipv4_repr_val ipv4) ⦒;
            ⦃ is_tcp ipv4 ? ⦑ encode result ⦒
            | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
            ⦑ pin' ⦒].
  change (⦑ encode eg_intr_md ⦒ :: l) with ([⦑ encode eg_intr_md ⦒] ++ l) in H2.
  rewrite format_match_app_iff' in H2. destruct H2 as [p1 [p2 [? [? ?]]]].
  step_call tofino_parser_body; [ entailer | eauto | apply H4 | ]. subst l.
  clear dependent pin. clear p1.
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [entailer | apply extract_encode; [ apply ext_val_typ_bridge | reflexivity] | ].
  remember (Build_header_sample_rec
              (eval_val_to_sval (bridge_repr_val has_sample))
              (header_sample_sample hsample)
              (header_sample_ethernet hsample)
              (header_sample_ipv4 hsample)
              (header_sample_tcp hsample)
              (header_sample_udp hsample)) as new_hdr.
  assert (Hu: update "bridge" (eval_val_to_sval (bridge_repr_val has_sample))
                (hdr hsample) = hdr new_hdr) by (subst new_hdr; reflexivity).
  Opaque P4BitV.
  rewrite Hu; step_if; rewrite Heqnew_hdr in H2; simpl in H2;
    change (P4Bit 8 1) with (eval_val_to_sval (P4BitV 8 1)) in H2;
    rewrite abs_eq_eq in H2. Transparent P4BitV.
  - apply is_sval_true_binary_op_eq in H2.
    change (Val_eqb _ _) with (contains_sample has_sample) in H2.
    unfold start_extract_result. rewrite H2 in *. rewrite Hu. simpl_format_list.
    step_call parser_parse_sample_body; [entailer | eauto..].
  - apply is_sval_false_binary_op_eq in H2.
    change (Val_eqb _ _) with (contains_sample has_sample) in H2.
    unfold start_extract_result. rewrite H2 in *. rewrite Hu.
    do 2 simpl_format_list.
    step_call parser_parse_ethernet_body; [entailer | eauto..].
Qed.

Definition parser_fundef :=
  ltac:(get_fd ["SwitchEgressParser"; "apply"] ge).

Definition parser_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["eg_md"]; ["eg_intr_md"]]) [["packet_in"]]
    WITH (pin pin': packet_in) eg_intr_md has_sample sample ether ipv4 result
         (_: ⊫ᵥ eg_intr_md \: egress_intrinsic_metadata_t)
         (_: if contains_sample has_sample then ⊫ᵥ sample \: sample_t
             else sample = ValBaseNull)
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [⦑ encode eg_intr_md ⦒;
                    ⦑ encode (bridge_repr_val has_sample) ⦒;
                    ⦃ contains_sample has_sample ? ⦑ encode sample ⦒ | ε ⦄;
                    ⦑ encode (ethernet_repr_val ether) ⦒;
                     ⦑ encode (ipv4_repr_val ipv4) ⦒;
                     ⦃ is_tcp ipv4 ? ⦑ encode result ⦒ |
                       ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄; ⦑ pin' ⦒] )
         (_: P4BitV 16 (ethernet_ether_type ether) = P4BitV 16 ETHERTYPE_IPV4),
      PRE
        (ARG []
        (MEM [(["hdr"], hdr hdr_init)]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [start_extract_result has_sample hdr_init
                             sample ether ipv4 result;
                  ValBaseStruct [("num_pkts", P4Bit_ 32)];
                  eval_val_to_sval eg_intr_md] ValBaseNull
           (MEM []
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma egress_parser_body:
  func_sound ge parser_fundef nil parser_spec.
Proof.
  start_function.
  step.
  replace (ValBaseStruct _) with (hdr hdr_init) by (unfold hdr; reflexivity).
  step.
  step.
  step_call parser_start_body; [entailer | eauto..].
  step. entailer.
Qed.
