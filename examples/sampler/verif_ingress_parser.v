Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Export ProD3.examples.sampler.verif_tofino_ingress_parser.
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
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [assumption | reflexivity] |].
  simpl_format_list.
  apply format_match_nil in H2. subst p0. rewrite app_nil_r.
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
  simpl_format_list.
  step_call (@packet_in_extract_body Info);
    [ entailer | apply extract_encode; [assumption | reflexivity] |].
  do 2 simpl_format_list. rewrite app_nil_r.
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_parse_ipv4_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "parse_ipv4"] ge).

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
    [ entailer | apply extract_encode; [apply ext_val_typ_ipv4 | reflexivity] |].
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
  ltac:(get_fd ["SwitchIngressParser"; "parse_ethernet"] ge).

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
    [ entailer | apply extract_encode; [apply ext_val_typ_ethernet | reflexivity]|].
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
    rewrite H2.
    step_call parser_parse_ipv4_body; [entailer | apply H | apply H3].
  - apply is_sval_false_binary_op_eq in H0.
    rewrite Val_eqb_neq_iff in H0. exfalso. apply H0. assumption.
Qed.

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition sample_valid_bridge (hsample: header_sample_rec): header_sample_rec :=
  Build_header_sample_rec
    (update "contains_sample" (P4Bit 8 0)
               (EvalBuiltin.setValid (header_sample_bridge hsample)))
    (header_sample_sample hsample)
    (header_sample_ethernet hsample)
    (header_sample_ipv4 hsample)
    (header_sample_tcp hsample)
    (header_sample_udp hsample).

Definition parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_md"]]) [["packet_in"]]
    WITH (pin pin': packet_in) ver port stamp ether ipv4 hsample result
         (_: ⊫ᵥ iimt_repr_val 0 ver port stamp \: ingress_intrinsic_metadata_t)
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒;
                    ⟨64⟩;
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
           (MEM [(["hdr"], ethernet_extract_result
                             (hdr (sample_valid_bridge hsample))
                             ether ipv4 result);
                 (["ig_intr_md"], (iimt_repr_sval 0 ver port stamp))]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_start_body:
  func_sound ge parser_start_fundef nil parser_start_spec.
Proof.
  start_function.
  change [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒;
          ⟨ 64 ⟩; ⦑ encode (ethernet_repr_val ether) ⦒;
          ⦑ encode (ipv4_repr_val ipv4) ⦒;
          ⦃ is_tcp ipv4 ? ⦑ encode result ⦒
          | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
          ⦑ pin' ⦒] with
    ([⦑ encode (iimt_repr_val 0 ver port stamp) ⦒; ⟨ 64 ⟩] ++
       [⦑ encode (ethernet_repr_val ether) ⦒;
        ⦑ encode (ipv4_repr_val ipv4) ⦒;
        ⦃ is_tcp ipv4 ? ⦑ encode result ⦒
        | ⦃ is_udp ipv4 ? ⦑ encode result ⦒ | ε ⦄ ⦄;
        ⦑ pin' ⦒]) in H1. rewrite format_match_app_iff' in H1.
  destruct H1 as [p1 [p2 [? [? ?]]]].
  step_call tofino_parser_body; [ entailer | apply H | apply H3 | ].
  step. simpl eval_write_var.
  step.
  change (ValBaseStruct _) with (hdr (sample_valid_bridge hsample)).
  step_call parser_parse_ethernet_body; [entailer | eauto.. |].
  step. entailer.
Qed.

Definition parser_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "apply"] ge).

Definition parser_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["ig_md"]; ["ig_intr_md"]]) [["packet_in"]]
    WITH (pin pin': packet_in) ver port stamp ether ipv4 result
         (_: ⊫ᵥ iimt_repr_val 0 ver port stamp \: ingress_intrinsic_metadata_t)
         (_: if is_tcp ipv4 then ⊫ᵥ result \: tcp_h
             else if is_udp ipv4 then ⊫ᵥ result \: udp_h
                  else result = ValBaseNull)
         (_: pin ⫢ [⦑ encode (iimt_repr_val 0 ver port stamp) ⦒;
                    ⟨64⟩;
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
        (ARG_RET [(ethernet_extract_result
                     (hdr (sample_valid_bridge hdr_init))
                     ether ipv4 result);
                  (ValBaseStruct [("num_pkts", P4Bit_ 32)]);
                  (iimt_repr_sval 0 ver port stamp)] ValBaseNull
           (MEM []
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma ingress_parser_body:
  func_sound ge parser_fundef nil parser_spec.
Proof.
  start_function.
  step.
  replace (ValBaseStruct _) with (hdr hdr_init) by
    (unfold hdr; reflexivity).
  step.
  step.
  step_call parser_start_body; [entailer | eauto..].
  step. entailer.
Qed.
