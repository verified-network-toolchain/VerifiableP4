Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "ingress_parser"; "layer4_parser"].

Definition parser_parse_udp_fundef :=
  ltac:(get_fd ["EtherIPTCPUDPParser"; "parse_udp"] ge).

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
  ltac:(get_fd ["EtherIPTCPUDPParser"; "parse_tcp"] ge).

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
  ltac:(get_fd ["EtherIPTCPUDPParser"; "parse_ipv4"] ge).

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
  ltac:(get_fd ["EtherIPTCPUDPParser"; "parse_ethernet"] ge).

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
    remember (Build_header_t_rec
                (eval_val_to_sval (ethernet_repr_val ether))
                (header_t_ipv4 hsample)
                (header_t_tcp hsample)
                (header_t_udp hsample)) as new_hdr.
    assert (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
              (hdr hsample) = hdr new_hdr) by (rewrite Heqnew_hdr; reflexivity).
    rewrite H2.
    step_call parser_parse_ipv4_body; [entailer | apply H | apply H3].
  - apply is_sval_false_binary_op_eq in H0.
    rewrite Val_eqb_neq_iff in H0. exfalso. apply H0. assumption.
Qed.

Definition parser_start_fundef :=
  ltac:(get_fd ["EtherIPTCPUDPParser"; "start"] ge).

Definition parser_parse_start_spec: func_spec :=
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

Lemma parser_parse_start_body:
  func_sound ge parser_start_fundef nil parser_parse_start_spec.
Proof.
  start_function.
  step_call parser_parse_ethernet_body; [entailer | apply H | apply H0 | apply H1 |].
  step. entailer.
Qed.

Definition layer4_parser_fundef :=
  ltac:(get_fd ["EtherIPTCPUDPParser"; "apply"] ge).

Definition layer4_parser_spec: func_spec :=
  WITH,
    PATH p
    MOD None [["packet_in"]]
    WITH (pin pin': packet_in) ether ipv4 result
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
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [ethernet_extract_result (hdr hdr_init) ether ipv4 result] ValBaseNull
           (MEM []
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma layer4_parser_body:
  func_sound ge layer4_parser_fundef nil layer4_parser_spec.
Proof.
  start_function.
  step.
  replace (ValBaseStruct _) with (hdr hdr_init) by
    (unfold hdr; reflexivity).
  step_call parser_parse_start_body; [entailer | eauto..].
  step. entailer.
Qed.
