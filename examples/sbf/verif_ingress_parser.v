Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.verif_tofino_ingress_parser.
Require Import ProD3.examples.sbf.verif_etheriptcpudp_parser.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Definition p := ["pipe"; "ingress_parser"].

Definition parser_start_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "start"] ge).

Definition parser_start_spec: func_spec :=
  WITH,
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_md"]]) [["packet_in"]]
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
        (MEM [(["hdr"], (hdr hdr_init))]
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["hdr"], ethernet_extract_result
                             (hdr hdr_init)
                             ether ipv4 result);
                 (["ig_intr_md"], (iimt_repr_sval 0 ver port stamp))]
              (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin')]))).

Lemma parser_start_body:
  func_sound ge parser_start_fundef nil parser_start_spec.
Proof.
  start_function.
  cut_list_n_in H1 2%nat.
  rewrite format_match_app_iff_rear in H1.
  destruct H1 as [p1 [p2 [? [? ?]]]].
  step_call tofino_parser_body; [ entailer | apply H | apply H3 | ].
  step_call layer4_parser_body; [entailer | eauto.. |].
  step_call (@parser_accept_body Info). entailer.
  step. entailer.
Qed.

Definition parser_fundef :=
  ltac:(get_fd ["SwitchIngressParser"; "apply"] ge).

Definition parser_spec: func_spec :=
  WITH,
    PATH p
    MOD None [["packet_in"]]
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
        (MEM []
        (EXT [ExtPred.singleton ["packet_in"] (ObjPin pin)])))
      POST
        (ARG_RET [(ethernet_extract_result (hdr hdr_init) ether ipv4 result);
                  (ValBaseStruct [("bf2_key", P4Bit_ 64);
                                  ("bf2_api", P4Bit_ 8);
                                  ("solicited", P4Bit_ 8)]);
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
