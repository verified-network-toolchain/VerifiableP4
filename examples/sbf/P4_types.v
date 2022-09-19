Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}. *)

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation P4Type := (@P4Type Info).

Definition ingress_intrinsic_metadata_t : P4Type :=
  TypHeader
    [(!"resubmit_flag", TypBit 1); (!"_pad1", TypBit 1);
    (!"packet_version", TypBit 2); (!"_pad2", TypBit 3);
    (!"ingress_port", TypBit 9);
    (!"ingress_mac_tstamp", TypBit 48)].

Definition ingress_intrinsic_metadata_from_parser_t : P4Type :=
  TypStruct
    [(!"global_tstamp", TypBit 48); (!"global_ver", TypBit 32);
    (!"parser_err", TypBit 16)].

Definition ingress_intrinsic_metadata_for_deparser_t : P4Type :=
  TypStruct
    [(!"drop_ctl", TypBit 3); (!"digest_type", TypBit 3);
    (!"resubmit_type", TypBit 3); (!"mirror_type", TypBit 3)].

Definition ingress_intrinsic_metadata_for_tm_t : P4Type :=
  TypStruct
    [(!"ucast_egress_port", TypBit 9);
    (!"bypass_egress", TypBit 1);
    (!"deflect_on_drop", TypBit 1); (!"ingress_cos", TypBit 3);
    (!"qid", TypBit 5); (!"icos_for_copy_to_cpu", TypBit 3);
    (!"copy_to_cpu", TypBit 1); (!"packet_color", TypBit 2);
    (!"disable_ucast_cutthru", TypBit 1);
    (!"enable_mcast_cutthru", TypBit 1);
    (!"mcast_grp_a", TypBit 16); (!"mcast_grp_b", TypBit 16);
    (!"level1_mcast_hash", TypBit 13);
    (!"level2_mcast_hash", TypBit 13);
    (!"level1_exclusion_id", TypBit 16);
    (!"level2_exclusion_id", TypBit 9); 
    (!"rid", TypBit 16)].


Definition ethernet_h : P4Type :=
  TypHeader
    [(!"dst_addr", TypBit 48); (!"src_addr", TypBit 48);
    (!"ether_type", TypBit 16)].

Definition ipv4_h : P4Type :=
  TypHeader
    [(!"version", TypBit 4); (!"ihl", TypBit 4);
    (!"diffserv", TypBit 8); (!"total_len", TypBit 16);
    (!"identification", TypBit 16); (!"flags", TypBit 3);
    (!"frag_offset", TypBit 13); (!"ttl", TypBit 8);
    (!"protocol", TypBit 8); (!"hdr_checksum", TypBit 16);
    (!"src_addr", TypBit 32); (!"dst_addr", TypBit 32)].

Definition tcp_h : P4Type :=
  TypHeader
    [(!"src_port", TypBit 16); (!"dst_port", TypBit 16);
    (!"seq_no", TypBit 32); (!"ack_no", TypBit 32);
    (!"data_offset", TypBit 4); (!"res", TypBit 4);
    (!"flags", TypBit 8); (!"window", TypBit 16);
    (!"checksum", TypBit 16); (!"urgent_ptr", TypBit 16)].

Definition udp_h : P4Type :=
  TypHeader
    [(!"src_port", TypBit 16); (!"dst_port", TypBit 16);
    (!"hdr_length", TypBit 16); (!"checksum", TypBit 16)].

Definition header_t : P4Type :=
  TypStruct
  [(!"ethernet", TypHeader
     [(!"dst_addr", TypBit 48); (!"src_addr", TypBit 48);
     (!"ether_type", TypBit 16)]);
  (!"ipv4", TypHeader
    [(!"version", TypBit 4); (!"ihl", TypBit 4);
    (!"diffserv", TypBit 8); (!"total_len", TypBit 16);
    (!"identification", TypBit 16); (!"flags", TypBit 3);
    (!"frag_offset", TypBit 13); (!"ttl", TypBit 8);
    (!"protocol", TypBit 8); (!"hdr_checksum", TypBit 16);
    (!"src_addr", TypBit 32); (!"dst_addr", TypBit 32)]);
  (!"tcp", TypHeader
    [(!"src_port", TypBit 16); (!"dst_port", TypBit 16);
    (!"seq_no", TypBit 32); (!"ack_no", TypBit 32);
    (!"data_offset", TypBit 4); (!"res", TypBit 4);
    (!"flags", TypBit 8); (!"window", TypBit 16);
    (!"checksum", TypBit 16); (!"urgent_ptr", TypBit 16)]);
  (!"udp", TypHeader
    [(!"src_port", TypBit 16); (!"dst_port", TypBit 16);
    (!"hdr_length", TypBit 16); (!"checksum", TypBit 16)])].

Definition metadata_t : P4Type :=
  TypStruct
    [(!"bf2_key", TypBit 64);
    (!"bf2_api", TypBit 8);
    (!"solicited", TypBit 8)].
