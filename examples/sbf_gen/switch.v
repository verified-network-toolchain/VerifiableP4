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

(* A simplified switch model to demonstrate bloom filter application. *)

Section Switch.

(* Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}. *)

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation P4Type := (@P4Type Info).

Variable ge : genv.
Variable H : P4Type.
Variable M : P4Type.

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

Definition timestamp_t := Z.
Definition ipv4_header : Type := Z * Z.
Definition payload_t := list bool.

Definition ipv4_addr_w := 32%N.

Definition get_drop_ctl (v : Sval) : bool :=
  match v with
  | ValBaseBit [_ ; _; ob] => force false ob
  | _ => false
  end.

Inductive process_packet : extern_state -> (timestamp_t * ipv4_header * payload_t * Z) -> extern_state -> option (ipv4_header * payload_t) -> Prop :=
  | process_packet_intro : forall es timestamp ipv4 port payload es' ipv4'
            pipe_class_name pipe_inst_path pipe_targs class_name inst_path targs fd
            m' hdr' meta' ingress_intrinsic_metadata_for_deparser' ingress_intrinsic_metadata_for_tm',
      PathMap.get ["main"; "pipe0"] (ge_inst ge) = Some {|iclass:=pipe_class_name; ipath:=pipe_inst_path; itargs:=pipe_targs|} ->
      PathMap.get (pipe_inst_path ++ ["ingress"]) (ge_inst ge) = Some {|iclass:=class_name; ipath:=inst_path; itargs:=targs|} ->
      PathMap.get ([class_name; "apply"]) (ge_func ge) = Some fd ->
      let hdr := update "ipv4"
        (update "src_addr" (P4Bit ipv4_addr_w (fst ipv4))
          (update "dst_addr" (P4Bit ipv4_addr_w (snd ipv4))
            (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
        (force ValBaseNull (uninit_sval_of_typ None header_t)) in
      (* 0 <= data < Z.pow 2 16 -> *)
      let meta := force ValBaseNull (uninit_sval_of_typ None M) in
      let ingress_intrinsic_metadata :=
        update "ingress_port" (P4Bit 9 port) (
            update "ingress_mac_tstamp" (P4Bit 48 timestamp)
              (force ValBaseNull (uninit_sval_of_typ (Some true) ingress_intrinsic_metadata_t))) in
      let ingress_intrinsic_metadata_from_parser := force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_from_parser_t) in
      let ingress_intrinsic_metadata_for_deparser := force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t) in
      let ingress_intrinsic_metadata_for_tm := force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_tm_t) in
      (* 0 <= data' < Z.pow 2 16 -> *)
      exec_func ge read_ndetbit inst_path (PathMap.empty, es) fd nil
          [hdr; meta; ingress_intrinsic_metadata; ingress_intrinsic_metadata_from_parser; ingress_intrinsic_metadata_for_deparser; ingress_intrinsic_metadata_for_tm]
          (m', es')
          [hdr'; meta'; ingress_intrinsic_metadata_for_deparser'; ingress_intrinsic_metadata_for_tm']
          (SReturn ValBaseNull) ->
      (* Construct ipv4' from hdr'. *)
      0 <=  fst ipv4' < Z.pow 2 32 ->
      get "src_addr" (get "ipv4" hdr') = P4Bit ipv4_addr_w (fst ipv4') ->
      0 <=  snd ipv4' < Z.pow 2 32 ->
      get "dst_addr" (get "ipv4" hdr') = P4Bit ipv4_addr_w (snd ipv4') ->
      let drop_ctl := get_drop_ctl (get "drop_ctl" ingress_intrinsic_metadata_for_deparser') in
      process_packet es (timestamp, ipv4, payload, port) es' (if drop_ctl then None else Some (ipv4', payload)).

Inductive process_packets : extern_state -> list (timestamp_t * ipv4_header * payload_t * Z) -> extern_state -> list (option (ipv4_header * payload_t)) -> Prop :=
  | process_packets_nil : forall es,
      process_packets es [] es []
  | process_packets_cons : forall es1 p p' es2 ps ps' es3,
      process_packet es1 p es2 p' ->
      process_packets es2 ps es3 ps' ->
      process_packets es1 (p :: ps) es3 (p' :: ps').

End Switch.
