Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Poulet4.P4light.Architecture.V1ModelTarget.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.Members.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

(* A simplified switch model to demonstrate bloom filter application. *)

Section Switch.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Expression := (@Expression tags_t).
Notation P4Type := (@P4Type tags_t).
Notation extern_state := (@extern_state tags_t Expression).

Instance target : @Target tags_t Expression := V1Model.

Variable ge : genv.
Variable M : P4Type.

Definition standard_metadata_t : P4Type :=
  TypStruct
    [(!"ingress_port", TypBit 9); (!"egress_spec", TypBit 9); (!"egress_port", TypBit 9);
    (!"instance_type", TypBit 32); (!"packet_length", TypBit 32); (!"enq_timestamp", TypBit 32);
    (!"enq_qdepth", TypBit 19); (!"deq_timedelta", TypBit 32); (!"deq_qdepth", TypBit 19);
    (!"ingress_global_timestamp", TypBit 48); (!"egress_global_timestamp", TypBit 48);
    (!"mcast_grp", TypBit 16); (!"egress_rid", TypBit 16); (!"checksum_error", TypBit 1);
    (!"parser_error", TypError); (!"priority", TypBit 3)].

Inductive port :=
  | port_int
  | port_ext.

Definition port_to_Z (p : port) :=
  match p with
  | port_int => 0
  | port_ext => 1
  end.

Definition port_to_sval (p : port) :=
  ValBaseBit (P4Arith.to_loptbool 9 (port_to_Z p)).

Definition out_port_to_Z (p : option port) :=
  match p with
  | Some p => port_to_Z p
  | None => 511
  end.

Definition out_port_to_sval (p : option port) :=
  ValBaseBit (P4Arith.to_loptbool 9 (out_port_to_Z p)).

Inductive process_packet : extern_state -> (Z * port) -> extern_state -> option (Z * port) -> Prop :=
  | process_packet_intro : forall es data in_port es' data' out_port meta' std_meta' class_name inst_path fd m',
      PathMap.get ["main"; "ig"] (ge_inst ge) = Some {|iclass:=class_name; ipath:=inst_path|} ->
      PathMap.get ([class_name; "apply"]) (ge_func ge) = Some fd ->
      0 <= data < Z.pow 2 16 ->
      let hdr := ValBaseStruct [("myHeader",
        ValBaseHeader [("data", ValBaseBit (P4Arith.to_loptbool 16 data))] (Some true))] in
      let meta := force ValBaseNull (uninit_sval_of_typ None M) in
      let std_meta := update "ingress_port" (port_to_sval in_port) (force ValBaseNull (uninit_sval_of_typ None standard_metadata_t)) in
      0 <= data' < Z.pow 2 16 ->
      let hdr' := ValBaseStruct [("myHeader",
        ValBaseHeader [("data", ValBaseBit (P4Arith.to_loptbool 16 data'))] (Some true))] in
      Members.get "egress_spec" std_meta' = out_port_to_sval out_port ->
      exec_func ge read_ndetbit inst_path (PathMap.empty, es) fd nil [hdr; meta; std_meta]
          (m', es') [hdr'; meta'; std_meta'] (SReturn ValBaseNull) ->
      process_packet es (data, in_port) es' (option_map (pair data') out_port).

Inductive process_packets : extern_state -> list (Z * port) -> extern_state -> list (option (Z * port)) -> Prop :=
  | process_packets_nil : forall es,
      process_packets es [] es []
  | process_packets_cons : forall es1 p p' es2 ps ps' es3,
      process_packet es1 p es2 p' ->
      process_packets es2 ps es3 ps' ->
      process_packets es1 (p :: ps) es3 (p' :: ps').

End Switch.
