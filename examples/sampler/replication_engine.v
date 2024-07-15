Require Import ProD3.core.PacketFormat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.ReplicationEngine.
Require Import ProD3.core.Tofino.
Require Import ProD3.core.TofinoPipeline.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation Port := Z (only parsing).

Definition ctrl_node_setting: MulticastLevel1Node Port:=
  Build_MulticastLevel1Node 123 0 false [129].

Definition excl_table: L2_exclusion_table Port := fun _ => [].

Definition mcast_tbl: multicast_table Port := [(1, [ctrl_node_setting])].

Definition validityP4Bit_to_Z (s: Sval): option Z :=
  match s with
  | ValBaseBit l => match lift_option l with
                   | Some s => match (snd (P4Arith.BitArith.from_lbool s)) with
                              | 0 => None
                              | n => Some n
                              end
                   | None => None
                   end
  | _ => None
  end.

Definition intr_tm_md_to_input_md (ig_intr_tm_md: Sval): InputMetadata Port :=
  let ucast_port := get "ucast_egress_port" ig_intr_tm_md in
  let mcast_grp_a := get "mcast_grp_a" ig_intr_tm_md in
  let mcast_grp_b := get "mcast_grp_b" ig_intr_tm_md in
  Build_InputMetadata (validityP4Bit_to_Z ucast_port)
    (validityP4Bit_to_Z mcast_grp_a)
    (validityP4Bit_to_Z mcast_grp_b) 0 0 0.

Definition output_md_to_egress_intr_md (md: OutputMetadata Port) : Val :=
  ValBaseHeader
    [("_pad0", P4BitV 7 0); ("egress_port", P4BitV 9 md.(out_meta_egress_port));
     ("_pad1", P4BitV 5 0); ("enq_qdepth", P4BitV 19 0); ("_pad2", P4BitV 6 0);
     ("enq_congest_stat", P4BitV 2 0); ("_pad3", P4BitV 14 0); ("enq_tstamp", P4BitV 18 0);
     ("_pad4", P4BitV 5 0); ("deq_qdepth", P4BitV 19 0); ("_pad5", P4BitV 6 0);
     ("deq_congest_stat", P4BitV 2 0); ("app_pool_congest_stat", P4BitV 8 0);
     ("_pad6", P4BitV 14 0); ("deq_timedelta", P4BitV 18 0);
     ("egress_rid", P4BitV 16 md.(out_meta_egress_rid)); ("_pad7", P4BitV 7 0);
     ("egress_rid_first", P4BitV 1 0); ("_pad8", P4BitV 3 0); ("egress_qid", P4BitV 5 0);
     ("_pad9", P4BitV 5 0); ("egress_cos", P4BitV 3 0); ("_pad10", P4BitV 7 0);
     ("deflection_flag", P4BitV 1 0); ("pkt_length", P4BitV 16 0)] true.

Definition encode_tm_output (elem: EgressPacketDescriptor Port packet) : packet :=
  match elem with
  | (md, pkt) => encode (output_md_to_egress_intr_md md) ++ pkt
  end.

Lemma output_is_eg_intr_md:
  forall md, ⊫ᵥ output_md_to_egress_intr_md md \: egress_intrinsic_metadata_t.
Proof.
  intros. destruct md. unfold output_md_to_egress_intr_md. simpl.
  split; [ repeat constructor | reflexivity].
Qed.

Definition tofino_pre (ig_intr_tm_md: Sval) (pkt: packet) :=
  qmap encode_tm_output
    (replication_engine mcast_tbl excl_table (intr_tm_md_to_input_md ig_intr_tm_md, pkt)).

Lemma tofino_tm_output: forall md pkt p,
    In p (list_rep (tofino_pre md pkt)) ->
    exists eg_md, ⊫ᵥ eg_md \: egress_intrinsic_metadata_t /\ p ⫢ [⦑ encode eg_md ⦒; ⦑ pkt ⦒].
Proof.
  intros. unfold tofino_pre in H. rewrite qmap_map in H. rewrite in_map_iff in H.
  destruct H as [x [? ?]]. apply replication_engine_output_snd in H0. simpl in H0.
  clear md. destruct x as [md out]. simpl in H0. subst out. unfold encode_tm_output in H.
  exists (output_md_to_egress_intr_md md). split.
  - apply output_is_eg_intr_md.
  - subst. exists [encode (output_md_to_egress_intr_md md); pkt]. split.
    + Opaque encode. simpl. rewrite app_nil_r. Transparent encode. reflexivity.
    + repeat constructor.
Qed.
