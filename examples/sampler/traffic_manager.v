Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.TrafficManager.
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

Definition tofino_tm {PT: Type} (ig_intr_tm_md: Sval) (packet: PT) :=
  traffic_manager mcast_tbl excl_table
    (intr_tm_md_to_input_md ig_intr_tm_md, packet).
