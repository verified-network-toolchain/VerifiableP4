Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.verif_Ingress.
Require Import ProD3.examples.sbf.switch.
Require Import ProD3.examples.sbf.flow_proof.
Require Import ProD3.examples.sbf.verif_switch.

Check process_packet_fw_process_packet.

Lemma process_packets_trans_fw : forall es f ps es' rs,
  filter_repr f es ->
  process_packets ge P4_types.metadata_t es ps es' rs ->
  exists f',
    filter_repr f' es' /\ trans_fw f ps f' rs.
Admitted.

Lemma high_level_exec_trans_fw_iff : forall h p res,
  high_level_exec h p res <->
  exists h' f,
    trans_fw (empty (get_tstamp (Znth 0 (h++[p])))) (h ++ [p]) f
    (h' ++ [res]).
Admitted.

Definition init_es := ltac:(get_init_es am_ge p4ast.prog).

Theorem main_theorem : forall h p es' rs' res,
  process_packets ge P4_types.metadata_t init_es (h ++ [p]) es' (rs' ++ [res]) ->
  valid_flow (h ++ [p]) ->
  property h p res.
Proof.
  intros.
  eapply process_packets_trans_fw with (f := empty (get_tstamp (Znth 0 (h++[p])))) in H.
  2 : { admit. }
  eapply flow_level_property; auto.
  apply <- high_level_exec_trans_fw_iff.
  destruct H. destruct H.
  eauto.
Admitted.
