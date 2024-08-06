Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf_gen.p4ast.
Require Import ProD3.examples.sbf_gen.common.
Require Import ProD3.examples.sbf_gen.verif_Ingress.
Require Import ProD3.examples.sbf_gen.switch.
Require Import ProD3.examples.sbf_gen.flow_proof.
Require Import ProD3.examples.sbf_gen.verif_switch.

Definition abs_flow_wf (ps : list Packet) : Prop :=
  forall i : Z, 0 <= i < Zlength ps ->
  0 <= fst (snd (fst (fst (Znth i ps)))) < Z.pow 2 32
    /\ 0 <= snd (snd (fst (fst (Znth i ps)))) < Z.pow 2 32.

Lemma process_packets_trans_fw : forall es f ps es' rs,
  filter_repr f es ->
  abs_flow_wf ps ->
  process_packets ge P4_types.metadata_t es ps es' rs ->
  exists f',
    filter_repr f' es' /\ trans_fw f ps f' rs.
Proof.
  intros es f ps; revert es f; induction ps as [ | p ps ?]; intros.
  - inv H1.
    eexists; split; eauto. constructor.
  - inv H1.
    assert (abs_flow_wf ps). {
      clear -H0. unfold abs_flow_wf in *.
      intros. specialize (H0 (i + 1) ltac:(list_solve)).
      replace (Znth (i + 1) (p :: ps)) with (Znth i ps) in * by list_solve.
      lia.
    }
    assert (H2 : 0 <= fst (snd (fst (fst p))) < Z.pow 2 32 /\
                   0 <= snd (snd (fst (fst p))) < Z.pow 2 32). {
      clear -H0. unfold abs_flow_wf in *.
      specialize (H0 0 ltac:(list_solve)).
      list_solve.
    }
    destruct H2.
    eapply process_packet_fw_process_packet in H5; only 2-4 : eassumption.
    destruct H5 as [f' []].
    specialize (IHps _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    destruct IHps as [? []].
    eexists; split; eauto.
    eapply trans_cons; eauto.
Qed.

Lemma high_level_exec_trans_fw_iff : forall h p res,
  high_level_exec h p res <->
  exists h' f,
    trans_fw (empty (get_tstamp (Znth 0 (h++[p])))) (h ++ [p]) f
    (h' ++ [res]).
Proof.
  intros; split; intros.
  - destruct H as [? [? [? []]]].
    repeat eexists; econstructor; eauto.
  - destruct H as [? [? H]].
    eapply trans_app_inv in H. 2 : auto.
    destruct H as [? [? [? [? []]]]].
    eapply trans_cons_inv in H0. 2 : auto.
    destruct H0 as [? [? [? [? []]]]].
    inv H2. 2 : { clear -H4. list_solve. }
    replace res with x5. 2 : {
      clear -H1.
      pose (Inhabitant_Result := (res : Inhabitant Result)).
      assert (Znth (Zlength x) (x ++ [res]) = (Znth (Zlength x) (x2 ++ [x5]))) by congruence.
      list_solve.
    }
    repeat eexists; eauto.
Qed.

Definition init_es := ltac:(get_init_es am_ge p4ast.prog).

Definition filter_empty := @ConFilter.filter_empty num_frames num_rows num_slots H_num_frames H_num_rows H_num_slots.

Ltac simpl_init_es_entry :=
  match goal with
  | |- context [PathMap.get ?p init_es] =>
      let obj' := eval cbv-[am_ge Tofino.extern_match] in
        (PathMap.get p init_es) in
      change (PathMap.get p init_es) with obj'
  end.

Transparent Tofino.new_register.
Lemma init_es_reg_repr :
  @Some (extern_object)
    (Tofino.ObjRegister
       (Tofino.new_register 262144
          (ValBaseBit [false; false; false; false; false; false; false; false]))) =
  Some
    (Tofino.ObjRegister (map FilterRepr.bool_to_val (` (ConFilter.row_empty H_num_slots)))).
Proof.
  unfold Tofino.new_register.
  unfold ConFilter.row_empty, proj1_sig.
  rewrite map_Zrepeat.
  f_equal.
Qed.
Opaque Tofino.new_register.

Lemma filter_repr_empty_init_es : forall t,
  filter_repr (empty t) init_es.
Proof.
  intros.
  unfold filter_repr; hnf.
  exists filter_empty.
  split.
  { repeat first [
      apply conj; hnf
    | apply I
    ];
    try simpl_init_es_entry;
    try apply init_es_reg_repr.
    - exists 0.
      repeat first [
        apply conj; hnf
      | apply I
      ].
      + simpl_init_es_entry.
        reflexivity.
      + reflexivity.
    - simpl. inversion 1.
    - auto.
    - reflexivity.
  }
  hnf.
  apply AbsFilter.filter_sim_empty;
    resolve_parameter_conditions.
Qed.

Theorem main_theorem : forall h p es' rs' res,
  process_packets ge P4_types.metadata_t init_es (h ++ [p]) es' (rs' ++ [res]) ->
  abs_flow_wf (h ++ [p]) ->
  valid_flow (h ++ [p]) ->
  property h p res.
Proof.
  intros.
  eapply process_packets_trans_fw with (f := empty (get_tstamp (Znth 0 (h++[p])))) in H.
  3 : auto.
  2 : apply filter_repr_empty_init_es.
  eapply flow_level_property; auto.
  apply <- high_level_exec_trans_fw_iff.
  destruct H. destruct H.
  eauto.
Qed.
