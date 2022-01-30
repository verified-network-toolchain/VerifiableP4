Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Require Import Coq.Program.Basics.
Require Import Poulet4.Maps.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.bloomfilter.bloomfilter.
Require Import ProD3.examples.bloomfilter.switch.
Require Import ProD3.examples.bloomfilter.verif.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Require Import ProD3.core.Coqlib.

Definition process' (bf : bloomfilter_state) (p : Z * port) :=
  let (data, pt) := p in
  match pt with
  | port_int =>
      (bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf data, (Some (data, port_ext)))
  | port_ext =>
      if bloomfilter.query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data then
        (bf, Some (data, port_int))
      else
        (bf, None)
  end.

Definition bf_encode (es : V1Model.extern_state) (bf : bloomfilter_state) :=
  PathMap.get ["bloom0"] es = Some (reg_encode (bloom0 bf))
    /\ PathMap.get ["bloom1"] es = Some (reg_encode (bloom1 bf))
    /\ PathMap.get ["bloom2"] es = Some (reg_encode (bloom2 bf)).

Open Scope Z_scope.

Lemma process_packet_prop : forall es bf p es' p',
  process_packet ge custom_metadata_t es p es' p' ->
  bf_encode es bf ->
  exists bf',
    process' bf p = (bf', p') /\ bf_encode es' bf'.
Proof.
  intros.
  inv H.
  inv H1. inv H2.
  eapply (proj1 bloomfilter_body (port_to_Z in_port) data bf) in H6.
  2 : {
    destruct in_port; simpl; lia.
  }
  2 : {
    clear H5.
    split. {
      simpl. unfold AssertionLang.arg_denote, AssertionLang.arg_satisfies.
      destruct in_port; Tactics.Forall2_sval_refine.
    }
    split. {
      repeat constructor.
    }
    destruct H0 as [? []].
    repeat constructor.
    - red; simpl; destruct (PathMap.get ["bloom0"] es); inv H; auto.
    - red; simpl; destruct (PathMap.get ["bloom1"] es); inv H0; auto.
    - red; simpl; destruct (PathMap.get ["bloom2"] es); inv H1; auto.
  }
  destruct H6 as  [? [? []]].
  exists (fst (process (port_to_Z in_port) data bf)).
  split.
  2 : {
    destruct H6 as [? [? []]].
    repeat constructor.
    - red in H6; simpl in H6; destruct (PathMap.get ["bloom0"] es'); inv H6; auto.
    - red in H7; simpl in H7; destruct (PathMap.get ["bloom1"] es'); inv H7; auto.
    - red in H8; simpl in H8; destruct (PathMap.get ["bloom2"] es'); inv H8; auto.
  }
  assert (data' = data
    /\ out_port_to_Z out_port = snd (process (port_to_Z in_port) data bf)).
  {
    inv H.
    split.
    - clear -H3 H4 H10.
      subst hdr'.
      inv H10. inv H1. destruct H5.
      clear -H3 H4 H0. inv H0. inv H7. destruct H2.
      clear -H3 H4 H0.
      apply SvalRefine.sval_refine_to_loptbool_eq in H0; eauto.
    - inv H12. inv H13.
      clear -H5 H11.
      apply SvalRefine.sval_refine_get with (f := "egress_spec") in H11.
      simpl in H11.
      rewrite H5 in H11.
      apply SvalRefine.sval_refine_to_loptbool_eq in H11; eauto.
      + destruct in_port; simpl.
        2 : destruct (query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data); simpl.
        all : lia.
      + destruct out_port as [[] | ]; simpl.
        all : lia.
  }
  clear -H7.
  destruct H7; subst.
  unfold process, process' in *.
  destruct in_port; destruct out_port as [[] | ];
    simpl in *; try solve [inv H0]; auto;
    destruct (query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data);
    try solve [inv H0]; auto.
Qed.

(* Definition packet1: BinNums.Z * port := (Z0, port_int).
Definition packet2: BinNums.Z * port := (1%Z, port_ext).

Lemma Test1: forall st' output,
     @process_packets _ _ ge custom_metadata_t  init_es  [packet1;packet2] st' output -> True.
Proof.
intros. inv H. 
unfold packet1 in H3.
unfold packet2 in H6.
inv H3. 
specialize ( bloomfilter_body). intros.
unfold FuncSpec.fundef_satisfies_spec in H.  destruct H. simpl in H.
specialize (H 0%Z Z0 (empty Z, empty Z, empty Z)).
unfold Hoare.hoare_func in H.
inv H1. inv H2.
apply H in H10. clear H.
2:{ clear H H10. 
  split. red. red. Tactics.Forall2_sval_refine.
  split. red. red. simpl; trivial.
  repeat constructor. }
trivial.
Qed.
Definition packet1': BinNums.Z * port := (Z0, port_int).
Definition packet2': BinNums.Z * port := (Z0, port_ext).

Lemma Test2: forall es' output,
     @process_packets _ _ ge custom_metadata_t  init_es  [packet1';packet2'] es' output -> 
     (*st' = add *)True.
Proof.
intros. inv H. Print  V1Model.extern_state.
unfold packet1 in H3.
unfold packet2 in H6.
inv H3. 
specialize ( bloomfilter_body). intros.
unfold FuncSpec.fundef_satisfies_spec in H.  destruct H. simpl in H.
specialize (H 0%Z Z0 (empty Z, empty Z, empty Z)).
unfold Hoare.hoare_func in H.
inv H1. inv H2.
apply H in H10. clear H.
2:{ clear H H10. 
  split. red. red. Tactics.Forall2_sval_refine.
  split. red. red. simpl; trivial.
  repeat constructor. }
inv H10. destruct H1 as [K1 [K2 K3]]. clear K1 K2.
specialize ( bloomfilter_body). intros.
unfold FuncSpec.fundef_satisfies_spec in H.  destruct H. simpl in H.
specialize (H 0%Z Z0 (empty Z, empty Z, empty Z)).
unfold Hoare.hoare_func in H.
inv H1. inv H2.
apply H in H10. clear H.
2:{ clear H H10. 
  split. red. red. Tactics.Forall2_sval_refine.
  split. red. red. simpl; trivial.
  repeat constructor. }
inv H10. destruct H1 as [K1 [K2 K3]]. clear K1 K2.
trivial.
Qed.
extern_state -> list (option (Z * port))
 trivial. red. red. simpl. split. reflexivity. split. reflexivity. 
    subst hdr. 
     simpl.  constructor.
    + 
  econstructor. simpl.  split. AssertionNotations.ARG.
assert (AP: ["main"; "ig"] = inst_path). 
{ clear H H10. inv H1; trivial. }
subst inst_path.
inv H2.
apply H in H10.
specialize (H  bloomfilter_state
apply H in H10. simpl in H.  in H10.
Check (FuncSpec.fundef_satisfies_spec _ _ tgt ge bloomfilter_spec).
bloomfilter_spec.

Check bloomfilter_body. Search FuncSpec.fundef_satisfies_spec Semantics.exec_func .
Print FuncSpec.fundef_satisfies_spec_aux.
Print FuncSpec.fundef_satisfies_hoare.
Search Semantics.exec_func.
inversion H3. simpl in *. *)
