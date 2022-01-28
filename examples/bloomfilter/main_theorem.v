Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Require Import Coq.Program.Basics.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.bloomfilter.bloomfilter.
Require Import ProD3.examples.bloomfilter.switch.
Require Import ProD3.examples.bloomfilter.verif.

Require Import Coq.ZArith.ZArith. 
Require Import Coq.Lists.List.
Import ListNotations.

Require Import ProD3.core.Coqlib.

Print port.
Definition packet1: BinNums.Z * port := (Z0, port_int).
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
apply H in H10. simpl in H.  in H10.*)
Check (FuncSpec.fundef_satisfies_spec _ _ tgt ge bloomfilter_spec).
bloomfilter_spec.

Check bloomfilter_body. *)Search FuncSpec.fundef_satisfies_spec Semantics.exec_func .
Print FuncSpec.fundef_satisfies_spec_aux.
Print FuncSpec.fundef_satisfies_hoare.
Search Semantics.exec_func.
inversion H3. simpl in *.