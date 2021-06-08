Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.count.p4ast.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Psatz.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Arith.
Require Import Poulet4.P4String.
Require Import Poulet4.Ops.
Require Import ProD3.core.Hoare.
(* Require Import ProD3.core.AssertionLang. *)

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := Eval compute in gen_ge prog.

Definition instantiation := Eval compute in instantiate_prog prog.

(* inst_m *)
Definition inst_m := Eval compute in fst instantiation.

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Notation ident := (P4String.t Info).
Notation path := (list ident).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Module Experiment.
Definition this : path := [!"main"; !"ig"].
Definition init_st : state := (PathMap.empty, init_es).

(* 
new_register *)

Definition myFundef := Eval compute in
  match PathMap.get [!"MyIngress"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Definition v1 : @ValueBase Info := ValBaseHeader [(!"firstBit", ValBaseBit 1%nat 0)] true.
Definition v2 : @ValueBase Info := ValBaseStruct [(!"myHeader", v1)].
Definition v3 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 10)].
Definition v4 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 0)].
Definition v5 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 10)].
Definition v6 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 0)].

(* 
Lemma test: (0 <= P4Arith.BitArith.mod_bound 32 0)%Z.
Proof.
  apply Zlt_succ_le.
  simpl. reflexivity.
Qed. *)

(* Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
Print init_es. *)

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_func: { st' & { signal | exec_func ge this inst_m init_st myFundef
    [] [v2; v3; v5] st' [v2; v4; v6] signal} }.
Proof.
  solve [repeat econstructor].
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Definition st' := Eval compute in (projT1 eval_func).
Print st'.

(* Functional model *)
Notation Val := (@ValueBase Info).
Notation P4String := (P4String.t Info).
Definition array_state := (list Z).
Definition NUM_ENTRY := 2.

Fixpoint array_incr (ast: array_state) (i: nat) : array_state :=
  match i, ast with
    | O, hd :: tl => (hd + 1) :: tl
    | S n, hd :: tl => array_incr tl n
    | _, [] => ast
  end.

Definition ast_match (st : state) (ast : array_state) : Prop :=
  exists content,
  PathMap.get !["main"; "ig"; "myCounter"] (snd st) = Some (ObjRegister (mk_register 1%nat NUM_ENTRY content)) /\
  content = ast.

Definition field_contains (v : Val) (name : P4String) (data: Val) : Prop :=
  match v with
  | ValBaseStruct fields => AList.get fields name = Some data
  | ValBaseHeader fields true => AList.get fields name = Some data
  | _ => False
  end.

Section Experiment1.
Variable fbit : Z.
Variable hdr : Val.
Variable meta : Val.
Variable standard_metadata : Val.
Variable ast : array_state.

Definition pre (* (fbit : Z) (hdr meta standard_metadata : Val) *) (in_args : list Val) (st : state) :=
  in_args = [ValBaseStruct [(!"myHeader", hdr)]; meta; standard_metadata]
    /\ field_contains hdr !"firstBit" (ValBaseBit 1%nat fbit)
    /\ ast_match st ast.

Definition process (fbit : Z) (ast : array_state) : (array_state * Z) :=
  if fbit =? 1 then
    (array_incr ast 1, 48)
  else
    (array_incr ast 0, 0).

Definition post (* (fbit : Z) (hdr meta standard_metadata : Val) *) (out_args : list Val) (st : state) :=
  let (ast', eport) := process fbit ast in
  exists standard_metadata' std_meta_fields std_meta_fields',
  out_args = [hdr; meta; standard_metadata']
    /\ standard_metadata = ValBaseStruct std_meta_fields 
    /\ standard_metadata' = ValBaseStruct std_meta_fields'
    /\ field_contains standard_metadata' !"egress_spec" (ValBaseBit 9%nat eport)
    /\ Ops.eval_binary_op_eq (ValBaseStruct (AList.filter std_meta_fields (P4String.equivb !"egress_spec" )))
                         (ValBaseStruct (AList.filter std_meta_fields' (P4String.equivb !"egress_spec" )))
       = Some true
    /\ ast_match st ast'.

Lemma body_counter : hoare_func ge inst_m this pre myFundef nil post.
Abort.

End Experiment1.

End Experiment.
