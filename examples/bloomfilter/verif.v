Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.bloomfilter.bloomfilter.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
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
Notation Val := (@ValueBase Info).
Definition this : path := [].

Definition init_st : state := (PathMap.set (this ++ !["var"]) (ValBaseBit 8 2) PathMap.empty, init_es).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Module Experiment1.

Definition MyIngress_fundef := Eval compute in
  match PathMap.get [!"MyIngress"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Definition this : path := !["main"; "ig"].

Notation Filter := (Filter Z).

Definition bloomfilter_state : Type := Filter * Filter * Filter.

Definition NUM_ENTRY := 1024.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Definition filter_match (st : state) (p : path) (f : Filter) : Prop :=
  exists content,
  PathMap.get p (snd st) = Some (ObjRegister (mk_register 1%nat NUM_ENTRY content)) /\
  forall i : Z, Znth i content = bool_to_Z (f i). (* out-of-bounds indexing is used *)

Definition bst_match (st : state) (bst : bloomfilter_state) : Prop :=
  let (rest, bloom2) := bst in
  let (bloom0, bloom1) := rest in
  filter_match st !["bloom0"] bloom0
    /\ filter_match st !["bloom1"] bloom1
    /\ filter_match st !["bloom2"] bloom2.

Axiom header_encodes : forall (hdr : Val) (rw : Z) (data : Z), Prop.

Section Experiment1.

Variable rw : Z.
Variable data : Z.
Variable hdr : Val.
Variable meta : Val.
Variable standard_metadata : Val.
Variable bst : bloomfilter_state.

Definition pre (* (rw data : Z) (hdr meta standard_metadata : Val) *) (args : list Val) (st : state) :=
  args = [hdr; meta; standard_metadata]
    /\ header_encodes hdr rw data
    /\ bst_match st bst.

Axiom CRC : Z -> Z.

Definition process (rw data : Z) (bst : bloomfilter_state) : bloomfilter_state :=
  bloomfilter.add Z Z.eqb CRC CRC CRC bst data.

Definition post (* (rw data : Z) (hdr meta standard_metadata : Val) *) (args : list Val) (st : state) :=
  args = [hdr; meta; standard_metadata]
  /\ bst_match st (process rw data bst).


Lemma body_bloomfilter : hoare_func ge inst_m this pre MyIngress_fundef nil post.
Abort.

End Experiment1.

End Experiment1.
