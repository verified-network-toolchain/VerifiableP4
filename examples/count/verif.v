Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.count.p4ast.

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
Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Module Experiment2.
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
Definition v3 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 0)].
Definition v4 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 1)].
Definition v5 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 0)].
Definition v6 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 0)].

Print init_es.


(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_func: { st' & { signal | exec_func ge this inst_m init_st myFundef
    [] [v2; v3; v5] st' [v2; v4; v6] signal} }.
Proof.
  repeat econstructor.
  


  solve [repeat econstructor].
Defined.

