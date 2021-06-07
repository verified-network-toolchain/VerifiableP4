Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.count.p4ast.
(* Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Nia. *)
Require Import Psatz.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Arith.
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

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_func: { st' & { signal | exec_func ge this inst_m init_st myFundef
    [] [v2; v3; v5] st' [v2; v4; v6] signal} }.
Proof.
  solve [repeat econstructor].
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Definition st'' := Eval compute in (projT1 eval_func).

Definition st' := (PathMap.set (loc_to_path this (LInstance !["meta"]))
(ValBaseStruct
   [(!"counter",
    ValBaseBit
      (reg_width
         {| reg_width := 4; reg_size := 2; reg_content := [0; 0] |})
      (Znth
         (BitArith.mod_bound (Pos.of_nat 32)
            (value
               {| tags := NoInfo; value := 0; width_signed := None |}))
         (reg_content
            {| reg_width := 4; reg_size := 2; reg_content := [0; 0] |})))])
(PathMap.set (loc_to_path this (LInstance !["standard_metadata"]))
   (ValBaseStruct
      [(!"egress_spec",
       ValBaseBit 9
         (BitArith.mod_bound (Pos.of_nat 9)
            (value
               {| tags := NoInfo; value := 0; width_signed := None |})))])
   (PathMap.sets
      (filter_in
         (map (map_fst (fun param : ident => (this ++ [param])%list)) []))
      (extract_invals [])
      (PathMap.sets
         (filter_in
            (map (map_fst (fun param : ident => (this ++ [param])%list))
               [(!"hdr", InOut); (!"meta", InOut);
               (!"standard_metadata", InOut)])) 
         [v2; v3; v5] PathMap.empty))),
PathMap.set [!"main"; !"ig"; !"myCounter"]
(ObjRegister
  {|
    reg_width :=
      reg_width
        {| reg_width := 4; reg_size := 2; reg_content := [0; 0] |};
    reg_size :=
      reg_size
        {| reg_width := 4; reg_size := 2; reg_content := [0; 0] |};
    reg_content :=
      upd_Znth
        (BitArith.mod_bound (Pos.of_nat 32)
           (value {| tags := NoInfo; value := 0; width_signed := None |}))
        (reg_content
           {| reg_width := 4; reg_size := 2; reg_content := [0; 0] |})
        (BitArith.plus_mod
           (Pos.of_nat
              (reg_width
                 {|
                   reg_width := 4; reg_size := 2; reg_content := [0; 0]
                 |}))
           (Znth
              (BitArith.mod_bound (Pos.of_nat 32)
                 (value
                    {|
                      tags := NoInfo; value := 0; width_signed := None
                    |}))
              (reg_content
                 {|
                   reg_width := 4; reg_size := 2; reg_content := [0; 0]
                 |}))
           (BitArith.mod_bound (Pos.of_nat 4)
              (value
                 {| tags := NoInfo; value := 1; width_signed := None |})))
  |}) init_es).

Goal st'' = st'. reflexivity. Qed.

End Experiment.
