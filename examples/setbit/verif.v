Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.setbit.p4ast.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := ltac:(let x := eval compute in (load_prog prog) in exact x).

(* Global environment for types *)
(* Definition ge_typ := ltac:(let x := eval compute in (gen_ge_typ prog) in exact x). *)
Axiom ge_typ : @genv_typ Info.
Axiom ge_senum : @genv_senum Info.

Definition instantiation := ltac:(let x := eval compute in (instantiate_prog prog) in exact x).

(* inst_m *)
Definition inst_m := ltac:(let x := eval compute in (fst instantiation) in exact x).

Definition _var := {| stags := NoInfo; str := "var" |}.

(* Initial extern state *)
Definition init_es := ltac:(let x := eval compute in (snd instantiation) in exact x).

Notation ident := (P4String.t Info).
Notation path := (list ident).
Definition this : path := [].

Definition init_st : state := (PathMap.set (this ++ [_var]) (ValBaseBit 8 2) PathMap.empty, init_es).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Module Experiment1.

Definition myBlock' :=
  match Increment with
  | DeclControl _ _ _ _ _ _ block => block
  | _ => BlockNil
  end.

Definition myBlock := ltac:(let x := eval compute in myBlock' in exact x).

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_block: {signal & { st' | exec_block ge ge_typ ge_senum this inst_m init_st myBlock st' signal } }.
Proof.
  eexists. eexists. repeat econstructor.
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.
Definition st' :=
(update_memory
(PathMap.set (this ++ [{| P4String.tags := NoInfo; str := "var" |}])
   (ValBaseBit 8
      (P4Arith.BitArith.plus_mod (Pos.of_nat 8) 2
         (P4Arith.BitArith.mod_bound (Pos.of_nat 8)
            (value
               {| tags := NoInfo; value := 1; width_signed := None |})))))
init_st).
Definition st'' := ltac:(let x := eval compute in st' in exact x).
Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

End Experiment1.

Module Experiment2.

Definition main_string : ident := {| P4String.tags := NoInfo; P4String.str := "main" |}.
Definition ig_string : ident := {| P4String.tags := NoInfo; P4String.str := "ig" |}.
Definition this : path := [main_string; ig_string].
Definition init_st : state := (PathMap.empty, init_es).
Definition MyIngress_string : ident := {| P4String.tags := NoInfo; P4String.str := "MyIngress" |}.

Definition myFundef' :=
  match PathMap.get [MyIngress_string] ge with
  | Some x => x
  | None => dummy_fundef
  end.

Definition myFundef := ltac:(let x := eval compute in myFundef' in exact x).

Definition firstByte_string : ident := {| P4String.tags := NoInfo; P4String.str := "firstByte" |}.
Definition v1 : @ValueBase Info := ValBaseHeader [(firstByte_string, ValBaseBit 8%nat 0)] true.
Definition myHeader_string : ident := {| P4String.tags := NoInfo; P4String.str := "myHeader" |}.
Definition v2 : @ValueBase Info := ValBaseStruct [(myHeader_string, v1)].
Definition v3 : @ValueBase Info := ValBaseHeader [(firstByte_string, ValBaseBit 8%nat 3)] true.
Definition v4 : @ValueBase Info := ValBaseStruct [(myHeader_string, v3)].

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_block: { st' & { signal | exec_func ge ge_typ ge_senum this inst_m init_st myFundef
    [] [v2; ValBaseNull; ValBaseNull] st' [v4; ValBaseNull; ValBaseNull] signal} }.
Proof.
  eexists. eexists.
  econstructor. econstructor. 
  repeat econstructor.
  econstructor.
  econstructor.
  repeat econstructor.
  econstructor.
  econstructor. simpl.
  (* Must be slow to eapply. *)
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eapply read_lmember_struct.
  repeat econstructor.
  repeat econstructor.
  repeat econstructor.
  repeat econstructor.
  repeat econstructor.
  repeat econstructor.
  simpl. reflexivity.
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Definition st3 := Eval compute in (projT1 eval_block).

Definition st' :=   (update_val_by_loc this
(PathMap.set
   [main_string; ig_string; {| P4String.tags := NoInfo; str := "x" |}]
   (ValBaseBit 8
      (P4Arith.BitArith.plus_mod 8 (P4Arith.BitArith.mod_bound 8 2)
         (P4Arith.BitArith.mod_bound 8 1)))
   (PathMap.set
      [{| P4String.tags := NoInfo; str := "main" |};
      {| P4String.tags := NoInfo; str := "ig" |};
      {| P4String.tags := NoInfo; str := "incr" |};
      {| P4String.tags := NoInfo; str := "var" |}]
      (ValBaseBit 8
         (P4Arith.BitArith.plus_mod 8 (P4Arith.BitArith.mod_bound 8 2)
            (P4Arith.BitArith.mod_bound 8 1)))
      (PathMap.sets
         [[{| P4String.tags := NoInfo; str := "main" |};
          {| P4String.tags := NoInfo; str := "ig" |};
          {| P4String.tags := NoInfo; str := "incr" |};
          {| P4String.tags := NoInfo; str := "var" |}]]
         [ValBaseBit 8 (P4Arith.BitArith.mod_bound 8 2)]
         (PathMap.set
            [main_string; ig_string;
            {| P4String.tags := NoInfo; str := "x" |}]
            (ValBaseBit 8 (P4Arith.BitArith.mod_bound 8 2))
            (PathMap.sets
               [[main_string; ig_string;
                {| P4String.tags := NoInfo; str := "hdr" |}];
               [main_string; ig_string;
               {| P4String.tags := NoInfo; str := "meta" |}];
               [main_string; ig_string;
               {| P4String.tags := NoInfo; str := "standard_metadata" |}]]
               [v2; ValBaseNull; ValBaseNull] PathMap.empty)))),
init_es) (LInstance [{| P4String.tags := NoInfo; str := "hdr" |}])
(ValBaseStruct
   [({| P4String.tags := NoInfo; str := "myHeader" |},
    ValBaseHeader
      [({| P4String.tags := NoInfo; str := "firstByte" |},
       ValBaseBit 8
         (P4Arith.BitArith.plus_mod 8 (P4Arith.BitArith.mod_bound 8 2)
            (P4Arith.BitArith.mod_bound 8 1)))] true)])).

Definition st'' := ltac:(let x := eval compute in st' in exact x).
(* Print st''. *)

Goal st3 = st'. reflexivity.


(* Compute (Ops.Ops.eval_binary_op Plus (ValBaseInteger 2)
        (ValBaseBit 8 1)).

Lemma path_equivb_reflexivity :
  forall tag_t (l : list (P4String.t tag_t)),
  @path_equivb tag_t l l = true.
Proof.
  induction l as [| x xs IHx].
  - reflexivity.
  - unfold path_equivb in *. unfold list_eqb in *.
    rewrite Nat.eqb_refl in *.
    rewrite Bool.andb_true_l in *.
    simpl.
    unfold equivb at 1.
    rewrite eqb_refl.
    rewrite Bool.andb_true_l.
    apply IHx.
Qed.

Ltac inv H := inversion H; subst; clear H.


Lemma property1: forall ge this decls m exts,    PathMap.get (name_cons this _var) m = Some (ValBaseBit 8 2) ->    exists m',    exec_stmt ge this decls myEnv init_mem (m, exts) myStatement (m', exts) SContinue /\    PathMap.get (name_cons this _var) m' = Some (ValBaseBit 8 3).
Proof.
  intros. 
  remember (PathMap.set (this ++ [_var]) (ValBaseBit 8 3) m) as m'.
  exists m'. split.
  - unfold myStatement. 
    remember (BareName {| P4String.tags := NoInfo; str := "var" |}) as name.
    apply eval_stmt_assignment with 
      (lv := (MkValueLvalue (ValLeftName name) (TypBit 8))) 
      (v := (@ValBaseBit Info 8 3)).
    + apply exec_lvalue_expr_name.
    + apply exec_expr_binary_op with 
        (largv := (@ValBaseBit Info 8 2))
        (rargv := (@ValBaseBit Info 8 1)).
      { apply exec_expr_name. unfold name_cons in H.
        unfold name_to_val. rewrite Heqname. simpl. rewrite H. reflexivity. }
      { apply exec_expr_cast with
          (oldv := (@ValBaseInteger Info 1)).
        { apply exec_expr_int. unfold eval_p4int. reflexivity. }
        { reflexivity. } }
      { reflexivity. }
    + unfold assign_lvalue, update_val_by_name. rewrite Heqname.
      unfold ident_to_path, update_memory. simpl.
      rewrite Heqm'. reflexivity.
  - rewrite Heqm'. unfold PathMap.get, PathMap.set, name_cons.
    rewrite path_equivb_reflexivity. reflexivity.
Qed. *)
