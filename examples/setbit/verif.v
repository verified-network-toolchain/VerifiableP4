Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.setbit.p4ast.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := Eval compute in load_prog prog.

(* Global environment for types *)
Definition ge_typ := Eval compute in match gen_ge_typ prog with Some ge_typ => ge_typ | None => IdentMap.empty end.

Axiom ge_senum : @genv_senum Info.

Definition instantiation := Eval compute in instantiate_prog prog.

(* inst_m *)
Definition inst_m := Eval compute in fst instantiation.

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Notation ident := (P4String.t Info).
Notation path := (list ident).
Definition this : path := [].

Definition init_st : state := (PathMap.set (this ++ !["var"]) (ValBaseBit 8 2) PathMap.empty, init_es).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Module Experiment1.

Definition myBlock' :=
  match Increment with
  | DeclControl _ _ _ _ _ _ block => block
  | _ => BlockNil
  end.

Definition myBlock := Eval compute in myBlock'.

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

Definition this : path := [!"main"; !"ig"].
Definition init_st : state := (PathMap.empty, init_es).

Definition myFundef := Eval compute in
  match PathMap.get [!"MyIngress"] ge with
  | Some x => x
  | None => dummy_fundef
  end.

Definition v1 : @ValueBase Info := ValBaseHeader [(!"firstByte", ValBaseBit 8%nat 0)] true.
Definition v2 : @ValueBase Info := ValBaseStruct [(!"myHeader", v1)].
Definition v3 : @ValueBase Info := ValBaseHeader [(!"firstByte", ValBaseBit 8%nat 3)] true.
Definition v4 : @ValueBase Info := ValBaseStruct [(!"myHeader", v3)].

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_func: { st' & { signal | exec_func ge ge_typ ge_senum this inst_m init_st myFundef
    [] [v2; ValBaseNull; ValBaseNull] st' [v4; ValBaseNull; ValBaseNull] signal} }.
Proof.
  solve [repeat econstructor].
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Definition st3 := Eval compute in (projT1 eval_func).

Definition st' :=   (Semantics.update_val_by_loc this
(PathMap.set
   [!"main"; !"ig"; {| P4String.tags := NoInfo; str := "x" |}]
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
            [!"main"; !"ig";
            {| P4String.tags := NoInfo; str := "x" |}]
            (ValBaseBit 8 (P4Arith.BitArith.mod_bound 8 2))
            (PathMap.sets
               [[!"main"; !"ig";
                {| P4String.tags := NoInfo; str := "hdr" |}];
               [!"main"; !"ig";
               {| P4String.tags := NoInfo; str := "meta" |}];
               [!"main"; !"ig";
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

Goal st3 = st'. reflexivity. Qed.

End Experiment2.

Module Experiment3.

Section Experiment3.

Variable this : path.
Variable x : Z.
Hypothesis range_x : 0 <= x < 1.

Definition myBlock := Eval compute in
  match Increment with
  | DeclControl _ _ _ _ _ _ block => block
  | _ => BlockNil
  end.

Definition myStmt := Eval compute in
  match myBlock with
  | BlockCons stmt _ => stmt
  | _ => MkStatement (default (* Info *)) StatEmpty StmUnit
  end.

Ltac inv H := inversion H; clear H; subst.

Lemma eval_block: hoare_block ge ge_typ ge_senum inst_m this
  (* pre: *) (to_shallow_assertion this [(LInstance !["var"], ValBaseBit 8%nat x)])
  myBlock
  (* post: *) (to_shallow_assertion this [(LInstance !["var"], ValBaseBit 8%nat (x+1))]).
Proof.
  assert (hoare_stmt ge ge_typ ge_senum inst_m this
    (* pre: *) (to_shallow_assertion this [(LInstance !["var"], ValBaseBit 8%nat x)])
    myStmt
    (* post: *) (to_shallow_assertion this [(LInstance !["var"], ValBaseBit 8%nat (x+1))])).
  { intro; intros.
    repeat lazymatch goal with
    | H : exec_stmt _ _ _ _ _ _ _ _ _ |- _ => inv H
    | H : exec_lvalue_expr _ _ _ _ _ _ _ |- _ => inv H
    | H : exec_expr _ _ _ _ _ _ |- _ => inv H
    end.
    { inv H11.
      replace (loc_to_val this (LInstance !!["var"]) st) with (Some (@ValBaseBit Info 8 x)) in H8. 2 : {
        symmetry. apply H.
      }
      inv H8. inv H14. inv H13.
      assert (P4Arith.BitArith.plus_mod 8 x (P4Arith.BitArith.mod_bound 8 1) = x + 1) by admit.
      rewrite H0 in H12.
      inv H12. repeat split.
      simpl. 
Abort.
  (* intro; intros.
  inversion H0.
  2 : {
  eexists. eexists. repeat econstructor.
Defined. *)

End Experiment3.

End Experiment3.


(* Module Experiment3.

Section Experiment3.

Definition this : path := [!"main"; !"ig"].
Definition init_st : state := (PathMap.empty, init_es).

Definition myFundef := Eval compute in
  match PathMap.get [!"MyIngress"] ge with
  | Some x => x
  | None => dummy_fundef
  end.

Variable x : Z.

Definition v1 : @ValueBase Info := ValBaseHeader [(!"firstByte", ValBaseBit 8%nat x)] true.
Definition v2 : @ValueBase Info := ValBaseStruct [(!"myHeader", v1)].
Definition v3 : @ValueBase Info := ValBaseHeader [(!"firstByte", ValBaseBit 8%nat 3)] true.
Definition v4 : @ValueBase Info := ValBaseStruct [(!"myHeader", v3)].

Definition pre : arg_assertion := fun args st => args = [v2; ValBaseNull; ValBaseNull].
Definition post : arg_assertion := fun args st => args = [v4; ValBaseNull; ValBaseNull].

Lemma eval_func : hoare_func ge ge_typ ge_senum inst_m this pre myFundef nil post.
Proof.
  intro. intros.
  
  assert (inargs = [v2; ValBaseNull; ValBaseNull]) by auto; subst inargs.
  inversion H0.
    auto.
  solve [repeat econstructor].
Defined.

End Experiment3.

End Experiment3. *)

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
