Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.setbit.p4ast.

Require Import Petr4.Maps.
Require Import Petr4.Semantics.
Require Import Petr4.SimplExpr.
Require Import Petr4.V1Model.

Definition prog2 := ltac:(let x := eval compute in (transform_prog NoInfo prog) in exact x).

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition ge := ltac:(let x := eval compute in (load_prog prog) in exact x).

Definition init_ms := ltac:(let x := eval compute in (instantiate_prog prog) in exact x).

Definition init_mem := ltac:(let x := eval compute in (fst init_ms) in exact x).

Definition init_es := ltac:(let x := eval compute in (snd init_ms) in exact x).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition standard_init_mem :=
  PathMap.set [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "dep" |}]
  (IMInst {| P4String.tags := NoInfo; str := "MyDeparser" |}
     [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "dep" |}])
  (PathMap.set
     [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ck" |}]
     (IMInst {| P4String.tags := NoInfo; str := "MyComputeChecksum" |}
        [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ck" |}])
     (PathMap.set
        [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "eg" |}]
        (IMInst {| P4String.tags := NoInfo; str := "MyEgress" |}
           [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "eg" |}])
        (PathMap.set
           [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |}]
           (IMInst {| P4String.tags := NoInfo; str := "MyIngress" |}
              [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |}])
           (PathMap.set
              [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |};
              {| P4String.tags := NoInfo; str := "incr" |}]
              (IMInst {| P4String.tags := NoInfo; str := "Increment" |}
                 [{| P4String.tags := NoInfo; str := "main" |};
                 {| P4String.tags := NoInfo; str := "ig" |};
                 {| P4String.tags := NoInfo; str := "incr" |}])
              (PathMap.set
                 [{| P4String.tags := NoInfo; str := "main" |};
                 {| P4String.tags := NoInfo; str := "vr" |}]
                 (IMInst {| P4String.tags := NoInfo; str := "MyVerifyChecksum" |}
                    [{| P4String.tags := NoInfo; str := "main" |};
                    {| P4String.tags := NoInfo; str := "vr" |}])
                 (PathMap.set
                    [{| P4String.tags := NoInfo; str := "main" |};
                    {| P4String.tags := NoInfo; str := "p" |}]
                    (IMInst {| P4String.tags := NoInfo; str := "MyParser" |}
                       [{| P4String.tags := NoInfo; str := "main" |};
                       {| P4String.tags := NoInfo; str := "p" |}]) PathMap.empty)))))).

Goal init_mem = standard_init_mem.
reflexivity.
Admitted. 

Definition myStatement := MkStatement NoInfo
              (StatAssignment
                   (MkExpression NoInfo
                        (ExpName
                         (BareName {| stags := NoInfo; str := "var" |}))
                        (TypBit 8) InOut)
                   (MkExpression NoInfo
                        (ExpBinaryOp Plus
                             ( (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "var" |}))
                                    (TypBit 8) InOut),
                               (MkExpression NoInfo
                                    (ExpCast (TypBit 8)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 1;
                                                  width_signed := None |})
                                              TypInteger Directionless))
                                    (TypBit 8) Directionless) )) (TypBit 8)
                        Directionless)) StmUnit.

Definition _var := {| stags := NoInfo; str := "var" |}.

Definition myEnv := IdentMap.set _var (Instance [_var]) IdentMap.empty.

Compute (Ops.Ops.eval_binary_op Plus (ValBaseInteger 2)
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
Qed.
