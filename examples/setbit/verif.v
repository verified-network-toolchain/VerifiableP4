Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.setbit.p4ast.

Require Import Petr4.Semantics.
Require Import Petr4.Trans.

Definition prog2 := ltac:(let x := eval compute in (transform_prog NoInfo prog) in exact x).

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition ge := ltac:(let x := eval compute in (load_prog prog) in exact x).

Definition init_mem := ltac:(let x := eval compute in (instantiate_prog prog) in exact x).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Definition standard_init_mem :=
  PathMap.set [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "dep" |}]
  (MInstance {| P4String.tags := NoInfo; str := "MyDeparser" |}
     [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "dep" |}])
  (PathMap.set
     [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ck" |}]
     (MInstance {| P4String.tags := NoInfo; str := "MyComputeChecksum" |}
        [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ck" |}])
     (PathMap.set
        [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "eg" |}]
        (MInstance {| P4String.tags := NoInfo; str := "MyEgress" |}
           [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "eg" |}])
        (PathMap.set
           [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |}]
           (MInstance {| P4String.tags := NoInfo; str := "MyIngress" |}
              [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |}])
           (PathMap.set
              [{| P4String.tags := NoInfo; str := "main" |}; {| P4String.tags := NoInfo; str := "ig" |};
              {| P4String.tags := NoInfo; str := "incr" |}]
              (MInstance {| P4String.tags := NoInfo; str := "Increment" |}
                 [{| P4String.tags := NoInfo; str := "main" |};
                 {| P4String.tags := NoInfo; str := "ig" |};
                 {| P4String.tags := NoInfo; str := "incr" |}])
              (PathMap.set
                 [{| P4String.tags := NoInfo; str := "main" |};
                 {| P4String.tags := NoInfo; str := "vr" |}]
                 (MInstance {| P4String.tags := NoInfo; str := "MyVerifyChecksum" |}
                    [{| P4String.tags := NoInfo; str := "main" |};
                    {| P4String.tags := NoInfo; str := "vr" |}])
                 (PathMap.set
                    [{| P4String.tags := NoInfo; str := "main" |};
                    {| P4String.tags := NoInfo; str := "p" |}]
                    (MInstance {| P4String.tags := NoInfo; str := "MyParser" |}
                       [{| P4String.tags := NoInfo; str := "main" |};
                       {| P4String.tags := NoInfo; str := "p" |}]) PathMap.empty)))))).

Goal init_mem = standard_init_mem.
reflexivity.
Admitted.  *)

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

Instance external : @External Info. Admitted. (*  := Build_External unit. *)

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

Lemma property1: forall ge this decls m m' exts,
    exec_stmt ge this decls myEnv init_mem (m, exts) myStatement (m', exts) SContinue ->
    PathMap.get (name_cons this _var) m = Some (ValBaseBit 8 2) ->
    PathMap.get (name_cons this _var) m' = Some (ValBaseBit 8 3).
Proof.
  intros. inversion H. subst. clear H.
  remember (BareName {| P4String.tags := NoInfo; str := "var" |}) as name.
  replace lv with (MkValueLvalue (ValLeftName name) (TypBit 8)) in *.
  2 : { inversion H12. reflexivity. }
  clear H12.
  replace v with (@ValBaseBit Info 8 3) in *.
  2 : { inversion H13. subst. clear H13.
        replace largv with (@ValBaseBit Info 8 2) in *.
        replace rargv with (@ValBaseBit Info 8 1) in *.
        2 : { inversion H11. subst. clear H11.
              replace oldv with (@ValBaseInteger Info 1) in *.
              2 : { inversion H9. subst. clear H9.
                    unfold eval_p4int. reflexivity. }
              inversion H13. reflexivity. }
        2 : { clear H11. inversion H10. subst. clear H10.
              unfold name_to_val in H8. inversion H8.
              unfold name_cons in H0. rewrite H0 in H1. inversion H1.
              reflexivity. }
        inversion H12. subst. clear H12. reflexivity. }
  clear H13. unfold assign_lvalue in H14. unfold update_val_by_name in H14.
  unfold update_memory in H14. unfold PathMap.set in H14.
  rewrite Heqname in H14.
  inversion H14. subst. clear H14.
  unfold name_cons in *. unfold PathMap.get.
  rewrite path_equivb_reflexivity.
  reflexivity.
Qed.
