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

Definition standard_init_mem :=
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
Qed.

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

Lemma property1: forall ge this decls m m' exts,
    exec_stmt ge this decls myEnv init_mem (m, exts) myStatement (m', exts) Out_normal ->
    PathMap.get (name_cons this _var) m = Some (ValBaseInteger 2) ->
    PathMap.get (name_cons this _var) m' = Some (ValBaseInteger 3).
Admitted.