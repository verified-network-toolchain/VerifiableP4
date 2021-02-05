Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.
Require Import p4ast.

Require Import Petr4.Semantics.

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

Definition myEnv := IdentMap.set IdentMap.empty _var (Instance (BareName _var)).

(* Instance external : External := Build_External unit.
Hint Resolve external : typeclass_instances. *)
Lemma property1: forall ge this decls m m' exts,
    @exec_stmt _ unit ge this decls myEnv (m, exts) myStatement (m', exts) Out_normal ->
    PathMap.get m (name_cons this _var) = Some (MVal (VInt 2)) ->
    PathMap.get m' (name_cons this _var) = Some (MVal (VInt 3)).
