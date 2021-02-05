Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.
Require Import p4ast.

Require Import Petr4.Semantics.

Check exec_instantiation.
Print packet_in.

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

Lemma property1: forall env this decls s ,
    exec_stmt env this decls s myStatement s' ->
    env (var) = Instantce ->
    s = 2 ->
    s' = 3.

    