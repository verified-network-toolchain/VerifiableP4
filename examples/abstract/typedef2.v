Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition PortId := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId" |} (inl (TypBit 8)).

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false InOut
          (TypTypeName (BareName {| stags := NoInfo; str := "PortId" |}))
          None {| stags := NoInfo; str := "p" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatAssignment
                   (MkExpression NoInfo
                        (ExpName (BareName {| stags := NoInfo; str := "p" |})
                         (LInstance [{| stags := NoInfo; str := "p" |}]))
                        (TypTypeName
                         (BareName {| stags := NoInfo; str := "PortId" |}))
                        InOut)
                   (MkExpression NoInfo
                        (ExpBinaryOp Plus
                             ( (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "p" |})
                                     (LInstance
                                          [{| stags := NoInfo; str := "p" |}]))
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo; str := "PortId" |}))
                                    InOut),
                               (MkExpression NoInfo
                                    (ExpCast (TypBit 8)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 1;
                                                  width_signed := None |})
                                              TypInteger Directionless))
                                    (TypBit 8) Directionless) )) (TypBit 8)
                        Directionless)) StmUnit) (BlockEmpty NoInfo)).

Definition PortId := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId" |} (inl (TypBit 4)).

Definition d := DeclControl NoInfo {| stags := NoInfo; str := "d" |} nil nil
    nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatInstantiation
                   (TypSpecializedType
                        (TypTypeName
                         (BareName {| stags := NoInfo; str := "c" |})) nil)
                   nil {| stags := NoInfo; str := "ci" |} nil) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatVariable (TypBit 4) {| stags := NoInfo; str := "x" |}
                        (Some
                         (MkExpression NoInfo
                              (ExpCast (TypBit 4)
                                   (MkExpression NoInfo
                                        (ExpInt
                                         {| itags := NoInfo; value := 4;
                                            width_signed := None |})
                                        TypInteger Directionless)) (TypBit 4)
                              Directionless))
                        (LInstance [{| stags := NoInfo; str := "x" |}]))
                   StmUnit)
              (BlockCons
                   (MkStatement NoInfo
                        (StatMethodCall
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpName
                                             (BareName
                                              {| stags := NoInfo;
                                                 str := "ci" |}) NoLocator)
                                            (TypControl
                                             (MkControlType nil
                                                  [(MkParameter false InOut
                                                        (TypBit 4) None
                                                        {| stags := NoInfo;
                                                           str := "p" |})]))
                                            Directionless)
                                       {| stags := NoInfo; str := "apply" |})
                                  (TypFunction
                                   (MkFunctionType nil
                                        [(MkParameter false InOut (TypBit 4)
                                              None
                                              {| stags := NoInfo;
                                                 str := "p" |})] FunControl
                                        TypVoid)) Directionless) nil
                             [(Some
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "x" |})
                                     (LInstance
                                          [{| stags := NoInfo; str := "x" |}]))
                                    (TypBit 4) InOut))]) StmUnit)
                   (BlockEmpty NoInfo)))).

Definition prog := Program [PortId; c; PortId; d].


