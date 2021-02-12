Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition max'left'right := DeclFunction NoInfo (TypBit 16)
    {| stags := NoInfo; str := "max" |} nil
    [(MkParameter false In (TypBit 16) None
          {| stags := NoInfo; str := "left" |});
     (MkParameter false In (TypBit 16) None
          {| stags := NoInfo; str := "right" |})]
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpBinaryOp Gt
                             ( (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "left" |}))
                                    (TypBit 16) In),
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "right" |}))
                                    (TypBit 16) In) )) TypBool In)
                   (MkStatement NoInfo
                        (StatReturn
                         (Some
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo; str := "left" |}))
                               (TypBit 16) In))) StmVoid) None) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatReturn
                    (Some
                     (MkExpression NoInfo
                          (ExpName
                           (BareName {| stags := NoInfo; str := "right" |}))
                          (TypBit 16) In))) StmVoid) (BlockEmpty NoInfo))).

Definition max'left := DeclFunction NoInfo (TypBit 16)
    {| stags := NoInfo; str := "max" |} nil
    [(MkParameter false In (TypBit 16) None
          {| stags := NoInfo; str := "left" |})]
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpBinaryOp Gt
                             ( (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "left" |}))
                                    (TypBit 16) In),
                               (MkExpression NoInfo
                                    (ExpCast (TypBit 16)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 256;
                                                  width_signed := None |})
                                              TypInteger Directionless))
                                    (TypBit 16) Directionless) )) TypBool
                        Directionless)
                   (MkStatement NoInfo
                        (StatReturn
                         (Some
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo; str := "left" |}))
                               (TypBit 16) In))) StmVoid) None) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatReturn
                    (Some
                     (MkExpression NoInfo
                          (ExpCast (TypBit 16)
                               (MkExpression NoInfo
                                    (ExpInt
                                     {| itags := NoInfo; value := 256;
                                        width_signed := None |}) TypInteger
                                    Directionless)) (TypBit 16)
                          Directionless))) StmVoid) (BlockEmpty NoInfo))).

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false Out (TypBit 16) None
          {| stags := NoInfo; str := "b" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatAssignment
                   (MkExpression NoInfo
                        (ExpName
                         (BareName {| stags := NoInfo; str := "b" |}))
                        (TypBit 16) Out)
                   (MkExpression NoInfo
                        (ExpFunctionCall
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "max" |}))
                                  (TypFunction
                                   (MkFunctionType nil
                                        [(MkParameter false In (TypBit 16)
                                              None
                                              {| stags := NoInfo;
                                                 str := "left" |});
                                         (MkParameter false In (TypBit 16)
                                              None
                                              {| stags := NoInfo;
                                                 str := "right" |})]
                                        FunFunction (TypBit 16)))
                                  Directionless) nil
                             [(Some
                               (MkExpression NoInfo
                                    (ExpCast (TypBit 16)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 10;
                                                  width_signed := None |})
                                              TypInteger Directionless))
                                    (TypBit 16) Directionless));
                              (Some
                               (MkExpression NoInfo
                                    (ExpCast (TypBit 16)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 12;
                                                  width_signed := None |})
                                              TypInteger Directionless))
                                    (TypBit 16) Directionless))]) (TypBit 16)
                        Directionless)) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatAssignment
                        (MkExpression NoInfo
                             (ExpName
                              (BareName {| stags := NoInfo; str := "b" |}))
                             (TypBit 16) Out)
                        (MkExpression NoInfo
                             (ExpFunctionCall
                                  (MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo; str := "max" |}))
                                       (TypFunction
                                        (MkFunctionType nil
                                             [(MkParameter false In
                                                   (TypBit 16) None
                                                   {| stags := NoInfo;
                                                      str := "left" |})]
                                             FunFunction (TypBit 16)))
                                       Directionless) nil
                                  [(Some
                                    (MkExpression NoInfo
                                         (ExpCast (TypBit 16)
                                              (MkExpression NoInfo
                                                   (ExpInt
                                                    {| itags := NoInfo;
                                                       value := 10;
                                                       width_signed := 
                                                       None |}) TypInteger
                                                   Directionless))
                                         (TypBit 16) Directionless))])
                             (TypBit 16) Directionless)) StmUnit)
              (BlockEmpty NoInfo))).

Definition ctr := DeclControlType NoInfo {| stags := NoInfo; str := "ctr" |}
    nil
    [(MkParameter false Out (TypBit 16) None
          {| stags := NoInfo; str := "b" |})].

Definition top := DeclPackageType NoInfo {| stags := NoInfo; str := "top" |}
    nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "ctr" |})) 
          None {| stags := NoInfo; str := "_c" |})].

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName (BareName {| stags := NoInfo; str := "top" |})) nil)
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "c" |})) nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Out (TypBit 16) None
                      {| stags := NoInfo; str := "b" |})])) Directionless)]
    {| stags := NoInfo; str := "main" |} None.

Definition prog := Program [max'left'right; max'left; c; ctr; top; main].


