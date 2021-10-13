Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition Virtual := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Virtual" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Virtual" |} nil);
     (ProtoAbstractMethod NoInfo (TypBit 16)
          {| stags := NoInfo; str := "f" |} nil
          [(MkParameter false In (TypBit 16) None
                {| stags := NoInfo; str := "ix" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "run" |} nil
          [(MkParameter false In (TypBit 16) None
                {| stags := NoInfo; str := "ix" |})])].

Definition State := DeclExternObject NoInfo
    {| stags := NoInfo; str := "State" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "State" |}
          [(MkParameter false Directionless (TypInt 16) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo (TypBit 16) {| stags := NoInfo; str := "get" |} nil
          [(MkParameter false In (TypBit 16) None
                {| stags := NoInfo; str := "index" |})])].

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false InOut (TypBit 16) None
          {| stags := NoInfo; str := "p" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Virtual" |})) nil) nil
          {| stags := NoInfo; str := "cntr" |}
          [(InitInstantiation NoInfo
                (TypSpecializedType
                     (TypTypeName
                      (BareName {| stags := NoInfo; str := "State" |})) nil)
                [(MkExpression NoInfo
                      (ExpCast (TypInt 16)
                           (MkExpression NoInfo
                                (ExpInt
                                 {| itags := NoInfo; value := 1024;
                                    width_signed := None |}) TypInteger
                                Directionless)) (TypInt 16) Directionless)]
                {| stags := NoInfo; str := "state" |} nil);
           (InitFunction NoInfo (TypBit 16) {| stags := NoInfo; str := "f" |}
                nil
                [(MkParameter false In (TypBit 16) None
                      {| stags := NoInfo; str := "ix" |})]
                (BlockCons
                     (MkStatement NoInfo
                          (StatReturn
                           (Some
                            (MkExpression NoInfo
                                 (ExpFunctionCall
                                      (MkExpression NoInfo
                                           (ExpExpressionMember
                                                (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "state" |})
                                                      NoLocator)
                                                     (TypExtern
                                                      {| stags := NoInfo;
                                                         str := "State" |})
                                                     Directionless)
                                                {| stags := NoInfo;
                                                   str := "get" |})
                                           (TypFunction
                                            (MkFunctionType nil
                                                 [(MkParameter false In
                                                       (TypBit 16) None
                                                       {| stags := NoInfo;
                                                          str := "index" |})]
                                                 FunExtern (TypBit 16)))
                                           Directionless) nil
                                      [(Some
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "ix" |}) NoLocator)
                                             (TypBit 16) In))]) (TypBit 16)
                                 Directionless))) StmVoid)
                     (BlockEmpty NoInfo)))])]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "cntr" |})
                                   (LInstance
                                        [{| stags := NoInfo; str := "cntr" |}]))
                                  (TypExtern
                                   {| stags := NoInfo; str := "Virtual" |})
                                  Directionless)
                             {| stags := NoInfo; str := "run" |})
                        (TypFunction
                         (MkFunctionType nil
                              [(MkParameter false In (TypBit 16) None
                                    {| stags := NoInfo; str := "ix" |})]
                              FunExtern TypVoid)) Directionless) nil
                   [(Some
                     (MkExpression NoInfo
                          (ExpCast (TypBit 16)
                               (MkExpression NoInfo
                                    (ExpInt
                                     {| itags := NoInfo; value := 6;
                                        width_signed := None |}) TypInteger
                                    Directionless)) (TypBit 16)
                          Directionless))]) StmUnit) (BlockEmpty NoInfo)).

Definition ctr := DeclControlType NoInfo {| stags := NoInfo; str := "ctr" |}
    nil
    [(MkParameter false InOut (TypBit 16) None
          {| stags := NoInfo; str := "x" |})].

Definition top := DeclPackageType NoInfo {| stags := NoInfo; str := "top" |}
    nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "ctr" |})) 
          None {| stags := NoInfo; str := "ctrl" |})].

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
                [(MkParameter false InOut (TypBit 16) None
                      {| stags := NoInfo; str := "p" |})])) Directionless)]
    {| stags := NoInfo; str := "main" |} nil.

Definition prog := Program [Virtual; State; c; ctr; top; main].


