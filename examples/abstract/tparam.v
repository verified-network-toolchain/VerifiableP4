Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition PortId := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId" |} (inl (TypBit 4)).

Definition Checksum16 := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Checksum16" |}
    [{| stags := NoInfo; str := "C" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Checksum16" |}
          [(MkParameter false Directionless
                (TypTypeName (BareName {| stags := NoInfo; str := "C" |}))
                None {| stags := NoInfo; str := "param" |})]);
     (ProtoAbstractMethod NoInfo (TypBit 16)
          {| stags := NoInfo; str := "f" |}
          [{| stags := NoInfo; str := "D" |};
           {| stags := NoInfo; str := "E" |}]
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "C" |}))
                None {| stags := NoInfo; str := "ix" |});
           (MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "D" |}))
                None {| stags := NoInfo; str := "data" |});
           (MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "E" |}))
                None {| stags := NoInfo; str := "data2" |});
           (MkParameter false In
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "PortId" |})) None
                {| stags := NoInfo; str := "p" |})]);
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

Definition bit16 := DeclTypeDef NoInfo {| stags := NoInfo; str := "bit16" |}
    (inl (TypBit 16)).

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false InOut (TypBit 16) None
          {| stags := NoInfo; str := "p" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Checksum16" |}))
               [(TypBit 16)])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 32;
                    width_signed := (Some ( 16, false )) |}) (TypBit 16)
                Directionless)] {| stags := NoInfo; str := "cntr" |}
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
                [{| stags := NoInfo; str := "E" |};
                 {| stags := NoInfo; str := "D" |}]
                [(MkParameter false In
                      (TypTypeName
                       (BareName {| stags := NoInfo; str := "bit16" |})) 
                      None {| stags := NoInfo; str := "ix" |});
                 (MkParameter false In
                      (TypTypeName
                       (BareName {| stags := NoInfo; str := "E" |})) 
                      None {| stags := NoInfo; str := "data" |});
                 (MkParameter false In
                      (TypTypeName
                       (BareName {| stags := NoInfo; str := "D" |})) 
                      None {| stags := NoInfo; str := "data2" |});
                 (MkParameter false In
                      (TypTypeName
                       (BareName {| stags := NoInfo; str := "PortId" |}))
                      None {| stags := NoInfo; str := "p" |})]
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
                                             (TypTypeName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "bit16" |})) In))])
                                 (TypBit 16) Directionless))) StmVoid)
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
                                  (TypSpecializedType
                                       (TypExtern
                                        {| stags := NoInfo;
                                           str := "Checksum16" |})
                                       [(TypBit 16)]) Directionless)
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

Definition prog := Program
    [PortId; Checksum16; State; bit16; c; ctr; top; main].


