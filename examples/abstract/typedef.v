Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition PortId := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId" |} (inl (TypBit 4)).

Definition Checksum16 := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Checksum16" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Checksum16" |} nil);
     (ProtoMethod NoInfo (TypBit 16) {| stags := NoInfo; str := "f" |} nil
          [(MkParameter false In
                (TypTypeName
                 (BareName {| stags := NoInfo; str := "PortId" |})) None
                {| stags := NoInfo; str := "p" |})])].

Definition PortId := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId" |} (inl (TypBit 8)).

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false InOut (TypBit 16) None
          {| stags := NoInfo; str := "p" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Checksum16" |})) nil)
          nil {| stags := NoInfo; str := "cs" |} nil)]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "cs" |})
                                   (LInstance
                                        [{| stags := NoInfo; str := "cs" |}]))
                                  (TypExtern
                                   {| stags := NoInfo; str := "Checksum16" |})
                                  Directionless)
                             {| stags := NoInfo; str := "f" |})
                        (TypFunction
                         (MkFunctionType nil
                              [(MkParameter false In
                                    (TypTypeName
                                     (BareName
                                      {| stags := NoInfo; str := "PortId" |}))
                                    None {| stags := NoInfo; str := "p" |})]
                              FunExtern (TypBit 16))) Directionless) nil
                   [(Some
                     (MkExpression NoInfo
                          (ExpInt
                           {| itags := NoInfo; value := 10;
                              width_signed := (Some ( 8, false )) |})
                          (TypBit 8) Directionless))]) StmUnit)
         (BlockEmpty NoInfo)).

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

Definition prog := Program [PortId; Checksum16; PortId; c; ctr; top; main].


