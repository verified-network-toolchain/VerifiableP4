Require Import Poulet4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition Register := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Register" |}
    [{| stags := NoInfo; str := "T" |}; {| stags := NoInfo; str := "I" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Register" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName (BareName {| stags := NoInfo; str := "T" |}))
                None {| stags := NoInfo; str := "initial_value" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Register" |}
          [(MkParameter false Directionless (TypBit 32) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "write" |} nil
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "I" |}))
                None {| stags := NoInfo; str := "index" |});
           (MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "T" |}))
                None {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo
          (TypTypeName (BareName {| stags := NoInfo; str := "T" |}))
          {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "I" |}))
                None {| stags := NoInfo; str := "index" |})])].

Definition RegisterAction := DeclExternObject NoInfo
    {| stags := NoInfo; str := "RegisterAction" |}
    [{| stags := NoInfo; str := "T0" |}; {| stags := NoInfo; str := "I1" |};
     {| stags := NoInfo; str := "U" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "RegisterAction" |}
          [(MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName
                      (BareName {| stags := NoInfo; str := "Register" |}))
                     [(TypTypeName
                       (BareName {| stags := NoInfo; str := "T0" |}));
                      (TypTypeName
                       (BareName {| stags := NoInfo; str := "I1" |}))]) 
                None {| stags := NoInfo; str := "reg" |})]);
     (ProtoMethod NoInfo
          (TypTypeName (BareName {| stags := NoInfo; str := "U" |}))
          {| stags := NoInfo; str := "predicate" |} nil
          [(MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmplo" |});
           (MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmphi" |})]);
     (ProtoAbstractMethod NoInfo TypVoid
          {| stags := NoInfo; str := "apply" |} nil
          [(MkParameter false InOut
                (TypTypeName (BareName {| stags := NoInfo; str := "T0" |}))
                None {| stags := NoInfo; str := "value" |});
           (MkParameter true Out
                (TypTypeName (BareName {| stags := NoInfo; str := "U" |}))
                None {| stags := NoInfo; str := "rv" |})]);
     (ProtoMethod NoInfo
          (TypTypeName (BareName {| stags := NoInfo; str := "U" |}))
          {| stags := NoInfo; str := "execute_log" |} nil nil);
     (ProtoMethod NoInfo
          (TypTypeName (BareName {| stags := NoInfo; str := "U" |}))
          {| stags := NoInfo; str := "execute" |} nil
          [(MkParameter false In
                (TypTypeName (BareName {| stags := NoInfo; str := "I1" |}))
                None {| stags := NoInfo; str := "index" |})])].

Definition c := DeclControl NoInfo {| stags := NoInfo; str := "c" |} nil
    [(MkParameter false InOut (TypBit 16) None
          {| stags := NoInfo; str := "index" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "Register" |}))
               [(TypBit 32); (TypBit 16)])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 65536;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32)
                Directionless);
           (MkExpression NoInfo
                (ExpCast (TypBit 32)
                     (MkExpression NoInfo
                          (ExpInt
                           {| itags := NoInfo; value := 0;
                              width_signed := None |}) TypInteger
                          Directionless)) (TypBit 32) Directionless)]
          {| stags := NoInfo; str := "reg" |} nil);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                (BareName {| stags := NoInfo; str := "RegisterAction" |}))
               [(TypBit 32); (TypBit 16); (TypBit 32)])
          [(MkExpression NoInfo
                (ExpName (BareName {| stags := NoInfo; str := "reg" |})
                 NoLocator)
                (TypSpecializedType
                     (TypExtern {| stags := NoInfo; str := "Register" |})
                     [(TypBit 32); (TypBit 16)]) Directionless)]
          {| stags := NoInfo; str := "regact" |}
          [(DeclFunction NoInfo TypVoid {| stags := NoInfo; str := "apply" |}
                nil
                [(MkParameter false InOut (TypBit 32) None
                      {| stags := NoInfo; str := "value" |});
                 (MkParameter false Out (TypBit 32) None
                      {| stags := NoInfo; str := "rv" |})]
                (BlockCons
                     (MkStatement NoInfo
                          (StatAssignment
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "rv" |})
                                     (LInstance
                                          [{| stags := NoInfo;
                                              str := "apply" |};
                                           {| stags := NoInfo; str := "rv" |}]))
                                    (TypBit 32) Out)
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "value" |})
                                     (LInstance
                                          [{| stags := NoInfo;
                                              str := "apply" |};
                                           {| stags := NoInfo;
                                              str := "value" |}]))
                                    (TypBit 32) InOut)) StmUnit)
                     (BlockCons
                          (MkStatement NoInfo
                               (StatAssignment
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "value" |})
                                          (LInstance
                                               [{| stags := NoInfo;
                                                   str := "apply" |};
                                                {| stags := NoInfo;
                                                   str := "value" |}]))
                                         (TypBit 32) InOut)
                                    (MkExpression NoInfo
                                         (ExpBinaryOp Plus
                                              ( (MkExpression NoInfo
                                                     (ExpName
                                                      (BareName
                                                       {| stags := NoInfo;
                                                          str := "value" |})
                                                      (LInstance
                                                           [{| stags := NoInfo;
                                                               str := "apply" |};
                                                            {| stags := NoInfo;
                                                               str := "value" |}]))
                                                     (TypBit 32) InOut),
                                                (MkExpression NoInfo
                                                     (ExpCast (TypBit 32)
                                                          (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 1;
                                                                   width_signed := 
                                                                   None |})
                                                               TypInteger
                                                               Directionless))
                                                     (TypBit 32)
                                                     Directionless) ))
                                         (TypBit 32) Directionless)) StmUnit)
                          (BlockEmpty NoInfo))))])]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "regact" |})
                                   (LInstance
                                        [{| stags := NoInfo;
                                            str := "regact" |}]))
                                  (TypSpecializedType
                                       (TypExtern
                                        {| stags := NoInfo;
                                           str := "RegisterAction" |})
                                       [(TypBit 32); (TypBit 16);
                                        (TypBit 32)]) Directionless)
                             {| stags := NoInfo; str := "execute" |})
                        (TypFunction
                         (MkFunctionType nil
                              [(MkParameter false In (TypBit 16) None
                                    {| stags := NoInfo; str := "index" |})]
                              FunExtern (TypBit 32))) Directionless) nil
                   [(Some
                     (MkExpression NoInfo
                          (ExpName
                           (BareName {| stags := NoInfo; str := "index" |})
                           (LInstance
                                [{| stags := NoInfo; str := "index" |}]))
                          (TypBit 16) InOut))]) StmUnit) (BlockEmpty NoInfo)).

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
                      {| stags := NoInfo; str := "index" |})]))
          Directionless)] {| stags := NoInfo; str := "main" |} nil.

Definition prog := Program [Register; RegisterAction; c; ctr; top; main].


