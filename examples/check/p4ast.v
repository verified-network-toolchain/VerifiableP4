Require Import Petr4.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition C := DeclControl NoInfo {| stags := NoInfo; str := "C" |} nil nil
    nil nil (BlockEmpty NoInfo).

Definition Cctrl := DeclControlType NoInfo
    {| stags := NoInfo; str := "Cctrl" |} nil nil.

Definition D := DeclControl NoInfo {| stags := NoInfo; str := "D" |} nil nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "Cctrl" |})) 
          None {| stags := NoInfo; str := "c1" |});
     (MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "Cctrl" |})) 
          None {| stags := NoInfo; str := "c2" |})] nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "c1" |}))
                                  (TypTypeName
                                   (BareName
                                    {| stags := NoInfo; str := "Cctrl" |}))
                                  Directionless)
                             {| stags := NoInfo; str := "apply" |})
                        (TypFunction
                         (MkFunctionType nil nil FunControl TypVoid))
                        Directionless) nil nil) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpExpressionMember
                                  (MkExpression NoInfo
                                       (ExpName
                                        (BareName
                                         {| stags := NoInfo; str := "c2" |}))
                                       (TypTypeName
                                        (BareName
                                         {| stags := NoInfo;
                                            str := "Cctrl" |}))
                                       Directionless)
                                  {| stags := NoInfo; str := "apply" |})
                             (TypFunction
                              (MkFunctionType nil nil FunControl TypVoid))
                             Directionless) nil nil) StmUnit)
              (BlockEmpty NoInfo))).

Definition E := DeclControl NoInfo {| stags := NoInfo; str := "E" |} nil nil
    nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName (BareName {| stags := NoInfo; str := "C" |}))
               nil) nil {| stags := NoInfo; str := "c1" |} None);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName (BareName {| stags := NoInfo; str := "C" |}))
               nil) nil {| stags := NoInfo; str := "c2" |} None);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName (BareName {| stags := NoInfo; str := "D" |}))
               nil)
          [(MkExpression NoInfo
                (ExpName (BareName {| stags := NoInfo; str := "c1" |}))
                (TypControl (MkControlType nil nil)) Directionless);
           (MkExpression NoInfo
                (ExpName (BareName {| stags := NoInfo; str := "c2" |}))
                (TypControl (MkControlType nil nil)) Directionless)]
          {| stags := NoInfo; str := "d" |} None)]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "d" |}))
                                  (TypControl (MkControlType nil nil))
                                  Directionless)
                             {| stags := NoInfo; str := "apply" |})
                        (TypFunction
                         (MkFunctionType nil nil FunControl TypVoid))
                        Directionless) nil nil) StmUnit) (BlockEmpty NoInfo)).

Definition Ectrl := DeclControlType NoInfo
    {| stags := NoInfo; str := "Ectrl" |} nil nil.

Definition top := DeclPackageType NoInfo {| stags := NoInfo; str := "top" |}
    nil
    [(MkParameter false Directionless
          (TypTypeName (BareName {| stags := NoInfo; str := "Ectrl" |})) 
          None {| stags := NoInfo; str := "_e" |})].

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName (BareName {| stags := NoInfo; str := "top" |})) nil)
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     (BareName {| stags := NoInfo; str := "E" |})) nil) nil)
          (TypControl (MkControlType nil nil)) Directionless)]
    {| stags := NoInfo; str := "main" |} None.

Definition prog := Program [C; Cctrl; D; E; Ectrl; top; main].

