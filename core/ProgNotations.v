Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.P4Int.

Declare Scope prog_scope.
Delimit Scope prog_scope with prog.

Notation "x" := (ExpCast _ x) (at level 98, only printing, x at level 99).
Notation "x" := (ExpInt {| tags := _; value := x; width_signed := _ |})
                  (at level 98, only printing, x at level 99).
Notation "x . y" := (ExpExpressionMember x y) (at level 98, only printing, left associativity, x at level 99, y at level 99, format "x . y").
Notation "x" := (BareName x) (only printing, at level 98, x at level 99).
Notation "x" := (ExpName x _) (at level 98, only printing, x at level 99).
Notation "x := y" := (StatAssignment x y) (at level 98, only printing, x at level 99, y at level 99).
Notation "x ()" := (StatMethodCall x _ nil) (at level 98, only printing, x at level 99, format "x ()").
Notation "x ( y )" := (StatMethodCall x _ y) (at level 98, only printing, x at level 99, y at level 99, format "x ( y )").
Notation "'if' '(' cond ')' x 'else' y" := (StatConditional cond x (Some y)) (at level 98, only printing, x at level 99, y at level 99).
Notation "x == y" := (ExpBinaryOp Eq x y) (at level 98, only printing, x at level 99, y at level 99).
Notation "x" := (MkExpression _ x _ _) (at level 98, only printing, x at level 99).
Notation "x" := (MkStatement _ x _) (at level 98, only printing, x at level 99).
Notation "⟦ x ⟧" := (BlockCons x (BlockEmpty _)) (only printing).
Notation "⟦ x ; y ; .. ; z ⟧" :=
  (BlockCons x (BlockCons y .. (BlockCons z (BlockEmpty _)) ..)) (only printing).
