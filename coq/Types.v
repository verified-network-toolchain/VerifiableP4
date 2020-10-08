Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.

Open Scope type_scope.

Definition info (A : Type) := Info * A.

Definition P4Int := info (Z * option (Z * bool)).

Definition P4String := info string.

Inductive name :=
  | BareName : P4String -> name
  | QualifiedName : list P4String -> P4String -> name.
