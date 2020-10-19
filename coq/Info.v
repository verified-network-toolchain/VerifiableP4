Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Inductive Info : Type :=
  (* I : filename -> line_start -> line_end -> col_start -> col_end -> Info *)
  | I : string -> Z -> option Z -> Z -> Z -> Info
  (* M : msg -> Info *)
  | M : string -> Info.