Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Inductive Info : Type :=
  (* I filename line_start line_end col_start col_end *)
  | I : string -> Z -> option Z -> Z -> Z -> Info
  (* M msg *)
  | M : string -> Info.