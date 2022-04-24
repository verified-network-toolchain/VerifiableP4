Require Import Coq.Lists.List.
Require Import Hammer.Plugin.Hammer.

(* Consider a Prop P. We want to know if P holds but we don't have a decision procedure.
  So we use a tactic to construct a sumbool {P} + {True}, which stands either we prove P
  or we failed to prove P. *)

Definition result (P : Prop) : Type := {P} + {True}.

Module Result.

Definition and {P Q} (r1 : result P) (r2 : result Q) : result (P /\ Q) :=
  match r1, r2 with
  | left r1, left r2 =>
      left (conj r1 r2)
  | _, _ =>
      right I
  end.

Definition or {P Q} (r1 : result P) (r2 : result Q) : result (P \/ Q) :=
  match r1, r2 with
  | left r1, _ =>
      left (or_introl r1)
  | _, left r2 =>
      left (or_intror r2)
  | _, _ =>
      right I
  end.

End Result.
