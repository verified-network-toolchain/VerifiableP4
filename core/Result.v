Require Import Coq.Lists.List.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Plugin.Hammer.

(* Consider a Prop P. We want to know if P holds but we don't have a decision procedure.
  So we use a tactic to construct a sumbool {P} + {True}, which stands either we prove P
  or we failed to prove P. *)

Definition result (P : Prop) : Type := {P} + {True}.

Inductive res_list {A} (P : A -> Prop) : list A -> Type :=
  | rnil : res_list P nil
  | rcons : forall {a al} (r : result (P a)) (rs : res_list P al),
      res_list P (a :: al).

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

Definition andb {x y : bool} (r1 : result x) (r2 : result y) : result (x && y).
Proof.
  refine (
    match r1, r2 with
    | left r1, left r2 =>
        left _
    | _, _ =>
        right I
    end
  ).
  sauto lq: on.
Defined.

Definition orb {x y : bool} (r1 : result x) (r2 : result y) : result (x || y).
Proof.
  refine (
    match r1, r2 with
    | right _, right _ =>
        right I
    | _, _ => _
    end
  ).
  - sauto lq: on.
  - sauto lq: on.
Defined.

Fixpoint forallb {A} (f : A -> bool) {al : list A} (rl : res_list f al)
    : result (forallb f al).
Proof.
  inversion rl as [ | a al'].
  - left. auto.
  - apply andb; auto.
    apply forallb; auto.
Defined.

End Result.
