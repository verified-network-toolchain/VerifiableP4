Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf.UseTofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.core.Core.
Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition am_ge := ltac:(get_am_ge prog).
(* Finished transaction in 12.13 secs (11.734u,0.39s) (successful) *)
Definition ge : genv := ltac:(get_ge am_ge prog).

(* TODO: put them somewhere in core. *)
Definition P4Bit (w : N) (v : Z) : Sval :=
  ValBaseBit (P4Arith.to_loptbool w v).

Definition P4NewBit (w : N) : Sval :=
  ValBaseBit (Zrepeat None (Z.of_N w)).

(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Definition num_slots := 262144.
Definition num_rows := 3.

(* NoAction *)

Definition NoAction_fundef : @fundef Info := Eval compute in
  ltac:(get_fd ["NoAction"] ge).

Definition NoAction_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH,
      PRE
        (ARG []
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
        (EXT []))).

Lemma NoAction_body :
  func_sound ge NoAction_fundef nil NoAction_spec.
Proof.
  start_function.
  step.
  entailer.
Qed.
