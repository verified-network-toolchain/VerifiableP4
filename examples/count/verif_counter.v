Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.count.common.
Require Import ProD3.examples.count.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"].

Open Scope func_spec.

Definition regact_counter_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_counter"])).

Definition regact_counter_execute_body :=
  ltac:(build_execute_body ge regact_counter_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_counter_execute_body) : func_specs.

Definition counter_act_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_counter"] ge).

Definition counter_act_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) [p]
    WITH (counter : Z),
      PRE
        (ARG []
        (MEM []
        (EXT [counter_repr p counter])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"; "num_pkt"], P4Bit 32 (counter + 1))]
           (EXT [counter_repr p (counter + 1)]))).

Lemma counter_act_body:
  func_sound ge counter_act_fundef nil counter_act_spec.
Proof.
  start_function.
  unfold counter_repr, counter_reg_repr.
  normalize_EXT.
  Intros_prop. simpl.
  (* step_call regact_counter_execute_body. *)
Abort.
