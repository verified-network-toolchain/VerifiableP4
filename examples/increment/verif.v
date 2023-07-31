Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.V1ModelTarget.
Require Import ProD3.core.Core.
Require Import ProD3.core.V1ModelSpec.
Require Import ProD3.examples.increment.p4ast.

#[local] Instance target : @Target Info (@Expression Info) := V1Model.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Opaque PathMap.empty PathMap.set.

(* Global environment *)
Definition ge : genv := ltac:(
  let ge := eval compute in (gen_ge prog) in
  lazymatch ge with
  | Result.Ok ?ge =>
      exact (ge : (@genv _ ltac:(typeclasses eauto)))
  | Result.Error ?msg =>
      fail 0 "Global environment evaluation failed with message:" msg
  end).

(* Initial extern state *)
Definition instantiation := ltac:(
  let instantiation := eval compute in (instantiate_prog ge (ge_typ ge) prog) in
  lazymatch instantiation with
  | Result.Ok ?instantiation =>
      exact instantiation
  | Result.Error ?msg =>
      fail 0 "Global environment evaluation failed with message:" msg
  end).

Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Definition custom_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "custom_metadata_t" (ge_typ ge)).

Definition standard_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "standard_metadata_t" (ge_typ ge)). *)

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.

Open Scope func_spec.

Definition Increment_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Increment"; "apply"] (ge_func ge)).

Definition p := ["main"; "ig"; "incr"].

Definition Increment_spec : func_spec :=
  WITH,
    PATH p
    MOD None [p]
    WITH (x : Z),
      PRE
        (ARG []
        (MEM []
        (EXT [ExtPred.singleton (p ++ ["reg"]) (ObjRegister [ValBaseBit (P4Arith.to_lbool 8 x)])])))
      POST
        (ARG_RET [P4Bit 8 (x + 1)] ValBaseNull
        (MEM []
        (EXT [ExtPred.singleton (p ++ ["reg"]) (ObjRegister [ValBaseBit (P4Arith.to_lbool 8 (x + 1))])]))).


(* Lemma eval_val_to_sval_P4Bit : forall w v,
  eval_val_to_sval (ValBaseBit (P4Arith.to_lbool w v)) = P4Bit w v.
Proof.
  reflexivity.
Qed.

Hint Rewrite eval_val_to_sval_P4Bit : abs_ops. *)

Lemma sval_refine_eval_val_to_sval_P4Bit : forall w v,
  sval_refine
    (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool w v)))
    (P4Bit w v).
Proof.
  intros.
  apply sval_refine_refl.
Qed.

(* Unify term with pattern and return pattern with placeholders filled. *)
(* I want to add error message to this tactic. But because it needs to return
  the unification result, it is hard to add any try-catch to it. *)
Ltac unify_to term pattern :=
  let eq_proof := constr:(eq_refl : term = pattern) in
  match type of eq_proof with
  | _ = ?result => result
  end.

Ltac change_P4Bit x :=
  let y := unify_to x uconstr:(P4Bit _ _) in
  change x with y.

Ltac change_P4Int x :=
  let y := unify_to x uconstr:(P4Int _ _) in
  change x with y.

Ltac change_P4Bit_B4Int x :=
  first [
    change_P4Bit x
  | change_P4Int x
  ].

Ltac prepare_abs_ops_rewrite :=
  (* There will be some backtracking if some of change_P4Bit_B4Int fail.
    This is a potential performance issue. *)
  repeat match goal with
  | |- context [abs_plus ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end;
  repeat match goal with
  | |- context [abs_minus ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end;
  repeat match goal with
  | |- context [abs_mul ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end;
  repeat match goal with
  | |- context [abs_eq ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end;
  repeat match goal with
  | |- context [abs_neq ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end;
  repeat match goal with
  | |- context [abs_plus_sat ?x ?y] =>
      change_P4Bit_B4Int x;
      change_P4Bit_B4Int y
  end.

Ltac simpl_abs_ops ::=
  prepare_abs_ops_rewrite; autorewrite with abs_ops.

Ltac sval_refine ::=
  try apply sval_refine_refl;
  try apply sval_refine_eval_val_to_sval_P4Bit.

Lemma Increment_body :
  func_sound ge Increment_fundef [] Increment_spec.
Proof.
  start_function.
  step.
  step_call register_read_body.
  { entailer. }
  { reflexivity. }
  { simpl. lia. }
  { simpl. lia. }
  step.
  step_call register_write_body.
  { entailer. }
  { reflexivity. }
  { simpl. lia. }
  { simpl. lia. }
  step.
  entailer.
Qed.
