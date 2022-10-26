Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.ConFilter.

Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition empty_genv {tags_t: Type} {target: Target} : @genv tags_t target :=
  MkGenv PathMap.empty IdentMap.empty IdentMap.empty
    PathMap.empty PathMap.empty PathMap.empty.
Opaque empty_genv.

Definition force_genv (r: Monads.Result.result Exn.t genv) :=
  match r with
  | Result.Ok x => x
  | Result.Error _ => empty_genv
  end.

Definition am_ge: genv :=
  ltac:(let ge := eval compute -[PathMap.empty PathMap.set] in
        (force_genv (gen_am_ge prog)) in
          exact (ge : (@genv _ ltac:(typeclasses eauto)))).

(* Finished transaction in 4.375 secs (4.218u,0.156s) (successful) *)
Definition ge :=
  ltac:( let ge := eval compute -[am_ge PathMap.empty PathMap.set] in
         (force_genv (gen_ge' am_ge prog)) in
  exact (ge : (@genv _ ltac:(typeclasses eauto)))).


(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Definition index_w := 18%N.
Definition num_slots := Eval compute in 2 ^ (Z.of_N index_w).
Definition num_rows := 3.
Definition num_frames := 4.
Definition frame_tick_tocks := 7034.
Definition tick_time := 2097152.
Definition frame_time := frame_tick_tocks * tick_time * 2.

Definition poly1 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 79764919;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash1 (v : Val) :=
  hash_Z 32 poly1 v mod 2 ^ (Z.of_N index_w).

Definition poly2 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 517762881;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash2 (v : Val) :=
  hash_Z 32 poly2 v mod 2 ^ Z.of_N index_w.


Definition poly3 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 2821953579;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash3 (v : Val) :=
  hash_Z 32 poly3 v mod 2 ^ Z.of_N index_w.

Definition header_type : Set := Z * Z.

Definition header_to_val '((x, y) : header_type) : Val :=
  ValBaseBit ((P4Arith.to_lbool 32 x) ++ (P4Arith.to_lbool 32 y)).

Definition hashes := [hash1 ∘ header_to_val; hash2 ∘ header_to_val; hash3 ∘ header_to_val].

Lemma H_Zlength_hashes : Zlength hashes = num_rows.
Proof. auto. Qed.

Lemma b2z_range : forall b,
  0 <= Z.b2z b < 2.
Proof.
  destruct b; simpl; lia.
Qed.

Ltac add_b2z_range b :=
  assert_fails (assert (0 <= Z.b2z b < 2) by assumption);
  pose proof (b2z_range b).

Ltac saturate_b2z :=
  repeat match goal with
  | H : context [Z.b2z ?b] |- _ =>
      add_b2z_range b
  | |- context [Z.b2z ?b] =>
      add_b2z_range b
  end.

Ltac Zify.zify_pre_hook ::=
  unfold is_true, index_w, num_slots, num_rows, num_frames, frame_tick_tocks,
    NOOP, CLEAR, INSERT, QUERY, INSQUERY in *;
  saturate_b2z.

Definition rows := ["row_1"; "row_2"; "row_3"].
Definition panes := ["win_1"; "win_2"; "win_3"; "win_4"].

Definition H_num_slots : 0 < num_slots := eq_refl.
Definition H_num_rows : 0 < num_rows := eq_refl.
Definition H_num_frames : 1 < num_frames := eq_refl.

Notation row := (row num_slots).
Notation frame := (frame num_rows num_slots).

#[export] Instance Inhabitant_row : Inhabitant row :=
  Inhabitant_row H_num_slots.

#[export] Instance Inhabitant_frame : Inhabitant frame :=
  Inhabitant_frame H_num_rows H_num_slots.

(* NoAction *)

Definition NoAction_fundef : @fundef Info :=
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
