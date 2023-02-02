Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.p4ast.
Require Import ProD3.examples.cms.ConModel.

Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition am_ge := ltac:(get_am_ge prog).
Definition ge := ltac:(get_ge am_ge prog).

(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Definition index_w := 15%N.
Definition value_w := 32%N.
Definition num_slots := Eval compute in 2 ^ (Z.of_N index_w).
Definition num_rows := 5.
Definition num_frames := 3.
Definition frame_tick_tocks := 7034.
Definition tick_time := 4194304.
Definition frame_time := frame_tick_tocks * tick_time * 2.

Definition poly1 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 16;
    Tofino.CRCP_coeff := P4Arith.to_lbool 16 32773;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 16 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 16 0
  |}.

Definition hash1 (v : Val) :=
  hash_Z 16 poly1 v mod 2 ^ (Z.of_N index_w).

Definition poly2 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 16;
    Tofino.CRCP_coeff := P4Arith.to_lbool 16 4129;
    Tofino.CRCP_reversed := false;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 16 65535;
    Tofino.CRCP_xor := P4Arith.to_lbool 16 0
  |}.

Definition hash2 (v : Val) :=
  hash_Z 16 poly2 v mod 2 ^ Z.of_N index_w.


Definition poly3 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 16;
    Tofino.CRCP_coeff := P4Arith.to_lbool 16 1417;
    Tofino.CRCP_reversed := false;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 16 1;
    Tofino.CRCP_xor := P4Arith.to_lbool 16 1
  |}.

Definition hash3 (v : Val) :=
  hash_Z 16 poly3 v mod 2 ^ Z.of_N index_w.

Definition poly4 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 16;
    Tofino.CRCP_coeff := P4Arith.to_lbool 16 15717;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 16 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 16 65535
  |}.

Definition hash4 (v : Val) :=
  hash_Z 16 poly4 v mod 2 ^ Z.of_N index_w.

Definition poly5 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 16;
    Tofino.CRCP_coeff := P4Arith.to_lbool 16 35767;
    Tofino.CRCP_reversed := false;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 16 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 16 0
  |}.

Definition hash5 (v : Val) :=
  hash_Z 16 poly5 v mod 2 ^ Z.of_N index_w.

Definition header_type : Set := Z * Z.

Definition header_to_val '((x, y) : header_type) : Val :=
  ValBaseBit ((P4Arith.to_lbool 32 y) ++ (P4Arith.to_lbool 32 x)).

Definition hashes := [hash1 ∘ header_to_val; hash2 ∘ header_to_val; hash3 ∘ header_to_val; hash4 ∘ header_to_val; hash5 ∘ header_to_val].

Lemma H_Zlength_hashes : Zlength hashes = num_rows.
Proof. auto. Qed.

Lemma mod_bound_small : forall w n,
  0 <= n < 2 ^ (Z.of_N w) ->
  P4Arith.BitArith.mod_bound w n = n.
Proof.
  intros.
  apply Z.mod_small; auto.
Qed.

Lemma sat_bound_spec : forall w n,
  P4Arith.BitArith.sat_bound w n
    = Z.min (Z.max n 0) (2 ^ (Z.of_N w) - 1).
Proof.
  intros.
  unfold P4Arith.BitArith.sat_bound, P4Arith.BitArith.maxZ, P4Arith.BitArith.upper_bound.
  destruct (n >? 2 ^ Z.of_N w - 1) eqn:?;
  only 2 : destruct (n <? 0) eqn:?;
  lia.
Qed.

Lemma Zmin_shrink : forall a b c,
  Z.min (Z.min a c) (Z.min b c)
    = Z.min (Z.min a b) c.
Proof.
  lia.
Qed.

Ltac Zify.zify_pre_hook ::=
  unfold is_true, index_w, num_slots, num_rows, num_frames, frame_tick_tocks,
    NOOP, CLEAR, INSERT, QUERY, INSQUERY in *.

Lemma ext_implies_trans : forall a1 a2 a3,
  ext_implies a1 a2 ->
  ext_implies a2 a3 ->
  ext_implies a1 a3.
Proof.
  unfold ext_implies; intros.
  auto.
Qed.

Definition rows := ["row_1"; "row_2"; "row_3"; "row_4"; "row_5"].
Definition panes := ["win_1"; "win_2"; "win_3"].

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
