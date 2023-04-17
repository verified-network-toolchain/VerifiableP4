Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.

Require Import ProD3.examples.cms.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "cm2_ds"; "win_1"; "row_5"].

Open Scope func_spec.

Definition Row_regact_insert_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_insert"])).

(* I would like to make it opaque, but I don't know how to. *)
Definition Row_regact_insert_execute_body :=
  ltac:(build_execute_body ge Row_regact_insert_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.

Definition Row_insert_fundef :=
  ltac:(get_fd ["Cm2CountMinSketchRow"; "act_insert"] ge).

(* Program:
  action act_insert() {
      rw = regact_insert.execute(index);
  }
*)

Definition Row_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit value_w (Z.min (Znth i (`r) + 1) (2 ^ 32 - 1)))]
        (EXT [row_repr p (row_insert r i)]))).

Lemma Row_insert_body :
  func_sound ge Row_insert_fundef nil Row_insert_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig row_insert].
  normalize_EXT.
  Intros_prop.
  step_call Row_regact_insert_execute_body.
  { entailer. }
  { list_solve. }
  { lia. }
  { rewrite Znth_map by list_solve.
    reflexivity.
  }
  step.
  replace (P4Arith.BitArith.sat_bound 32
            (P4Arith.BitArith.mod_bound 32
               (Z.min (Znth i r) (2 ^ 32 - 1)) +
             P4Arith.BitArith.mod_bound 32 1))
    with
    (Z.min (Znth i r + 1) (2 ^ 32 - 1)).
  2 : {
    repeat rewrite mod_bound_small by list_solve.
    rewrite sat_bound_spec.
    list_solve.
  }
  entailer.
  { f_equal.
    list_solve.
  }
  { apply ext_implies_prop_intro.
    list_solve.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_insert_body) : func_specs.

Definition Row_regact_query_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_query"])).

Definition Row_regact_query_execute_body :=
  ltac:(build_execute_body ge Row_regact_query_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_query_execute_body) : func_specs.

Definition Row_query_fundef := Eval compute in
  ltac:(get_fd ["Cm2CountMinSketchRow"; "act_query"] ge).

(* Program:
  action act_query() {
      rw = regact_query.execute(index);
  }
*)

Definition Row_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit value_w (Z.min (row_query r i) (2 ^ 32 - 1)))]
        (EXT [row_repr p r]))).

Lemma Row_query_body :
  func_sound ge Row_query_fundef nil Row_query_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig].
  normalize_EXT.
  step_call Row_regact_query_execute_body.
  { entailer. }
  { list_solve. }
  { lia. }
  { rewrite Znth_map by list_solve.
    reflexivity.
  }
  step.
  entailer.
  { f_equal.
    list_simplify. subst. auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_query_body) : func_specs.

Definition Row_regact_clear_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_clear"])).

Definition Row_regact_clear_execute_body :=
  ltac:(build_execute_body ge Row_regact_clear_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_clear_execute_body) : func_specs.

Definition Row_clear_fundef :=
  ltac:(get_fd ["Cm2CountMinSketchRow"; "act_clear"] ge).

(* Program:
  action act_clear() {
      rw = regact_clear.execute(index);
  }
*)

Definition Row_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit value_w 0)]
        (EXT [row_repr p (row_clear r i)]))).

Lemma Row_clear_body :
  func_sound ge Row_clear_fundef nil Row_clear_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig row_clear].
  normalize_EXT.
  step_call Row_regact_clear_execute_body.
  { entailer. }
  { list_solve. }
  { lia. }
  { rewrite Znth_map by list_solve.
    reflexivity.
  }
  step.
  entailer.
  { f_equal.
    list_solve.
  }
  { Intros_prop.
    apply ext_implies_prop_intro.
    list_solve.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_clear_body) : func_specs.

Definition Row_tbl_bloom_fundef :=
  ltac:(get_fd ["Cm2CountMinSketchRow"; "tbl_cms"; "apply"] ge).

Definition Row_fundef :=
  ltac:(get_fd ["Cm2CountMinSketchRow"; "apply"] ge).

Definition Row_noop_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG [P4Bit 8 NOOP;
              P4Bit index_w i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit_ value_w] ValBaseNull
        (MEM []
        (EXT [row_repr p r]))).

Definition Row_tbl_bloom_noop_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 NOOP);
              (["rw"], P4Bit_ value_w)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit_ value_w)]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_noop_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_noop_spec.
Proof.
  start_function; elim_trivial_cases; try lia.
  table_action (@NoAction_body Info).
  { entailer. }
  { entailer. }
Qed.

Lemma Row_noop_case_body :
  func_sound ge Row_fundef nil Row_noop_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_noop_body.
  { entailer. }
  Intros _.
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_noop_case_body) : func_specs.

Definition Row_insert_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG [P4Bit 8 INSERT;
              P4Bit index_w i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit 32 (Z.min (Znth i (`r) + 1) (2 ^ 32 - 1))] ValBaseNull
        (MEM []
        (EXT [row_repr p (row_insert r i)]))).

Definition Row_tbl_bloom_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 INSERT);
              (["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit value_w (Z.min (Znth i (`r) + 1) (2 ^ 32 - 1)))]
        (EXT [row_repr p (row_insert r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_insert_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_insert_spec.
Proof.
  start_function; elim_trivial_cases; try lia.
  table_action Row_insert_body.
  { entailer. }
  { auto. }
  { entailer. }
Qed.

Lemma Row_insert_case_body :
  func_sound ge Row_fundef nil Row_insert_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_insert_body.
  { entailer. }
  { auto. }
  Intros _.
  step.
  entailer.
Qed.

Definition Row_query_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG [P4Bit 8 QUERY;
              P4Bit index_w i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit 32 (Z.min (row_query r i) (2 ^ 32 - 1))] ValBaseNull
        (MEM []
        (EXT [row_repr p r]))).

Definition Row_tbl_bloom_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 QUERY);
              (["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit 32 (Z.min (row_query r i) (2 ^ 32 - 1)))]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_query_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_query_spec.
Proof.
  start_function; elim_trivial_cases; try lia.
  table_action Row_query_body.
  { entailer. }
  { auto. }
  { entailer. }
Qed.

Lemma Row_query_case_body :
  func_sound ge Row_fundef nil Row_query_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_query_body.
  { entailer. }
  { auto. }
  Intros _.
  step.
  entailer.
Qed.

Definition Row_clear_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG [P4Bit 8 CLEAR;
              P4Bit index_w i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit value_w 0] ValBaseNull
        (MEM []
        (EXT [row_repr p (row_clear r i)]))).

Definition Row_tbl_bloom_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 CLEAR);
              (["index"], P4Bit index_w i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit value_w 0)]
        (EXT [row_repr p (row_clear r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_clear_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_clear_spec.
Proof.
  start_function; elim_trivial_cases; try lia.
  table_action Row_clear_body.
  { entailer. }
  { auto. }
  { entailer. }
Qed.

Lemma Row_clear_case_body :
  func_sound ge Row_fundef nil Row_clear_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_clear_body.
  { entailer. }
  { auto. }
  Intros _.
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_noop_case_body) : func_specs.
