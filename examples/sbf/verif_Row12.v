Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.TofinoSpec.
Require Import ProD3.examples.sbf.UseTofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_2"].

Open Scope func_spec.

Definition Row_regact_insert_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_insert"; "apply"])).

Definition Row_regact_insert_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_insert"]) 8 (fun _ => 1)
    (fun _ => P4Bit 8 1).

Lemma Row_regact_insert_apply_body :
  func_sound am_ge Row_regact_insert_apply_fd nil Row_regact_insert_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
Qed.

(* I would like to make it opaque, but I don't know how to. *)
Definition Row_regact_insert_execute_body :=
  ltac:(build_execute_body ge 18%N Row_regact_insert_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.

Definition Row_insert_fundef :=
  ltac:(get_fd ["Bf2BloomFilterRow"; "act_insert"] ge).

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
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit 8 1)]
        (EXT [row_repr p (row_insert r i)]))).

Lemma Row_insert_body :
  func_sound ge Row_insert_fundef nil Row_insert_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_insert_execute_body.
  4 : { entailer. }
  { list_solve. }
  { unfold num_slots in *; list_solve. }
  { rewrite Znth_map by list_solve.
    split; reflexivity.
  }
  step.
  entailer.
  f_equal.
  unfold row_insert.
  list_solve.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_insert_body) : func_specs.

Definition Row_regact_query_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_query"; "apply"])).

Definition Row_regact_query_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_query"]) 8 (fun b => b)
    (fun b => P4Bit 8 b).

Lemma Row_regact_query_apply_body :
  func_sound am_ge Row_regact_query_apply_fd nil Row_regact_query_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

Definition Row_regact_query_execute_body :=
  ltac:(build_execute_body ge 18%N Row_regact_query_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_query_execute_body) : func_specs.

Definition Row_query_fundef := Eval compute in
  ltac:(get_fd ["Bf2BloomFilterRow"; "act_query"] ge).

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
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit 8 (Z.b2z (row_query r i)))]
        (EXT [row_repr p r]))).

Lemma upd_Znth_Znth_same : forall {A} {dA : Inhabitant A} (al : list A) i,
  upd_Znth i al (Znth i al) = al.
Proof.
  intros.
  list_solve.
Qed.

Lemma upd_Znth_Znth_same' : forall {A} {dA : Inhabitant A} (al : list A) a i,
  a = Znth i al ->
  upd_Znth i al a = al.
Proof.
  intros.
  list_solve.
Qed.

Lemma Row_query_body :
  func_sound ge Row_query_fundef nil Row_query_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_query_execute_body.
  4 : { entailer. }
  { list_solve. }
  { unfold num_slots in *; list_solve. }
  { rewrite Znth_map by list_solve.
    split; reflexivity.
  }
  step.
  entailer.
  { rewrite to_lbool_lbool_to_val' by auto.
    f_equal.
    list_simplify. subst.
    reflexivity.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_query_body) : func_specs.

Definition Row_regact_clear_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear"; "apply"])).

Definition Row_regact_clear_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear"]) 8 (fun _ => 0)
    (fun _ => ValBaseBit (P4Arith.to_loptbool 8 0)).

Lemma Row_regact_clear_apply_body :
  func_sound am_ge Row_regact_clear_apply_fd nil Row_regact_clear_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
Qed.

(* Finished transaction in 0.179 secs (0.14u,0.031s) (successful) *)
Definition Row_regact_clear_execute_body :=
  ltac:(build_execute_body ge 18%N Row_regact_clear_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_clear_execute_body) : func_specs.

Definition Row_clear_fundef :=
  ltac:(get_fd ["Bf2BloomFilterRow"; "act_clear"] ge).

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
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], P4Bit 8 0)]
        (EXT [row_repr p (row_clear r i)]))).

Lemma Row_clear_body :
  func_sound ge Row_clear_fundef nil Row_clear_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_clear_execute_body.
  4 : { entailer. }
  { list_solve. }
  { unfold num_slots in *; list_solve. }
  { rewrite Znth_map by list_solve.
    split; reflexivity.
  }
  step.
  entailer.
  f_equal.
  unfold row_clear.
  list_solve.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_clear_body) : func_specs.

Definition Row_tbl_bloom_fundef :=
  ltac:(get_fd ["Bf2BloomFilterRow"; "tbl_bloom"; "apply"] ge).

Definition Row_fundef :=
  ltac:(get_fd ["Bf2BloomFilterRow"; "apply"] ge).

Definition Row_noop_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [P4Bit 8 NOOP;
              P4Bit 18 i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4NewBit 8] ValBaseNull
        (MEM []
        (EXT [row_repr p r]))).

Definition Row_tbl_bloom_noop_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 NOOP);
              (["index"], P4Bit 18 i);
              (["rw"], P4NewBit 8)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4NewBit 8)]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_noop_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_noop_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { instantiate (1 := [(true, mk_action_ref "NoAction" [])]).
    constructor.
  }
  econstructor.
  (* NOOP case *)
  { reflexivity. }
  { intros.
    step_call NoAction_body.
    { entailer. }
    apply ret_implies_refl.
  }
  { constructor. }
  { intros.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_noop_case_body :
  func_sound ge Row_fundef nil Row_noop_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_noop_body.
  3 : entailer.
  1-2 : auto.
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
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [P4Bit 8 INSERT;
              P4Bit 18 i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit 8 1] ValBaseNull
        (MEM []
        (EXT [row_repr p (row_insert r i)]))).

Definition Row_tbl_bloom_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 INSERT);
              (["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit 8 1)]
        (EXT [row_repr p (row_insert r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_insert_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_insert_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { instantiate (1 := [(true, mk_action_ref "act_insert" [])]).
    constructor.
  }
  econstructor.
  (* INSERT case *)
  { reflexivity. }
  { intros.
    step_call Row_insert_body.
    3 : { entailer. }
    { auto. }
    { auto. }
    apply ret_implies_refl.
  }
  { constructor. }
  { intros.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_insert_case_body :
  func_sound ge Row_fundef nil Row_insert_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_insert_body.
  3 : entailer.
  1-2 : auto.
  Intros _.
  step.
  entailer.
Qed.

Definition Row_query_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [P4Bit 8 QUERY;
              P4Bit 18 i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit 8 (Z.b2z (row_query r i))] ValBaseNull
        (MEM []
        (EXT [row_repr p r]))).

Definition Row_tbl_bloom_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 QUERY);
              (["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit 8 (Z.b2z (row_query r i)))]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_query_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_query_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { instantiate (1 := [(true, mk_action_ref "act_query" [])]).
    constructor.
  }
  econstructor.
  (* QUERY case *)
  { reflexivity. }
  { intros.
    step_call Row_query_body.
    3 : { entailer. }
    { auto. }
    { auto. }
    apply ret_implies_refl.
  }
  { constructor. }
  { intros.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_query_case_body :
  func_sound ge Row_fundef nil Row_query_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_query_body.
  3 : entailer.
  1-2 : auto.
  Intros _.
  step.
  entailer.
Qed.

Definition Row_clear_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [P4Bit 8 CLEAR;
              P4Bit 18 i]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [P4Bit 8 0] ValBaseNull
        (MEM []
        (EXT [row_repr p (row_clear r i)]))).

Definition Row_tbl_bloom_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 CLEAR);
              (["index"], P4Bit 18 i)]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], P4Bit 8 0)]
        (EXT [row_repr p (row_clear r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_clear_body :
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_clear_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { instantiate (1 := [(true, mk_action_ref "act_clear" [])]).
    constructor.
  }
  econstructor.
  (* CLEAR case *)
  { reflexivity. }
  { intros.
    step_call Row_clear_body.
    3 : { entailer. }
    { auto. }
    { auto. }
    apply ret_implies_refl.
  }
  { constructor. }
  { intros.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_clear_case_body :
  func_sound ge Row_fundef nil Row_clear_case_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_clear_body.
  3 : entailer.
  1-2 : auto.
  Intros _.
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_noop_case_body) : func_specs.
