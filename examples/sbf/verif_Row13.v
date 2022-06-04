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


Definition p := ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_3"].

Open Scope func_spec.

Definition Row_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (op : Z) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N op));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i))]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N
          (if (op =? INSERT)%Z then 1 else
           if (op =? QUERY)%Z then Z.b2z (row_query r i) else
           if (op =? CLEAR)%Z then 0 else
           0)))] ValBaseNull
        (MEM []
        (EXT [row_repr p
          (if (op =? INSERT)%Z then row_insert r i else
           if (op =? QUERY)%Z then r else
           if (op =? CLEAR)%Z then row_clear r i else
           r)]))).

Definition Row_regact_insert_apply_sem := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_insert"; "apply"]) (ge_ext ge))).

Definition Row_regact_insert_apply_fd :=
  ltac:(
    let sem := eval unfold Row_regact_insert_apply_sem in Row_regact_insert_apply_sem in
    match sem with
    | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
        exact fd
    end).

Definition Row_regact_insert_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_insert"]) 8 (fun _ => 1)
    (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 1)).

Lemma Row_regact_insert_apply_body :
  fundef_satisfies_spec am_ge Row_regact_insert_apply_fd nil Row_regact_insert_apply_spec.
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
  RegisterAction_execute_body ge am_ge (p ++ ["regact_insert"]) 18%N 8%N num_slots (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_slots; lia))
    Row_regact_insert_apply_fd (fun _ => 1) (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 1)) eq_refl Row_regact_insert_apply_body.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.

Definition NoAction_fundef : @fundef Info := Eval compute in
  force dummy_fundef (PathMap.get ["NoAction"] (ge_func ge)).

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
  fundef_satisfies_spec ge NoAction_fundef nil NoAction_spec.
Proof.
  start_function.
  step.
  entailer.
Qed.

Definition Row_insert_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "act_insert"] (ge_func ge)).

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
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 1)))]
        (EXT [row_repr p (row_insert r i)]))).

Lemma Row_insert_body :
  fundef_satisfies_spec ge Row_insert_fundef nil Row_insert_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_insert_execute_body.
  4 : { entailer. }
  { list_solve. }
  { list_solve. }
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

Definition Row_regact_query_apply_sem := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_query"; "apply"]) (ge_ext ge))).

Definition Row_regact_query_apply_fd :=
  ltac:(
    let sem := eval unfold Row_regact_query_apply_sem in Row_regact_query_apply_sem in
    match sem with
    | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
        exact fd
    end).

Definition Row_regact_query_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_query"]) 8 (fun b => b)
    (fun b => ValBaseBit (P4Arith.to_loptbool 8%N b)).

Lemma Row_regact_query_apply_body :
  fundef_satisfies_spec am_ge Row_regact_query_apply_fd nil Row_regact_query_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

Definition Row_regact_query_execute_body :=
  RegisterAction_execute_body ge am_ge (p ++ ["regact_query"]) 18%N 8%N num_slots (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_slots; lia))
    Row_regact_query_apply_fd (fun b => b) (fun b => ValBaseBit (P4Arith.to_loptbool 8%N b)) eq_refl Row_regact_query_apply_body.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_query_execute_body) : func_specs.

Definition Row_query_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "act_query"] (ge_func ge)).

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
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (bool_to_val (row_query r i)))]
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
  fundef_satisfies_spec ge Row_query_fundef nil Row_query_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_query_execute_body.
  4 : { entailer. }
  { list_solve. }
  { list_solve. }
  { rewrite Znth_map by list_solve.
    split; reflexivity.
  }
  step.
  entailer.
  { unfold P4Arith.to_loptbool.
    rewrite to_lbool_lbool_to_val' by auto.
    repeat constructor.
  }
  { rewrite to_lbool_lbool_to_val' by auto.
    f_equal.
    apply upd_Znth_Znth_same'.
    unfold bool_to_val.
    list_solve.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_query_body) : func_specs.

Definition Row_regact_clear_apply_sem := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_clear"; "apply"]) (ge_ext ge))).

Definition Row_regact_clear_apply_fd :=
  ltac:(
    let sem := eval unfold Row_regact_clear_apply_sem in Row_regact_clear_apply_sem in
    match sem with
    | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
        exact fd
    end).

Definition Row_regact_clear_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear"]) 8 (fun _ => 0)
    (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 0)).

Lemma Row_regact_clear_apply_body :
  fundef_satisfies_spec am_ge Row_regact_clear_apply_fd nil Row_regact_clear_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
Qed.

(* Finished transaction in 0.152 secs (0.14u,0.015s) (successful) *)
Definition Row_regact_clear_execute_body :=
  RegisterAction_execute_body ge am_ge (p ++ ["regact_clear"]) 18%N 8%N num_slots (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_slots; lia))
    Row_regact_clear_apply_fd (fun _ => 0) (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 0)) eq_refl Row_regact_clear_apply_body.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_clear_execute_body) : func_specs.

Definition Row_clear_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "act_clear"] (ge_func ge)).

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
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 0)))]
        (EXT [row_repr p (row_clear r i)]))).

Lemma Row_clear_body :
  fundef_satisfies_spec ge Row_clear_fundef nil Row_clear_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_clear_execute_body.
  4 : { entailer. }
  { list_solve. }
  { list_solve. }
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

Definition Row_tbl_bloom_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "tbl_bloom"; "apply"] (ge_func ge)).

Definition Row_tbl_bloom_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row) (op i : Z)
      (_ : Zlength r = num_slots)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N op)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N
          (if (op =? INSERT)%Z then 1 else
           if (op =? QUERY)%Z then Z.b2z (row_query r i) else
           if (op =? CLEAR)%Z then 0 else
           0))))]
        (EXT [row_repr p
          (if (op =? INSERT)%Z then row_insert r i else
           if (op =? QUERY)%Z then r else
           if (op =? CLEAR)%Z then row_clear r i else
           r)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { instantiate (1 :=
        [((op =? INSERT)%Z, mk_action_ref "act_insert" []);
         ((op =? QUERY)%Z, mk_action_ref "act_query" []);
         ((op =? CLEAR)%Z, mk_action_ref "act_clear" [])]).
    admit.
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
    replace (op =? INSERT)%Z with true.
    apply arg_ret_implies_post_ex. eexists.
    entailer.
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
    replace (op =? INSERT)%Z with false by hauto.
    replace (op =? QUERY)%Z with true.
    apply arg_ret_implies_post_ex. eexists.
    entailer.
    destruct (row_query r i);
      apply sval_refine_refl.
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
    replace (op =? INSERT)%Z with false by hauto.
    replace (op =? QUERY)%Z with false by hauto.
    replace (op =? CLEAR)%Z with true.
    apply arg_ret_implies_post_ex. eexists.
    entailer.
  }
  econstructor.
  (* NOOP case *)
  (* We cannot prove the NOOP case with the current spec. *)
Admitted.

Definition Row_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "apply"] (ge_func ge)).

(* Note: In order to automatically prove modifies clauses for tables, we need to
  ensure that the action will be executed by tables are only actions listed in the
  action list. That can be guaranteed in the lookup and synthesize step. *)

Lemma Row_body :
  fundef_satisfies_spec ge Row_fundef nil Row_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_body.
  4 : entailer.
  1-3 : auto.
  Intros _.
  step.
  entailer.
Qed.

Definition Row_noop_case_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (i : Z)
      (_ : Zlength r = num_slots)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N NOOP));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i))]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [ValBaseBit (Zrepeat None 8)] ValBaseNull
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
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N NOOP)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)));
              (["rw"], ValBaseBit (Zrepeat None 8))]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], ValBaseBit (Zrepeat None 8))]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_noop_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_noop_spec.
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
    apply arg_ret_implies_post_ex. eexists.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_noop_case_body :
  fundef_satisfies_spec ge Row_fundef nil Row_noop_case_spec.
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
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N INSERT));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i))]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 1))] ValBaseNull
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
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N INSERT)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 1)))]
        (EXT [row_repr p (row_insert r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_insert_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_insert_spec.
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
    apply arg_ret_implies_post_ex. eexists.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_insert_case_body :
  fundef_satisfies_spec ge Row_fundef nil Row_insert_case_spec.
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
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N QUERY));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i))]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 (Z.b2z (row_query r i))))] ValBaseNull
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
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N QUERY)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 (Z.b2z (row_query r i)))))]
        (EXT [row_repr p r]))))%arg_ret_assr.

Lemma Row_tbl_bloom_query_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_query_spec.
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
    apply arg_ret_implies_post_ex. eexists.
    entailer.
    destruct (row_query r i);
      apply sval_refine_refl.
  }
  intros H; inv H.
Qed.

Lemma Row_query_case_body :
  fundef_satisfies_spec ge Row_fundef nil Row_query_case_spec.
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
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N CLEAR));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i))]
        (MEM []
        (EXT [row_repr p r])))
      POST
        (ARG_RET [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 0))] ValBaseNull
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
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N CLEAR)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8 0)))]
        (EXT [row_repr p (row_clear r i)]))))%arg_ret_assr.

Lemma Row_tbl_bloom_clear_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_clear_spec.
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
    apply arg_ret_implies_post_ex. eexists.
    entailer.
  }
  intros H; inv H.
Qed.

Lemma Row_clear_case_body :
  fundef_satisfies_spec ge Row_fundef nil Row_clear_case_spec.
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
