Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.TofinoSpec.
Require Import ProD3.examples.sbf.UseTofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

(* By making am_ge opaque, now it takes 28s. *)
Definition am_ge : genv := Eval compute -[PathMap.empty PathMap.set Tofino.extern_match] in gen_am_ge prog.
Definition ge : genv := Eval compute -[am_ge PathMap.empty PathMap.set Tofino.extern_match] in gen_ge' am_ge prog.

Definition p := ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"].

(* Eval compute in PathMap.get (p ++ ["regact_insert"]) (ge_ext ge).
Time Eval compute in PathMap.get (p ++ ["regact_insert"; "apply"]) (ge_ext ge). *)

(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Open Scope func_spec.

Definition num_cells := 262144.

Definition Row_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row num_cells) (op : Z) (i : Z)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < num_cells),
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

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.

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
  RegisterAction_execute_body ge am_ge (p ++ ["regact_insert"]) 18%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
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
  func_sound ge NoAction_fundef nil NoAction_spec.
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
    WITH (r : row num_cells) (i : Z)
      (_ : 0 <= i < num_cells),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 1)))]
        (EXT [row_repr p (row_insert r i)]))).

Lemma Row_insert_body :
  func_sound ge Row_insert_fundef nil Row_insert_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig row_insert].
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
  func_sound am_ge Row_regact_query_apply_fd nil Row_regact_query_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

Definition Row_regact_query_execute_body :=
  RegisterAction_execute_body ge am_ge (p ++ ["regact_query"]) 18%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
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
    WITH (r : row num_cells) (i : Z)
      (_ : 0 <= i < num_cells),
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
  func_sound ge Row_query_fundef nil Row_query_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig].
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
    apply sval_refine_refl.
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
  func_sound am_ge Row_regact_clear_apply_fd nil Row_regact_clear_apply_spec.
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
  RegisterAction_execute_body ge am_ge (p ++ ["regact_clear"]) 18%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
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
    WITH (r : row num_cells) (i : Z)
      (_ : 0 <= i < num_cells),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 0)))]
        (EXT [row_repr p (row_clear r i)]))).

Lemma Row_clear_body :
  func_sound ge Row_clear_fundef nil Row_clear_spec.
Proof.
  start_function.
  destruct r as [r ?H].
  unfold row_repr, row_reg_repr. cbn [proj1_sig row_clear].
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
  list_solve.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_clear_body) : func_specs.

Definition Row_tbl_bloom_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "tbl_bloom"; "apply"] (ge_func ge)).

Definition Row_tbl_bloom_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row num_cells) (op i : Z)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < num_cells),
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
  func_sound ge Row_tbl_bloom_fundef nil Row_tbl_bloom_spec.
Proof.
  split. 2 : {
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.

  hoare_func_table.
  simpl Tofino.extern_matches.
  econstructor.
  (* INSERT case *)
  { econstructor.
    { reflexivity. }
    { intros.
      step_call Row_insert_body.
      2 : { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { intros.
      assert (op = INSERT). {
        repeat destruct x as [? | x]; subst; try solve [inv H].
        auto.
        destruct x.
      }
      subst.
      apply arg_ret_implies_post_ex. eexists.
      entailer.
    }
  }
  econstructor.
  (* QUERY case *)
  { econstructor.
    { reflexivity. }
    { intros.
      step_call Row_query_body.
      2 : { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { intros.
      assert (op = QUERY). {
        repeat destruct x as [? | x]; subst; try solve [inv H0].
        auto.
        destruct x.
      }
      subst.
      apply arg_ret_implies_post_ex. eexists.
      entailer.
      destruct (row_query r i);
        apply sval_refine_refl.
    }
  }
  econstructor.
  (* CLEAR case *)
  { econstructor.
    { reflexivity. }
    { intros.
      step_call Row_clear_body.
      2 : { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { intros.
      assert (op = CLEAR). {
        repeat destruct x as [? | x]; subst; try solve [inv H1].
        auto.
        destruct x.
      }
      subst.
      apply arg_ret_implies_post_ex. eexists.
      entailer.
    }
  }
  (* NOOP case *)
  (* We cannot prove the NOOP case with the current spec. *)
Admitted.

Definition Row_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "apply"] (ge_func ge)).

(* Note: In order to automatically prove modifies clauses for tables, we need to
  ensure that the action will be executed by tables are only actions listed in the
  action list. That can be guaranteed in the lookup and synthesize step. *)

Lemma Row_body :
  func_sound ge Row_fundef nil Row_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_body.
  3 : entailer.
  1-2 : auto.
  Intros _.
  step.
  entailer.
Qed.
