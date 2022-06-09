Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
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

Definition p := ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"].

Open Scope func_spec.

Definition Row_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row num_slots) (op : Z) (i : Z)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < num_slots),
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
    WITH (r : row num_slots) (i : Z)
      (_ : 0 <= i < num_slots),
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
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_insert_body) : func_specs.

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
    WITH (r : row num_slots) (i : Z)
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 18%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (bool_to_val (row_query r i)))]
        (EXT [row_repr p r]))).

Lemma Row_query_body :
  func_sound ge Row_query_fundef nil Row_query_spec.
Proof.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_query_body) : func_specs.

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
    WITH (r : row num_slots) (i : Z)
      (_ : 0 <= i < num_slots),
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
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_clear_body) : func_specs.

Definition Row_tbl_bloom_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "tbl_bloom"; "apply"] (ge_func ge)).

Definition Row_tbl_bloom_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["rw"]]) [p]
    WITH (r : row num_slots) (op i : Z)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < num_slots),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 op);
              (["index"], P4Bit 18 i)]
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
  start_function.
  (* simpl Tofino.extern_matches. *)
  econstructor.
  (* INSERT case *)
  { intros.
    econstructor.
    { reflexivity. }
    { step_call Row_insert_body.
      { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { assert (op = INSERT). {
        repeat destruct H as [? | H]; subst; try solve [inv H1].
        auto.
        destruct H.
      }
      subst.
      entailer.
    }
  }
  econstructor.
  (* QUERY case *)
  { intros.
    econstructor.
    { reflexivity. }
    { step_call Row_query_body.
      { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { assert (op = QUERY). {
        repeat destruct H as [? | H]; subst; try solve [inv H2].
        auto.
        destruct H.
      }
      subst.
      entailer.
      destruct (row_query r i);
        apply sval_refine_refl.
    }
  }
  econstructor.
  (* CLEAR case *)
  { intros.
    econstructor.
    { reflexivity. }
    { step_call Row_clear_body.
      { entailer. }
      { auto. }
      apply ret_implies_refl.
    }
    { constructor. }
    { assert (op = CLEAR). {
        repeat destruct H as [? | H]; subst; try solve [inv H3].
        auto.
        destruct H.
      }
      subst.
      entailer.
    }
  }
  (* NOOP case *)
  (* We cannot prove the NOOP case with the current spec. *)
Admitted.

(* Definition Row_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "apply"] (ge_func ge)). *)

(* Note: In order to automatically prove modifies clauses for tables, we need to
  ensure that the action will be executed by tables are only actions listed in the
  action list. That can be guaranteed in the lookup and synthesize step. *)

(* Lemma Row_body :
  func_sound ge Row_fundef nil Row_spec.
Proof.
  start_function.
  step.
  step_call Row_tbl_bloom_body.
  { entailer. }
  1-2 : auto.
  Intros _.
  step.
  entailer.
Qed. *)
