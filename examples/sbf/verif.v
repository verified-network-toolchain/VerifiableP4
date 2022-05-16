Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
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

Opaque PathMap.empty PathMap.set.

(* This currently takes 7s to evaluate. The reason is the exec_abstract_method takes a
  partial_ge as a parameter and this partial_ge is fully expended and we have as many copies
  as the number of instances. We would try to prevent this partial_ge from unfolding later. *)
Definition ge : genv := Eval compute in gen_ge prog.

Transparent PathMap.empty PathMap.set.

Definition p :=  ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"].

(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Open Scope func_spec.

Definition Row_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (op : Z) (i : Z)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N op));
              eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i))]
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
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 1)))]
        (EXT [row_repr p (row_insert r i)]))).

Definition Row_regact_insert_execute_spec : func_spec :=
  WITH (* p *),
    PATH p ++ ["regact_insert"]
    MOD None [p ++ ["reg_row"]]
    WITH (r : row) (i : Z)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i))]
        (MEM []
        (EXT [ExtPred.singleton (p ++ ["reg_row"]) (Tofino.ObjRegister (map bool_to_val r))])))
      POST
        (ARG_RET [] (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N 1)))
        (MEM []
        (EXT [ExtPred.singleton (p ++ ["reg_row"])
            (Tofino.ObjRegister (upd_Znth i (map bool_to_val r) (bool_to_val true)))]))).

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.
Definition execute_fundef : @fundef Info := FExternal "RegisterAction" "execute".

Axiom Row_regact_insert_execute_body :
  fundef_satisfies_spec ge execute_fundef nil Row_regact_insert_execute_spec.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.
(* #[local] Hint Extern 1 (list P4Type) => (exact (@nil _)) : func_specs. *)

Axiom Row_regact_query_execute_modifies :
  func_modifies ge (p ++ ["regact_query"]) (FExternal "RegisterAction" "execute") None [].
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_query_execute_modifies) : func_specs.

Axiom Row_regact_clear_execute_modifies :
  func_modifies ge (p ++ ["regact_clear"]) (FExternal "RegisterAction" "execute") None [p ++ ["reg_row"]].
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_clear_execute_modifies) : func_specs.

Definition NoAction_fundef : @fundef Info := Eval compute in
  force dummy_fundef (PathMap.get ["NoAction"] (ge_func ge)).

(* Axiom Row_regact_clear_execute_modifies :
  func_modifies ge (p ++ ["regact_clear"]) (FExternal "RegisterAction" "execute") None [p ++ ["reg_row"]].
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_clear_execute_modifies) : func_specs. *)

Definition Row_insert_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "act_insert"] (ge_func ge)).

Lemma Row_insert_body :
  fundef_satisfies_spec ge Row_insert_fundef nil Row_insert_spec.
Proof.
  start_function.
  unfold row_repr, row_reg_repr.
  normalize_EXT.
  step_call Row_regact_insert_execute_body.
  2 : { entailer. }
  { auto. }
  step.
  entailer.
  f_equal.
  unfold row_insert.
  list_solve.
Qed.

Definition Row_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Bf2BloomFilterRow"; "apply"] (ge_func ge)).

(* Note: In order to automatically prove modifies clauses for tables, we need to
  ensure that the action will be executed by tables are only actions listed in the
  action list. That can be guaranteed in the lookup and synthesize step. *)

Lemma Row_body :
  fundef_satisfies_spec ge Row_fundef nil Row_spec.
Proof.
  start_function.
  step_into_call.
  { hoare_func_table.
    admit.
    admit.
  }
  (* destruct (Z.eq_dec op INSERT).
  { subst op.
    step_into_call.
  { hoare_func_table.
    step_call Row_insert_body.
    2 : { entailer. }
    auto.
  }
  { reflexivity. }
  { reflexivity. }
  { entailer. } *)
Abort.
