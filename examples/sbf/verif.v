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

(* By making am_ge opaque, now it takes 28s. *)
Definition am_ge : genv := Eval compute -[PathMap.empty PathMap.set] in gen_am_ge prog.
Definition ge : genv := Eval compute -[am_ge PathMap.empty PathMap.set] in gen_ge' am_ge prog.

Definition p :=  ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"].

(* Eval compute in PathMap.get (p ++ ["regact_insert"]) (ge_ext ge).
Time Eval compute in PathMap.get (p ++ ["regact_insert"; "apply"]) (ge_ext ge). *)

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

Definition num_cells := 65536.

Definition Row_regact_insert_execute_spec : func_spec :=
  WITH (* p *),
    PATH p ++ ["regact_insert"]
    MOD None [p ++ ["reg_row"]]
    WITH (r : row) (i : Z)
      (H_r : Zlength r = num_cells)
      (H_i : 0 <= i < num_cells),
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

Definition Row_regact_insert_apply_fundef := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_insert"; "apply"]) (ge_ext ge))).

Definition Row_regact_insert_apply :=
  FInternal [(["apply"; "value"], InOut); (["apply"; "rv"], Out)]
    (BlockCons
       (MkStatement NoInfo
          (StatVariable (TypTypeName {| P4String.tags := NoInfo; str := "bf2_value_t" |})
             {| P4String.tags := NoInfo; str := "rv" |} None (LInstance ["rv"])) StmUnit)
       (BlockCons
          (MkStatement NoInfo
             (StatAssignment
                (MkExpression NoInfo
                   (ExpName (BareName {| P4String.tags := NoInfo; str := "value" |})
                      (LInstance ["apply"; "value"]))
                   (TypTypeName {| P4String.tags := NoInfo; str := "bf2_value_t" |}) InOut)
                (MkExpression NoInfo
                   (ExpInt
                      {| tags := NoInfo; value := 1; width_signed := Some (8%N, false) |})
                   (TypBit 8) Directionless)) StmUnit)
          (BlockCons
             (MkStatement NoInfo
                (StatAssignment
                   (MkExpression NoInfo
                      (ExpName (BareName {| P4String.tags := NoInfo; str := "rv" |})
                         (LInstance ["apply"; "rv"]))
                      (TypTypeName {| P4String.tags := NoInfo; str := "bf2_value_t" |}) Out)
                   (MkExpression NoInfo
                      (ExpInt
                         {| tags := NoInfo; value := 1; width_signed := Some (8%N, false) |})
                      (TypBit 8) Directionless)) StmUnit) (BlockEmpty NoInfo)))).

Definition Row_regact_insert_apply_spec : func_spec :=
  WITH,
    PATH (p ++ ["regact_insert"])
    MOD None []
    WITH,
      PRE
        (ARG [ValBaseBit (repeat None 8)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [ValBaseBit (P4Arith.to_loptbool 8%N 1);
                  ValBaseBit (P4Arith.to_loptbool 8%N 1)]
           ValBaseNull
        (MEM []
        (EXT []))).

Lemma Row_regact_insert_apply_body :
  fundef_satisfies_spec am_ge Row_regact_insert_apply nil Row_regact_insert_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
Qed.

(* So the problem here is that, we need to define a rule for execute.
  And, should the ge constraint in spec for read and write be on the path quantifier? *)

(* Currently we have two problem. One is to use abstract method spec to prove execute.
The other is to find a way to prevent unfolding Extern typeclass in the computation of ge. *)

Lemma Row_regact_insert_execute_body :
  fundef_satisfies_spec ge execute_fundef nil Row_regact_insert_execute_spec.
Proof.
  split.
  2 : {
    unfold func_modifies; intros.
    inv H.
    inv H5. inv H. compute in H0. inv H0.
    compute in H3; inv H3.
    destruct (-1 <? index) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    destruct (index <? 65536) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    simpl in H8. destruct H8; subst.
    compute - [am_ge] in H1. inv H1.
    eapply modifies_trans.
    { eapply modifies_incl.
      assert (modifies None [] (m, es) (m, s')). {
        change
          (exec_abstract_method (tags_t := Info) (target := target) am_ge (p ++ ["regact_insert"])
            Row_regact_insert_apply
            es [old_value] s' [new_value; retv] SReturnNull)
          in H7.
        inv H7.
        split.
        { constructor. }
        { simpl.
          apply Row_regact_insert_apply_body in H1.
          apply H1.
        }
      }
      eassumption.
      solve_modifies.
      solve_modifies.
    }
    eapply modifies_set_ext with (st := (m, s')).
    auto.
  }
  repeat lazymatch goal with
  | |- fundef_satisfies_hoare _ _ _ _ (fsh_bind (fun x => _)) =>
    let x := fresh x in intro x
  end;
  unfold fundef_satisfies_hoare.
  unfold hoare_func; intros.
  inv H0. inv H6.
  cbn - [ge] in H0.
  inv H0.
  compute in H1. inv H1. (* get reg from ge *)
  compute in H4. inv H4. (* get (w, size) from ge *)
  destruct H as [? [_ ?]].
  assert (index = i). {
    clear -H_i H H3 H6.
    unfold arg_denote, arg_satisfies in H.
    remember (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16 i))) as x in H.
    inv H. inv H5.
    inv H3. clear H7.
    assert (ValBaseBit indexb = (ValBaseBit (P4Arith.to_lbool 16 i))). {
      eapply exec_val_eq.
      eapply exec_val_sym with eq.
      { clear; auto. }
      assert (val_to_sval
          (ValBaseBit (P4Arith.to_lbool 16 i))
          (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16 i)))). {
        eapply exec_val_sym with strict_read_ndetbit.
        2 : eapply sval_to_val_eval_val_to_sval.
        { clear; sauto. }
        { clear; sauto. }
      }
      eapply exec_val_trans with (f := read_detbit);
        [ | eapply exec_val_trans; [ | eassumption | eassumption] | eassumption ].
      { unfold rel_trans; clear; sauto. }
      { unfold rel_trans; clear; sauto. }
    }
    inv H.
    rewrite P4Arith.bit_from_to_bool in H6.
    inv H6.
    apply Z.mod_small; assumption.
  }
  clear H H3 H6.
  subst.
  destruct (-1 <? i) eqn:Heqb; only 2 : lia. clear Heqb.
  destruct (i <? 65536) eqn:Heqb; only 2 : (unfold num_cells in H_i; lia). clear Heqb.
  compute -[target am_ge] in H2. inv H2.
  change
    (exec_abstract_method (tags_t := Info) (target := target) am_ge (p ++ ["regact_insert"])
      Row_regact_insert_apply
      es [old_value] s' [new_value; retv] SReturnNull)
    in H8.
  simpl in H7. destruct H9. subst.
  assert (content = map bool_to_val r). {
    clear -H0 H5.
    inv H0.
    simpl in H.
    congruence.
  }
  clear H0.
  subst.
  assert (content' = map bool_to_val r). {
    clear -H H5 H8.
    inv H8.
    apply (Row_regact_insert_apply_body) in H1.
    destruct H1.
    assert (PathMap.get ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"; "reg_row"] s'
        = PathMap.get ["pipe"; "ingress"; "bf2_ds"; "win_1"; "row_1"; "reg_row"] es). {
      symmetry.
      apply H3.
      auto.
    }
    rewrite H4 in H.
    change (@extern_object Info (@Expression Info) (@extern_sem Info (@Expression Info) target))
      with (@Tofino.object Info (@Expression Info)) in H.
    rewrite H5 in H.
    congruence.
  }
  clear H H5.
  subst.
  rewrite Znth_map in H8 by list_solve.
  assert (new_value = ValBaseBit (P4Arith.to_lbool 8 1)
      /\ retv = ValBaseBit (P4Arith.to_lbool 8 1)). {
    clear -H8.
    inv H8.
    apply (proj1 Row_regact_insert_apply_body) in H0.
    2 : {
      split.
      2 : { split; constructor. }
      inv H. inv H4. inv H6.
      do 9 lazymatch goal with
      | H : Forall2 read_detbit _ _ |- _ =>
          inv H
      end.
      do 8 lazymatch goal with
      | H : read_detbit _ _ |- _ =>
          inv H
      end.
      repeat constructor.
    }
    destruct H0.
    inv H0. inv H7. inv H8.
    assert (forall width value sv,
      sval_refine (ValBaseBit (P4Arith.to_loptbool width value)) sv ->
      sv = (ValBaseBit (P4Arith.to_loptbool width value))
    ) as sval_refine_bit_to_loptbool by admit.
    apply sval_refine_bit_to_loptbool in H4, H5; subst.
    inv H1. inv H7. clear H8.
    assert (forall width value v,
      sval_to_val read_ndetbit (ValBaseBit (P4Arith.to_loptbool width value)) v ->
      v = (ValBaseBit (P4Arith.to_lbool width value))
    ) as sval_to_val_bit_to_loptbool by admit.
    apply sval_to_val_bit_to_loptbool in H4, H5; subst.
    auto.
  }
  clear H8.
  destruct H; subst.
  simpl.
  split.
  { inv H12. constructor. }
  clear H12.
  split.
  { unfold ret_denote, ret_satisfies.
    intros.
    assert (forall width value sv,
      val_to_sval (ValBaseBit (P4Arith.to_lbool width value)) sv ->
      sv = (ValBaseBit (P4Arith.to_loptbool width value))
    ) as val_to_sval_bit_to_lbool by admit.
    apply val_to_sval_bit_to_lbool in H. subst.
    repeat constructor.
  }
  split.
  { constructor. }
  { constructor.
    2 : constructor.
    simpl.
    rewrite PathMap.get_set_same.
    auto.
  }
Admitted.

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
