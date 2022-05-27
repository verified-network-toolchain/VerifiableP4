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

Definition num_cells := 65536.

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.
Definition execute_fundef : @fundef Info := FExternal "RegisterAction" "execute".

(* This is the general form of RegisterAction's apply method's spec that we support.
  We expecct this is general enough for all practical application. We don't support
  other kind of apply methods. *)
Definition RegisterAction_apply_spec (p : path) (w : N) (f : Z -> Z) (retv : Z -> Sval) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH old_value (H_old_value : 0 <= old_value < Z.pow 2 (Z.of_N w)),
      PRE
        (ARG [ValBaseBit (P4Arith.to_loptbool w old_value)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [ValBaseBit (P4Arith.to_loptbool w (f old_value));
                  retv old_value]
           ValBaseNull
        (MEM []
        (EXT []))).

(* TODO write down the write post condition.
  the problem here is, we need to say Znth i c is ValBaseBit, right? *)

Definition RegisterAction_execute_spec : func_spec :=
  WITH p (* path *) index_w w (* width *) s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (w, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : fundef_satisfies_spec am_ge apply_fd nil
          (RegisterAction_apply_spec p w apply_f apply_retv)),
    PATH p
    MOD None [r]
    WITH (c : list Val) (i : Z)
      (H_c : Zlength c = s)
      (H_i : 0 <= i < s)
      old_v
      (H_old_v : Znth i c = ValBaseBit old_v /\ Zlength old_v = Z.of_N w),
      PRE
        (ARG [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool index_w i))]
        (MEM []
        (EXT [ExtPred.singleton r (Tofino.ObjRegister c)])))
      POST
        (ARG_RET [] (apply_retv (P4Arith.BitArith.lbool_to_val old_v 1 0))
        (MEM []
        (EXT [ExtPred.singleton r
            (Tofino.ObjRegister (upd_Znth i c
                (ValBaseBit (P4Arith.to_lbool w (apply_f (P4Arith.BitArith.lbool_to_val old_v 1 0))))))]))).

Ltac intros_fs_bind :=
  repeat lazymatch goal with
  | |- fundef_satisfies_spec _ _ _ (fs_bind (fun x => _)) =>
    let x := fresh x in intro x
  | |- fundef_satisfies_spec _ _ _ ?x =>
    unfold x
  end.

Ltac intros_fsh_bind :=
  repeat lazymatch goal with
  | |- fundef_satisfies_hoare _ _ _ _ (fsh_bind (fun x => _)) =>
    let x := fresh x in intro x
  | |- fundef_satisfies_hoare _ _ _ _ ?x =>
    unfold x
  end.

Lemma RegisterAction_execute_body :
  fundef_satisfies_spec ge execute_fundef nil RegisterAction_execute_spec.
Proof.
  intros_fs_bind.
  split.
  2 : {
    unfold func_modifies. intros.
    inv H.
    inv H5. inv H.
    eapply eq_trans in H0; only 2 : (symmetry; apply H_r).
    symmetry in H0; inv H0.
    eapply eq_trans in H3; only 2 : (symmetry; apply H_ws).
    symmetry in H3; inv H3.
    eapply eq_trans in H1; only 2 : (symmetry; apply H_apply_fd).
    symmetry in H1; inv H1.
    destruct (-1 <? index) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    destruct (index <? s) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    simpl in H8. destruct H8; subst.
    eapply modifies_trans.
    { eapply modifies_incl.
      { assert (modifies None [] (m, es) (m, s')). {
          split.
          { constructor. }
          { simpl.
            inv H7.
            eapply (proj2 H_apply_body) in H1.
            apply H1.
          }
        }
        eassumption.
      }
      all : solve_modifies.
    }
    eapply modifies_set_ext with (st := (m, s')).
    simpl.
    replace (in_scope r r) with true. 2 : {
      clear; induction r.
      - auto.
      - simpl. rewrite eqb_refl; auto.
    }
    auto.
  }
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold hoare_func; intros.
  inv H0. inv H6.
  inv H0.
  eapply eq_trans in H1; only 2 : (symmetry; apply H_r).
  symmetry in H1; inv H1.
  eapply eq_trans in H4; only 2 : (symmetry; apply H_ws).
  symmetry in H4; inv H4.
  eapply eq_trans in H2; only 2 : (symmetry; apply H_apply_fd).
  symmetry in H2; inv H2.
  destruct H as [? []].
  destruct H1 as [? _].
  simpl in H1.
  rewrite H5 in H1. inv H1.
  assert (index = i). {
    clear -H_i H_s H H3 H6.
    unfold arg_denote, arg_satisfies in H.
    inv H. inv H5.
    inv H3. clear H7.
    assert (ValBaseBit indexb = (ValBaseBit (P4Arith.to_lbool index_w i))). {
      eapply exec_val_eq.
      eapply exec_val_sym with eq.
      { clear; auto. }
      assert (val_to_sval
          (ValBaseBit (P4Arith.to_lbool index_w i))
          (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool index_w i)))). {
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
    apply Z.mod_small.
    unfold P4Arith.BitArith.upper_bound.
    lia.
  }
  clear H H3 H6.
  subst.
  destruct (-1 <? i) eqn:Heqb; only 2 : lia. clear Heqb.
  destruct (i <? Zlength c) eqn:Heqb; only 2 : lia. clear Heqb.
  simpl in H7. destruct H9. subst.
  clear H0.
  assert (content' = c). {
    clear -H_apply_body H H5 H8.
    inv H8.
    apply (H_apply_body) in H1.
    destruct H1.
    assert (PathMap.get r s' = PathMap.get r es). {
      symmetry.
      apply H3.
      auto.
    }
    rewrite H4 in H.
    change (@extern_object Info (@Expression Info) (@extern_sem Info (@Expression Info) target))
      with (@Tofino.object Info (@Expression Info)) in H.
    congruence.
  }
  clear H H5.
  subst.
  destruct H_old_v.
  set (old_value := P4Arith.BitArith.lbool_to_val old_v 1 0).
  assert (new_value = ValBaseBit (P4Arith.to_lbool w (apply_f old_value))
      /\ sval_to_val read_ndetbit (apply_retv old_value) retv). {
    clear -H_apply_body H H0 H8.
    inv H8.
    eapply (proj1 H_apply_body old_value) in H2.
    3 : {
      split.
      2 : { split; constructor. }
      inv H1. inv H8.
      rewrite H in H6. constructor. 2 : constructor.
      subst old_value.
      assert (forall b, P4Arith.to_lbool (fst (P4Arith.BitArith.from_lbool b)) (snd (P4Arith.BitArith.from_lbool b)) = b)
        as to_lbool_from_lbool by admit.
      replace w with (fst (P4Arith.BitArith.from_lbool old_v))
        by (unfold P4Arith.BitArith.from_lbool, fst; lia).
      unfold P4Arith.to_loptbool.
      rewrite to_lbool_from_lbool.
      eapply exec_val_trans with (f := read_ndetbit). 3 : eassumption.
      { red. sauto. }
      constructor.
      clear; induction old_v.
      - constructor.
      - constructor; auto. constructor.
    }
    2 : {
      pose proof (P4Arith.BitArith.from_lbool_bound old_v).
      unfold uncurry, P4Arith.BitArith.bound, P4Arith.BitArith.upper_bound in H4.
      unfold P4Arith.BitArith.from_lbool in H4.
      rewrite H0 in H4.
      rewrite N2Z.id in H4.
      subst old_value. simpl. lia.
    }
    clear H1.
    destruct H2.
    inv H1. inv H8. inv H9.
    assert (sval_refine_sval_to_val_n_trans : forall v1 v2 v3,
      sval_refine v1 v2 ->
      sval_to_val read_ndetbit v2 v3 ->
      sval_to_val read_ndetbit v1 v3). {
      intros. eapply exec_val_trans; only 2, 3 : eassumption.
      red; sauto.
    }
    inv H3. inv H10. inv H11.
    eapply sval_refine_sval_to_val_n_trans in H6. 2 : eapply H8. clear H8.
    eapply sval_refine_sval_to_val_n_trans in H5. 2 : eapply H7. clear H7.
    split.
    { eapply sval_to_val_bit_to_loptbool; eauto. }
    { auto. }
  }
  clear H8.
  destruct H1; subst.
  split.
  { inv H12. constructor. }
  clear H12.
  split.
  { unfold ret_denote, ret_satisfies.
    intros.
    eapply exec_val_trans; only 2, 3 : eassumption.
    clear; red; sauto.
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

Definition Row_regact_insert_apply_sem := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_insert"; "apply"]) (ge_ext ge))).

Definition Row_regact_insert_apply_fd :=
  ltac : (
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

Program Definition Row_regact_insert_execute_body :=
  RegisterAction_execute_body _ 16%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
    Row_regact_insert_apply_fd (fun _ => 1) (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 1)) eq_refl Row_regact_insert_apply_body.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.

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
      (_ : Zlength r = num_cells)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i)))]
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
