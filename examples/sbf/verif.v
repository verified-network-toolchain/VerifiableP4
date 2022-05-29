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

Definition num_cells := 65536.

Definition Row_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (r : row) (op : Z) (i : Z)
      (_ : Zlength r = num_cells)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
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

Fixpoint to_lbool'' (width : nat) (value : Z) : list bool :=
  match width with
  | 0%nat => []
  | S n => Z.odd value :: to_lbool'' n (value / 2)
  end.

Lemma to_lbool'_app : forall width value res,
  P4Arith.to_lbool' width value res = P4Arith.to_lbool' width value [] ++ res.
Proof.
  induction width; intros.
  - auto.
  - simpl.
    rewrite IHwidth.
    rewrite IHwidth with (res := [Z.odd value]).
    list_solve.
Qed.

Lemma to_lbool''_to_lbool' : forall width value,
  to_lbool'' width value = rev (P4Arith.to_lbool' width value []).
Proof.
  induction width; intros.
  - auto.
  - simpl.
    rewrite to_lbool'_app.
    rewrite rev_app_distr.
    rewrite IHwidth.
    auto.
Qed.

Lemma to_lbool_lbool_to_val : forall bs,
  P4Arith.to_lbool (Z.to_N (Zlength bs))
      (P4Arith.BitArith.lbool_to_val bs 1 0)
  = bs.
Proof.
  intros.
  unfold P4Arith.to_lbool.
  rewrite <- to_lbool''_to_lbool'.
  induction bs.
  - auto.
  - replace (N.to_nat (Z.to_N (Zlength (a :: bs))))
      with (S (N.to_nat (Z.to_N (Zlength bs)))) by list_solve.
    simpl.
    rewrite P4Arith.BitArith.lbool_to_val_1_0.
    rewrite P4Arith.BitArith.lbool_to_val_1_0 with (o := 2).
    destruct a.
    + replace (Z.odd (P4Arith.BitArith.lbool_to_val bs 1 0 * 2 + 1)) with true. 2 : {
        rewrite Z.add_comm.
        rewrite Z.mul_comm.
        rewrite Z.odd_add_mul_2.
        auto.
      }
      rewrite Z.div_add_l by lia.
      replace (1 / 2) with 0 by auto.
      rewrite Z.add_0_r.
      f_equal; auto.
    + replace (Z.odd (P4Arith.BitArith.lbool_to_val bs 1 0 * 2 + 0)) with false. 2 : {
        rewrite Z.add_comm.
        rewrite Z.mul_comm.
        rewrite Z.odd_add_mul_2.
        auto.
      }
      rewrite Z.div_add_l by lia.
      replace (1 / 2) with 0 by auto.
      rewrite Z.add_0_r.
      f_equal; auto.
Qed.

Lemma to_lbool_lbool_to_val' : forall bs w,
  w = Z.to_N (Zlength bs) ->
  P4Arith.to_lbool w
      (P4Arith.BitArith.lbool_to_val bs 1 0)
  = bs.
Proof.
  intros; subst.
  apply to_lbool_lbool_to_val.
Qed.

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
      replace w with (Z.to_N (Zlength old_v)) by (lia).
      unfold P4Arith.to_loptbool.
      rewrite to_lbool_lbool_to_val.
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
Qed.

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

(* I would like to make it opaque, but I don't know how to. *)
Program Definition Row_regact_insert_execute_body :=
  RegisterAction_execute_body _ 16%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
    Row_regact_insert_apply_fd (fun _ => 1) (fun _ => ValBaseBit (P4Arith.to_loptbool 8%N 1)) eq_refl Row_regact_insert_apply_body.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_regact_insert_execute_body) : func_specs.

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

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Row_insert_body) : func_specs.

Definition Row_regact_query_apply_sem := Eval compute -[am_ge] in
  (force Tofino.EnvPin (PathMap.get (p ++ ["regact_query"; "apply"]) (ge_ext ge))).

Definition Row_regact_query_apply_fd :=
  ltac : (
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

Program Definition Row_regact_query_execute_body :=
  RegisterAction_execute_body _ 16%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
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
      (_ : Zlength r = num_cells)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i)))]
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
  ltac : (
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

Program Definition Row_regact_clear_execute_body :=
  RegisterAction_execute_body _ 16%N 8%N num_cells (p ++ ["reg_row"]) eq_refl eq_refl ltac:(abstract (unfold num_cells; lia))
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
      (_ : Zlength r = num_cells)
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i)))]
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
      (_ : Zlength r = num_cells)
      (_ : In op [NOOP; INSERT; QUERY; CLEAR])
      (_ : 0 <= i < Zlength r),
      PRE
        (ARG []
        (MEM [(["api"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N op)));
              (["index"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 16%N i)))]
        (EXT [row_repr p r])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["rw"], eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 8%N
          (if (op =? INSERT)%Z then 1 else
           if (op =? QUERY)%Z then Z.b2z (row_query r i) else
           if (op =? CLEAR)%Z then 0 else
           0))))]
        (EXT [row_repr p
          (if (op =? INSERT)%Z then row_insert r i else
           if (op =? QUERY)%Z then r else
           if (op =? CLEAR)%Z then row_clear r i else
           r)]))).

Lemma Row_tbl_bloom_body :
  fundef_satisfies_spec ge Row_tbl_bloom_fundef nil Row_tbl_bloom_spec.
Proof.
  split. 2 : {
    unfold Row_tbl_bloom_fundef.
    solve_modifies.
  }
  intros_fsh_bind.
  red.
  unfold Row_tbl_bloom_fundef.
  hoare_func_table.
  { (* I ignore the NOOP case here. I think we eventually need to say
      In op [NOOP; INSERT; QUERY; CLEAR]. *)
    instantiate (1 :=
        [(is_true (op =? INSERT)%Z, Some (mk_action_ref "act_insert" []));
         (not (is_true (op =? INSERT)%Z) /\ is_true (op =? QUERY)%Z,
            Some (mk_action_ref "act_query" []));
         (not (is_true (op =? INSERT)%Z) /\ not (is_true (op =? QUERY)%Z)
            /\ is_true (op =? CLEAR)%Z, Some (mk_action_ref "act_clear" []))]).
    admit.
  }
  constructor. {
    econstructor.
    { reflexivity. }
    { intros.
      replace (op =? INSERT)%Z with true.
      step_call Row_insert_body.
      3 : { entailer. }
      { auto. }
      { auto. }
      entailer.
    }
    { admit. }
  }
  constructor. {
    econstructor.
    { reflexivity. }
    { intros [].
      replace (op =? INSERT)%Z with false by hauto.
      replace (op =? QUERY)%Z with true.
      step_call Row_query_body.
      3 : { entailer. }
      { auto. }
      { auto. }
      entailer.
      destruct (row_query r i);
        apply sval_refine_refl.
    }
    { admit. }
  }
  constructor. {
    econstructor.
    { reflexivity. }
    { intros [? []].
      replace (op =? INSERT)%Z with false by hauto.
      replace (op =? QUERY)%Z with false by hauto.
      replace (op =? CLEAR)%Z with true.
      step_call Row_clear_body.
      3 : { entailer. }
      { auto. }
      { auto. }
      entailer.
    }
    { admit. }
  }
  constructor.
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
  step_call Row_tbl_bloom_body.
  4 : { entailer. }
  1-3 : auto.
  step.
  entailer.
Qed.
