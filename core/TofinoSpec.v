Require Import Coq.Strings.String.
Require Import BinNat.
Require Import BinInt.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Poulet4.Utils.P4Arith.
Require Import ProD3.core.Core.
Require Import Hammer.Plugin.Hammer.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Section TofinoSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation Expression := (@Expression tags_t).

Instance target : @Target tags_t Expression := Tofino.

Variable ge : genv.
Variable am_ge : genv.

Lemma hoare_extern_match_list_intro : forall keys_match_kinds entryvs,
  hoare_extern_match_list keys_match_kinds entryvs (extern_matches keys_match_kinds entryvs).
Proof.
  intros. unfold hoare_extern_match_list.
  simpl. unfold extern_match.
  remember (extern_matches keys_match_kinds entryvs) as cases.
  clear Heqcases.
  induction cases.
  - auto.
  - destruct a.
    destruct b; auto.
Qed.

Open Scope func_spec.

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

Definition RegisterAction_execute_spec : func_spec :=
  WITH p (* path *) index_w w (* width *) s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (w, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : func_sound am_ge apply_fd nil
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

Definition execute_fundef : (@fundef tags_t) := FExternal "RegisterAction" "execute".

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
  func_sound ge execute_fundef nil RegisterAction_execute_spec.
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
    change (@extern_object tags_t Expression (@extern_sem tags_t Expression target))
      with (@Tofino.object tags_t Expression) in H.
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
      rewrite Znat.N2Z.id in H4.
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

End TofinoSpec.

Ltac get_am_fd ge am_ge p :=
  let am_sem := eval compute -[am_ge] in
    (force Tofino.EnvPin (PathMap.get p (ge_ext ge))) in
  lazymatch am_sem with
  | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
      exact fd
  end.

Ltac build_execute_body ge index_w body :=
  (* get spec from body *)
  lazymatch type of body with
  | func_sound ?am_ge ?fd _ ?spec =>
    (* unfold spec *)
    let spec :=
      lazymatch spec with
      | RegisterAction_apply_spec _ _ _ _ =>
          spec
      | _ =>
          eval unfold spec in spec
      end in
    lazymatch spec with
    | RegisterAction_apply_spec ?p ?w ?f ?retv =>
        let r := eval compute in (PathMap.get p (ge_ext ge)) in
        let r := lazymatch r with (Some (Tofino.EnvRegAction ?r)) => r end in
        let s := eval compute in (PathMap.get r (ge_ext ge)) in
        let s := lazymatch s with (Some (Tofino.EnvRegister (_, ?s))) => s end in
        exact (RegisterAction_execute_body ge am_ge p index_w w s r eq_refl eq_refl ltac:(lia)
          fd f retv eq_refl body)
    | _ => fail "body is not a body proof for apply"
    end
  | _ => fail "body is not a body proof"
  end.
