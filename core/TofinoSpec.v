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
(* I don't define f as (Val -> Val) because this function should be partial. *)
Definition RegisterAction_apply_spec {A} (p : path) (repr : A -> Val) (f : A -> A) (retv : A -> Sval) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (old_value : A),
      PRE
        (ARG [eval_val_to_sval (repr old_value)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [eval_val_to_sval (repr (f old_value));
                  retv old_value]
           ValBaseNull
        (MEM []
        (EXT []))).

Definition RegisterAction_apply_spec' {A} (p : path) (valid : A -> Prop) (repr : A -> Val) (f : A -> A) (retv : A -> Sval) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (old_value : A) (H_old_value : valid old_value),
      PRE
        (ARG [eval_val_to_sval (repr old_value)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [eval_val_to_sval (repr (f old_value));
                  retv old_value]
           ValBaseNull
        (MEM []
        (EXT []))).

(* Remove the content type constaint of register, right? *)

Definition RegisterAction_execute_spec : func_spec :=
  WITH A p (* path *) index_w typ s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (index_w, typ, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd repr apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : func_sound am_ge apply_fd nil
          (RegisterAction_apply_spec (A := A) p repr apply_f apply_retv)),
    PATH p
    MOD None [r]
    WITH (c : list Val) (i : Z)
      (H_c : Zlength c = s)
      (H_i : 0 <= i < s)
      old_v
      (H_old_v : Znth i c = repr old_v),
      PRE
        (ARG [P4Bit index_w i]
        (MEM []
        (EXT [ExtPred.singleton r (Tofino.ObjRegister c)])))
      POST
        (ARG_RET [] (apply_retv old_v)
        (MEM []
        (EXT [ExtPred.singleton r
            (Tofino.ObjRegister (upd_Znth i c (repr (apply_f old_v))))]))).

Definition RegisterAction_execute_spec' : func_spec :=
  WITH A p (* path *) index_w typ s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (index_w, typ, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd apply_valid repr apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : func_sound am_ge apply_fd nil
          (RegisterAction_apply_spec' (A := A) p apply_valid repr apply_f apply_retv)),
    PATH p
    MOD None [r]
    WITH (c : list Val) (i : Z)
      (H_c : Zlength c = s)
      (H_i : 0 <= i < s)
      old_v
      (H_old_v : Znth i c = repr old_v)
      (H_valid : apply_valid old_v),
      PRE
        (ARG [P4Bit index_w i]
        (MEM []
        (EXT [ExtPred.singleton r (Tofino.ObjRegister c)])))
      POST
        (ARG_RET [] (apply_retv old_v)
        (MEM []
        (EXT [ExtPred.singleton r
            (Tofino.ObjRegister (upd_Znth i c (repr (apply_f old_v))))]))).

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

Lemma RegisterAction_execute_body' :
  func_sound ge execute_fundef nil RegisterAction_execute_spec'.
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
          inv H7.
          eapply (proj2 H_apply_body) in H1.
          solve_modifies.
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
  rewrite H_old_v in H8.
  assert (new_value = repr (apply_f old_v)
      /\ sval_to_val read_ndetbit (apply_retv old_v) retv). {
    clear -H_apply_body H_valid H8.
    inv H8.
    eapply (proj1 H_apply_body old_v) in H0.
    2 : { auto. }
    2 : {
      split.
      2 : { split; constructor. }
      inv H. inv H6.
      apply val_to_sval_iff in H4.
      subst.
      constructor; only 2 : constructor.
      apply sval_refine_refl.
    }
    clear H.
    destruct H0.
    inv H. inv H6. inv H7.
    inv H1. inv H8. inv H9.
    eapply sval_refine_sval_to_val_n_trans in H6. 2 : eapply H4. clear H4.
    eapply sval_refine_sval_to_val_n_trans in H5. 2 : eapply H3. clear H3.
    split.
    { eapply sval_to_val_n_eval_val_to_sval_eq; eauto. }
    { auto. }
  }
  clear H8.
  destruct H; subst.
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

Lemma RegisterAction_execute_body :
  func_sound ge execute_fundef nil RegisterAction_execute_spec.
Proof.
  intros_fs_bind.
  assert (H_apply_body' : func_sound am_ge apply_fd []
      (RegisterAction_apply_spec' p (fun _ => True) repr apply_f apply_retv)). {
    refine_function H_apply_body.
    entailer.
    entailer.
  }
  split.
  2 : {
    unshelve eapply (proj2 (RegisterAction_execute_body' _ _ _ _ _ _ _ _ _ _ (fun _ => True) _ _ _ _ _));
      eauto.
  }
  intros_fsh_bind.
  eapply hoare_func_post.
  { eapply hoare_func_pre.
    2 : {
      unshelve eapply (proj1 (RegisterAction_execute_body' _ _ _ _ s _ _ _ _ _ (fun _ => True) _ _ _ _ _));
        eauto.
    }
    entailer.
  }
  entailer.
Qed.

Definition extend_hash_output_Z (hash_w : N) (output : list bool) : Z :=
  let output_w := N.of_nat (List.length output) in
  let num_copies := N.div hash_w output_w in
  let num_remainder := Z.of_N (N.modulo hash_w output_w) in
  let lsbs := repeat_concat_list (N.to_nat num_copies) output in
  let msbs := sublist (Z.of_N output_w - num_remainder) (Z.of_N output_w) output in
  BitArith.lbool_to_val (app msbs lsbs) 1 0.

Definition dummy_Z : Z.
Proof. exact 0. Qed.

Definition hash_Z (hash_w : N) (poly : CRC_polynomial) (v : Val) : Z :=
  match convert_to_bits v with
  | Some input =>
      extend_hash_output_Z hash_w (Hash.compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_hex (CRCP_coeff poly)) 
          (lbool_to_hex (CRCP_init poly)) (lbool_to_hex (CRCP_xor poly))
          (CRCP_reversed poly) (CRCP_reversed poly) input)
  | None =>
      dummy_Z
  end.

Definition Hash_get_fundef : (@fundef tags_t) := FExternal "Hash" "get".

Definition Hash_get_spec : func_spec :=
  WITH p (* path *) hash_w poly
      (H_p : PathMap.get p (ge_ext ge) = Some (EnvHash (hash_w, poly))),
    PATH p
    MOD None []
    WITH (v : Val),
      PRE
        (ARG [eval_val_to_sval v]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] (P4Bit hash_w (hash_Z hash_w poly v))
        (MEM []
        (EXT []))).

Lemma Hash_get_body targs :
  func_sound ge Hash_get_fundef targs Hash_get_spec.
Proof.
  intros_fs_bind.
  split.
  2 : {
    red. intros.
    inv H.
    inv H5. inv H.
    apply modifies_refl.
  }
  intros_fsh_bind.
  hnf; intros.
  inv H0. inv H6.
  inv H0.
  eapply eq_trans in H1; only 2 : (symmetry; apply H_p).
  symmetry in H1; inv H1.
  unfold hash_Z.
  destruct H as [? []].
  hnf in H. inv H. inv H8.
  assert (y = eval_val_to_sval v) by (clear; admit).
  subst y.
  inv H3. clear H9.
  apply sval_to_val_eval_val_to_sval_iff in H7. 2 : {
    clear; sauto lq: on.
  }
  subst.
  rewrite H2. clear H2.
  split.
  { inv H12. constructor. }
  split.
  { apply eval_val_to_sval_ret_denote.
    unfold extend_hash_output_Z.
    unfold P4Bit.
    unfold to_loptbool.
    rewrite to_lbool_lbool_to_val'. 2 : {
      clear.
      generalize (Hash.compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_hex (CRCP_coeff poly))
                    (lbool_to_hex (CRCP_init poly)) (lbool_to_hex (CRCP_xor poly))
                    (CRCP_reversed poly) (CRCP_reversed poly) input).
      intros.
      replace (N.of_nat (Datatypes.length b)) with (Z.to_N (Zlength b)). 2 : {
        rewrite Zlength_correct. lia.
      }
      clear; admit.
    }
    reflexivity.
  }
  repeat constructor.
Admitted.

End TofinoSpec.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) =>
  (refine (proj2 (Hash_get_body _ _ _ _ _ _)); try exact (@nil _); compute; reflexivity) : func_specs.
