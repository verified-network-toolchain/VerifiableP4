Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Semantics.Typing.ValueTyping.
Require Import Poulet4.P4light.Syntax.Value.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import Hammer.Plugin.Hammer.
Open Scope type_scope.

Section Members.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation mem := Semantics.mem.

(* Test whether sv has a WRITABLE field f. *)
(* Unions are not allowed in the has_field analysis, as their fields are not separated. *)
Definition has_field (f : ident) (sv : Sval) : bool :=
  match sv with
  | ValBaseStruct fields
  | ValBaseHeader fields (Some true) =>
      is_some (AList.get fields f)
  | _ => false
  end.

Definition get (f : ident) (sv : Sval) : Sval :=
  match sv with
  | ValBaseStruct fields
  | ValBaseHeader fields _
  | ValBaseUnion fields =>
      force ValBaseNull (AList.get fields f)
  | ValBaseStack headers next =>
      if String.eqb f "size" then
        ValBaseBit (P4Arith.to_loptbool 32%N (Zlength headers))
      else if String.eqb f "lastIndex" then
        (if (next =? 0)%N
        then (ValBaseBit (Zrepeat (@None bool) 32%Z))
        else (ValBaseBit (P4Arith.to_loptbool 32%N (Z.of_N (next - 1)))))
      else if String.eqb f "last" then
        force ValBaseNull (get_last_of_stack headers next)
      else if String.eqb f "next" then
        force ValBaseNull (get_next_of_stack headers next)
      else
        ValBaseNull
  | _ => ValBaseNull
  end.

Definition getv (f : ident) (v : Val) : Val :=
  match v with
  | ValBaseStruct fields
  | ValBaseHeader fields _
  | ValBaseUnion fields => force ValBaseNull (AList.get fields f)
  | _ => ValBaseNull
  end.

Definition updatev (f : ident) (f_sv : Val) (sv : Val) : Val :=
  match sv with
  | ValBaseStruct fields =>
      ValBaseStruct (force fields (AList.set fields f f_sv))
  | ValBaseHeader fields is_valid =>
      ValBaseHeader (force fields (AList.set fields f f_sv)) is_valid
  | _ => sv
  end.

Definition update (f : ident) (f_sv : Sval) (sv : Sval) : Sval :=
  match sv with
  | ValBaseStruct fields =>
      ValBaseStruct (force fields (AList.set fields f f_sv))
  | ValBaseHeader fields (Some true) =>
      ValBaseHeader (force fields (AList.set fields f f_sv)) (Some true)
  | ValBaseHeader fields is_valid (* (Some false) or None *) =>
      let uninit_f_sv' := uninit_sval_of_sval None f_sv in
      ValBaseHeader (force fields (AList.set fields f uninit_f_sv')) is_valid
  | ValBaseUnion fields =>
      let havoc_fields :=
        force []
          match f_sv with
          | ValBaseHeader hfields (Some true) =>
              lift_option_kv (kv_map (havoc_header (fun _ => Some false)) fields)
          | ValBaseHeader hfields (Some false) =>
              lift_option_kv (kv_map (havoc_header id) fields)
          | ValBaseHeader hfields None =>
              lift_option_kv (kv_map (havoc_header (fun _ => None)) fields)
          | _ => None
          end in
      ValBaseUnion (force havoc_fields (AList.set havoc_fields f f_sv))
  | _ => sv
  end.

Lemma get_some_get_set_same : forall {A} (l : AList.StringAList A) k (l' : AList.StringAList A) v1 v2,
  AList.get l k = Some v1 ->
  AList.get (force l' (AList.set l k v2)) k = Some v2.
Proof.
  intros.
  erewrite AList.get_some_set by eauto.
  apply AList.set_some_get.
Qed.

Lemma get_update_same : forall sv f f_sv,
  has_field f sv ->
  get f (update f f_sv sv) = f_sv.
Proof.
  intros.
  destruct sv; try solve [inv H].
  - unfold get, update, has_field in *.
    destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set_same by eauto.
      auto.
    + inv H.
  - destruct is_valid as [[] | ].
    * unfold get, update, has_field in *.
      destruct (AList.get fields f) eqn:?.
      + erewrite get_some_get_set_same by eauto.
        auto.
      + inv H.
    * inv H.
    * inv H.
Qed.

Lemma get_update_same' : forall sv f1 f2 f_sv,
  f1 = f2 ->
  has_field f2 sv ->
  get f1 (update f2 f_sv sv) = f_sv.
Proof.
  intros. subst. apply get_update_same; auto.
Qed.

Lemma get_set_diff : forall {A} (l : AList.StringAList A) k1 k2 v,
  k1 <> k2 ->
  AList.get (force l (AList.set l k2 v)) k1 = AList.get l k1.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct a as [k' v'].
    destruct (EquivUtil.StringEqDec k2 k') as [H_k2 | H_k2].
    + simpl. cbv in H_k2; subst.
      rewrite !AList.get_neq_cons; auto.
    + simpl. cbv in H_k2.
      destruct (AList.set l k2 v).
      * simpl.
        destruct (EquivUtil.StringEqDec k1 k') as [H_k1 | H_k1].
        ++rewrite !AList.get_eq_cons; auto.
        ++rewrite !AList.get_neq_cons; auto.
      * simpl.
        destruct (EquivUtil.StringEqDec k1 k') as [H_k1 | H_k1].
        ++rewrite !AList.get_eq_cons; auto.
        ++rewrite !AList.get_neq_cons; auto.
Qed.

Lemma get_update_diff : forall sv f1 f2 f_sv,
  has_field f2 sv ->
  f1 <> f2 ->
  get f1 (update f2 f_sv sv) = get f1 sv.
Proof.
  intros.
  destruct sv; try solve [inv H].
  - unfold get, update in *.
    rewrite get_set_diff; auto.
  - destruct is_valid as [[] | ].
    * unfold get, update in *.
      rewrite get_set_diff; auto.
    * inv H.
    * inv H.
Qed.

Lemma get_some_set_set_same : forall {A} (l : AList.StringAList A) k l' v1 v2 v3,
  AList.get l k = Some v1 ->
  AList.set (force l' (AList.set l k v2)) k v3 = AList.set l k v3.
Proof.
  intros.
  induction l.
  - inv H.
  - destruct a as [k' v'].
    simpl.
    destruct (EquivUtil.StringEqDec k k') as [H_k | H_k] eqn:H_k'.
    + simpl. cbv in H_k; subst.
      rewrite H_k'; auto.
    + rewrite AList.get_neq_cons in H by auto.
      specialize (IHl H).
      destruct (AList.set l k v2) eqn:?H.
      * simpl in *.
        rewrite H_k'.
        rewrite IHl; auto.
      * pose proof (AList.get_set_is_some l k v2).
        destruct (AList.get l k); destruct (AList.set l k v2); discriminate.
Qed.

Lemma get_some_set_set_same' : forall {A} (l : AList.StringAList A) k l' l'' l''' v1 v2 v3,
  AList.get l k = Some v1 ->
  force l'' (AList.set (force l' (AList.set l k v2)) k v3)
    = force l''' (AList.set l k v3).
Proof.
  intros.
  erewrite get_some_set_set_same; eauto.
  pose proof (AList.get_set_is_some l k v3).
  destruct (AList.get l k); destruct (AList.set l k v3); try discriminate.
  auto.
Qed.

Lemma update_update_same : forall sv f f_sv1 f_sv2,
  has_field f sv ->
  update f f_sv2 (update f f_sv1 sv) = update f f_sv2 sv.
Proof.
  intros.
  destruct sv; try solve [inv H].
  - unfold update, has_field in *.
    destruct (AList.get fields f) eqn:?.
    + erewrite (get_some_set_set_same' fields f); eauto.
    + inv H.
  - destruct is_valid as [[] | ].
    + unfold update, has_field in *.
      destruct (AList.get fields f) eqn:?.
      * erewrite (get_some_set_set_same' fields f); eauto.
      * inv H.
    + inv H.
    + inv H.
Qed.

Lemma get_set_some : forall f1 f2 (fields : AList.StringAList Sval) f_sv,
  is_some (AList.get fields f1) ->
  is_some (AList.get (force fields (AList.set fields f2 f_sv)) f1).
Proof.
  intros.
  destruct (string_dec f1 f2).
  + subst.
    destruct (AList.get fields f2) eqn:?; only 2 : inv H.
    erewrite get_some_get_set_same; eauto.
  + rewrite get_set_diff; auto.
Qed.

Lemma has_field_update : forall f1 f2 sv f_sv,
  has_field f1 sv ->
  has_field f1 (update f2 f_sv sv).
Proof.
  intros.
  destruct sv; try solve [inv H].
  - apply get_set_some; auto.
  - destruct is_valid as [[] | ]; try solve [inv H].
    apply get_set_some; auto.
Qed.

(* Auxiliary lemmas for sval_refine_get. *)

Lemma Forall2_True: forall {A B: Type} (l1: list A) (l2: list B),
    length l1 = length l2 -> Forall2 (fun _ _ => True) l1 l2.
Proof.
  induction l1; intros; destruct l2; simpl in H; inv H; constructor; auto.
Qed.

Lemma all_values_get_some_rel :
  forall {A B} (kvl : AList.StringAList A) (kvl' : AList.StringAList B) f rel v v',
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  AList.get kvl' f = Some v' ->
  rel v v'.
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H1 by auto.
      rewrite AList.get_eq_cons in H0 by auto.
      inv H1; inv H0.
      auto.
    + rewrite AList.get_neq_cons in H1 by auto.
      rewrite AList.get_neq_cons in H0 by auto.
      auto.
Qed.

Lemma all_values_get_some_is_some : forall {A} (kvl kvl' : AList.StringAList A) f rel v,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  is_some (AList.get kvl' f).
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H0 |- * by auto.
      auto.
    + rewrite AList.get_neq_cons in H0 |- * by auto.
      auto.
Qed.

Lemma all_values_get_some_exists_rel: forall {A} (kvl kvl' : AList.StringAList A) f rel v,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = Some v ->
  exists v', AList.get kvl' f = Some v' /\ rel v v'.
Proof.
  intros. pose proof H0. eapply all_values_get_some_is_some in H0; eauto.
  unfold is_some, isSome in H0. destruct (AList.get kvl' f) eqn:?H. 2: inv H0.
  eapply all_values_get_some_rel in H2; eauto.
Qed.

Lemma all_values_get_none_is_none :
  forall {A B} (kvl: AList.StringAList A) (kvl' : AList.StringAList B) f rel,
  AList.all_values rel kvl kvl' ->
  AList.get kvl f = None ->
  AList.get kvl' f = None.
Proof.
  intros.
  induction H; auto.
  destruct x as [kx vx]; destruct y as [ky vy].
  destruct H. simpl in H. subst ky.
  destruct (String.string_dec f kx) eqn:?.
  - rewrite AList.get_eq_cons in H0 by auto.
    rewrite AList.get_eq_cons by auto. inv H0.
  - rewrite AList.get_neq_cons in H0 by auto.
    rewrite AList.get_neq_cons by auto. auto.
Qed.

Lemma all_values_get_some_is_some' :
  forall {A B} (kvl : AList.StringAList A) (kvl' : AList.StringAList B) f rel v',
  AList.all_values rel kvl kvl' ->
  AList.get kvl' f = Some v' ->
  is_some (AList.get kvl f).
Proof.
  intros.
  induction H.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H. simpl in H. subst ky.
    destruct (String.string_dec f kx) eqn:?.
    + rewrite AList.get_eq_cons in H0 by auto.
      rewrite AList.get_eq_cons by auto.
      auto.
    + rewrite AList.get_neq_cons in H0 by auto.
      rewrite AList.get_neq_cons by auto.
      auto.
Qed.

Lemma all_values_get_is_some : forall {A} (kvl kvl' : AList.StringAList A) f rel,
  AList.all_values rel kvl kvl' ->
  is_some (AList.get kvl f) = is_some (AList.get kvl' f).
Proof.
  intros.
  destruct (AList.get kvl f) eqn:H_get1; destruct (AList.get kvl' f) eqn:H_get2; auto.
  - epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0; auto.
    rewrite H_get2 in H0. inv H0.
  - epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0; auto.
    rewrite H_get1 in H0. inv H0.
Qed.

Lemma all_values_key_unique : forall {A} (kvl kvl' : AList.StringAList A) rel,
    AList.all_values rel kvl kvl' ->
    AList.key_unique kvl -> AList.key_unique kvl'.
Proof.
  intros. induction H; auto. inv H0. destruct x. destruct (AList.get l s) eqn:?H.
  1: inv H3. simpl. destruct y. eapply all_values_get_none_is_none in H0; eauto.
  simpl in H. destruct H. subst s0. rewrite H0. apply IHForall2; auto.
Qed.

Lemma sval_refine_get_case1 : forall f kvs kvs',
  AList.all_values (exec_val bit_refine) kvs kvs' ->
  sval_refine (force ValBaseNull (AList.get kvs f)) (force ValBaseNull (AList.get kvs' f)).
Proof.
  intros.
  destruct (AList.get kvs f) eqn:H_get1; destruct (AList.get kvs' f) eqn:H_get2.
  + eapply all_values_get_some_rel; eauto.
  + epose proof (all_values_get_some_is_some _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0.
    rewrite H_get2 in H0. inv H0.
  + epose proof (all_values_get_some_is_some' _ _ _ _ _ ltac:(eauto) ltac:(eauto)) as H0.
    rewrite H_get1 in H0. inv H0.
  + constructor.
Qed.

Lemma sval_refine_get : forall sv sv' f,
  sval_refine sv sv' ->
  sval_refine (get f sv) (get f sv').
Proof.
  intros.
  inv H; try solve [constructor | apply sval_refine_get_case1; auto].
  - unfold get.
    destruct (String.eqb f "size").
    {
      apply Forall2_length in H0.
      pose proof (Zlength_correct lv).
      pose proof (Zlength_correct lv').
      replace (Zlength lv) with (Zlength lv') by lia.
      apply sval_refine_refl.
    }
    destruct (String.eqb f "lastIndex").
    { apply sval_refine_refl. }
    destruct (String.eqb f "last").
    { unfold get_last_of_stack, ListUtil.Znth_default.
      set (last := (Z.of_N (next - 1))). clearbody last.
      destruct ((0 <=? last) && (last <? Zlength lv)) eqn:H_last.
      { apply Forall2_forall_Znth in H0; destruct H0.
        list_simplify.
        apply H0; lia.
      }
      { apply Forall2_Zlength in H0.
        do 2 rewrite Znth_outofbounds by list_solve.
        apply sval_refine_refl.
      }
    }
    destruct (String.eqb f "next").
    { unfold get_next_of_stack, ListUtil.Znth_default.
      set (next' := (Z.of_N next)). clearbody next'.
      destruct ((0 <=? next') && (next' <? Zlength lv)) eqn:H_next'.
      { apply Forall2_forall_Znth in H0; destruct H0.
        list_simplify.
        apply H0; lia.
      }
      { apply Forall2_Zlength in H0.
        do 2 rewrite Znth_outofbounds by list_solve.
        apply sval_refine_refl.
      }
    }
    apply sval_refine_refl.
Qed.

Lemma Forall2_bit_refine_Some_same':
  forall l1 l2, Forall2 bit_refine (map Some l1) l2 -> l2 = map Some l1.
Proof.
  induction l1; intros.
  - inv H. simpl. auto.
  - destruct l2; simpl in H; inv H. inv H3. simpl. f_equal. now apply IHl1.
Qed.

Lemma Forall2_bit_refine_Some_same:
  forall l1 l2 : list bool, Forall2 bit_refine (map Some l1) (map Some l2) -> l1 = l2.
Proof.
  induction l1; intros.
  - inv H. symmetry in H0. apply map_eq_nil in H0. now subst.
  - destruct l2; simpl in H; inv H. inv H3. f_equal. now apply IHl1.
Qed.

#[local] Open Scope Z_scope.

Lemma sval_refine_to_loptbool_eq : forall w n1 n2,
  0 <= n1 < Z.pow 2 (Z.of_N w) ->
  0 <= n2 < Z.pow 2 (Z.of_N w) ->
  SvalRefine.sval_refine
    (Value.ValBaseBit (P4Arith.to_loptbool w n1))
    (Value.ValBaseBit (P4Arith.to_loptbool w n2)) ->
  n1 = n2.
Proof.
  intros. inv H1. unfold P4Arith.to_loptbool in H4.
  apply Forall2_bit_refine_Some_same in H4.
  pose proof (eq_refl (P4Arith.BitArith.lbool_to_val (P4Arith.to_lbool w n1) 1 0)).
  rewrite H4 in H1 at 2. rewrite !P4Arith.bit_to_lbool_back in H1.
  unfold P4Arith.BitArith.mod_bound, P4Arith.BitArith.upper_bound in H1.
  rewrite !Zmod_small in H1; auto.
Qed.

Lemma all_values_val_typ_set {bit: Type}:
  forall (fld : ident) (f_sv : @ValueBase bit) (typ : P4Type)
    (flds : AList.StringAList P4Type),
    AList.get flds fld = Some typ ->
    ⊢ᵥ f_sv \: typ ->
    forall vs : AList.AList ident (@ValueBase bit) eq,
      AList.all_values val_typ vs flds ->
      AList.all_values val_typ (force vs (AList.set vs fld f_sv)) flds.
Proof.
  intros fld f_sv typ flds H Ht vs H0.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H0 H).
  destruct (AList.get vs fld) eqn: ?H. 2: inversion H1. clear H1.
  destruct (AListUtil.AList_get_some_split _ _ _ H2) as [k [l1 [l2 [? [? ?]]]]].
  hnf in H1. subst k. subst vs.
  rewrite AListUtil.AList_set_app_cons_some; [| reflexivity | assumption ]. simpl.
  pose proof (firstn_skipn (length l1) flds).
  remember (firstn (length l1) flds) as fl1.
  remember (skipn (length l1) flds) as fl3. symmetry in H1.
  assert (length l1 = length fl1). {
    apply Forall2_length in H0. subst fl1.
    rewrite firstn_length_le; auto. rewrite app_length in H0.
    simpl in H0. rewrite <- H0. apply Nat.le_add_r. }
  rewrite H1 in H0. apply AListUtil.all_values_app in H0; auto.
  destruct H0. rewrite H1. apply AListUtil.all_values_app_inv; auto.
  pose proof (all_values_get_none_is_none _ _ _ _ H0 H4).
  rewrite H1 in H. rewrite AList.get_app_none in H; auto.
  destruct fl3. 1: inversion H5. destruct p as [fld' typ']. inversion H5. clear H5.
  subst x l y l'. clear Heqfl1 Heqfl3. destruct H10. simpl in H5, H7. subst fld'.
  rewrite AList.get_eq_cons in H; [|reflexivity]. inversion H. subst typ'.
  constructor; auto.
Qed.

Lemma update_struct_typ: forall fld f_sv sv (typ: P4Type) fields,
    AList.get (P4String.clear_AList_tags fields) fld = Some typ ->
    ⊢ᵥ f_sv \: typ ->
    ⊢ᵥ sv \: TypStruct fields ->
    ⊢ᵥ update fld f_sv sv \: TypStruct fields.
Proof.
  intros. inv H1. unfold update. constructor; auto.
  eapply all_values_val_typ_set; eauto.
Qed.

Lemma update_struct_valid_only: forall fld f_sv sv (typ: P4Type) fields,
    AList.get (P4String.clear_AList_tags fields) fld = Some typ ->
    ⊢ᵥ sv \: TypStruct fields ->
    val_to_sval_valid_only (updatev fld f_sv sv) =
      update fld (val_to_sval_valid_only f_sv) (val_to_sval_valid_only sv).
Proof.
  intros. inv H0. unfold updatev, update. simpl.
  rewrite <- P4String.key_unique_clear_AList_tags in H2.
  remember (P4String.clear_AList_tags fields) as flds. clear fields Heqflds.
  pose proof (all_values_get_some_is_some' _ _ _ _ _ H4 H).
  destruct (AList.get vs fld) eqn: ?H. 2: inversion H0. clear H0.
  destruct (AListUtil.AList_get_some_split _ _ _ H1) as [k [l1 [l2 [? [? ?]]]]].
  hnf in H0. subst k. subst vs.
  rewrite AListUtil.AList_set_app_cons_some; [| reflexivity | assumption ]. simpl.
  rewrite !kv_map_app. simpl kv_map.
  rewrite AListUtil.AList_set_app_cons_some; [reflexivity..|].
  apply AListUtil.not_in_fst_get_none. intros. hnf in H0. subst k'.
  pose proof (AListUtil.get_none_not_in_fst _ _ H5).
  rewrite kv_map_fst. apply H0. reflexivity.
Qed.

Lemma updatev_struct_typ: forall fld f_sv sv (typ: P4Type) fields,
    AList.get (P4String.clear_AList_tags fields) fld = Some typ ->
    ⊢ᵥ f_sv \: typ ->
    ⊢ᵥ sv \: TypStruct fields ->
    ⊢ᵥ updatev fld f_sv sv \: TypStruct fields.
Proof.
  intros. inv H1. unfold update. constructor; auto.
  eapply all_values_val_typ_set; eauto.
Qed.

Lemma updatev_fld_diff_comm: forall fld1 fld2 fsv1 fsv2 v,
    fld1 <> fld2 ->
    updatev fld1 fsv1 (updatev fld2 fsv2 v) = updatev fld2 fsv2 (updatev fld1 fsv1 v).
Proof.
  intros.
  assert (forall fields, force (force fields (AList.set fields fld2 fsv2))
                      (AList.set (force fields (AList.set fields fld2 fsv2)) fld1 fsv1) =
                      force (force fields (AList.set fields fld1 fsv1))
                        (AList.set (force fields (AList.set fields fld1 fsv1)) fld2 fsv2)). {
    intros. destruct (AList.get fields fld1) eqn:?; destruct (AList.get fields fld2) eqn:?.
    - destruct (AListUtil.AList_get_some_split _ _ _ Heqo) as [k [l1 [l2 [? [? ?]]]]].
      hnf in H0. symmetry in H0. subst.
      rewrite (AListUtil.AList_set_app_cons_some l1 fld1 fld1); auto. 2: reflexivity. simpl.
      destruct (AList.get l1 fld2) eqn:?.
      + destruct (AListUtil.AList_get_some_split _ _ _ Heqo1) as [k [l3 [l4 [? [? ?]]]]].
        hnf in H0. symmetry in H0. subst. rewrite <- !app_assoc, <- !app_comm_cons in *.
        rewrite AList.get_app_none in Heqo0 by assumption.
        rewrite AList.get_eq_cons in Heqo0 by reflexivity. inv Heqo0.
        rewrite !AListUtil.AList_set_app_cons_some with (k2 := fld2); auto. 2,3: reflexivity.
        simpl. rewrite app_comm_cons, app_assoc, AListUtil.AList_set_app_cons_some.
        * simpl. rewrite <- app_assoc, <- app_comm_cons. reflexivity.
        * reflexivity.
        * apply AListUtil.AList_get_app_none_inv in H2. destruct H2.
          apply AListUtil.AList_get_cons_none_inv in H1. destruct H1.
          rewrite AList.get_app_none by assumption. rewrite AList.get_neq_cons; assumption.
      + rewrite AList.get_app_none in Heqo0 by assumption.
        rewrite AList.get_neq_cons in Heqo0 by (symmetry; apply H).
        destruct (AListUtil.AList_get_some_split _ _ _ Heqo0) as [k [l3 [l4 [? [? ?]]]]].
        hnf in H0. symmetry in H0. subst.
        assert (forall fv, AList.get (l1 ++ (fld1, fv) :: l3) fld2 = None). {
          intros. rewrite AList.get_app_none by assumption. rewrite AList.get_neq_cons; auto.
          symmetry. apply H. }
        rewrite !app_comm_cons, !app_assoc, !AListUtil.AList_set_app_cons_some; auto.
        2, 3: reflexivity. simpl. rewrite <- !app_assoc, <- !app_comm_cons.
        rewrite AListUtil.AList_set_app_cons_some; auto. reflexivity.
    - rewrite (AList.get_none_set fields _ fsv2); auto. simpl.
      rewrite !(AList.get_some_set fields _ v0 fsv1); auto. simpl.
      rewrite (AList.get_none_set (AList.set_some _ _ _) fld2). 1: reflexivity.
      rewrite <- Heqo0. apply AList.set_some_get_miss. apply H.
    - rewrite (AList.get_none_set fields _ fsv1); auto. simpl.
      rewrite (AList.get_some_set fields _ v0 fsv2); auto. simpl.
      rewrite (AList.get_none_set (AList.set_some _ _ _) fld1). 1: reflexivity.
      rewrite <- Heqo. apply AList.set_some_get_miss. symmetry. apply H.
    - rewrite (AList.get_none_set fields _ fsv1); auto. simpl.
      rewrite (AList.get_none_set fields _ fsv2); auto. simpl.
      rewrite (AList.get_none_set fields _ fsv1); auto. }
  destruct v; simpl; try reflexivity; f_equal; apply H0.
Qed.

Lemma updatev_fld_same: forall fld fsv1 fsv2 v,
    updatev fld fsv1 (updatev fld fsv2 v) = updatev fld fsv1 v.
Proof.
  intros.
  assert (forall fields, force (force fields (AList.set fields fld fsv2))
                      (AList.set (force fields (AList.set fields fld fsv2)) fld fsv1) =
                      force fields (AList.set fields fld fsv1)). {
    intros. destruct (AList.get fields fld) eqn:?.
    - destruct (AListUtil.AList_get_some_split _ _ _ Heqo) as [k [l1 [l2 [? [? ?]]]]].
      hnf in H. symmetry in H. subst.
      rewrite !AListUtil.AList_set_app_cons_some; auto. 2, 3: reflexivity. simpl.
      rewrite AListUtil.AList_set_app_cons_some; auto. reflexivity.
    - rewrite !AList.get_none_set; auto. }
  destruct v; simpl; try reflexivity; f_equal; apply H.
Qed.

End Members.
