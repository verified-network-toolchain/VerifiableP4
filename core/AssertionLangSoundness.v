Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.AssertionLang.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section AssertionLangSoundness.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation Lval := (@Lval tags_t).
Notation SemLval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation semlval_equivb := (@Semantics.lval_equivb tags_t).
Notation mem := (@Semantics.mem tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Notation alist_get l s := (AList.get l (P4String.Build_t _ default s)).

Variable this : path.

Notation mem_eval_read := (mem_eval_read this).
Notation mem_is_valid_field := (mem_is_valid_field this).
Notation satisfies_unit := (satisfies_unit this).
Notation to_shallow_assertion := (to_shallow_assertion this).

Lemma mem_eval_read_snoc m loc fl f :
  mem_eval_read m (loc, fl ++ [f]) =
    extract_option (mem_eval_read m (loc, fl)) f .
Proof.
  simpl. rewrite fold_left_app. reflexivity.
Qed.

Lemma not_isNil_snoc {A} (l : list A) (x : A) :
  ~~(isNil (l ++ [x])).
Proof.
  induction l; auto.
Qed.

Lemma mem_is_valid_field_parent m loc fl1 f :
  mem_is_valid_field m (loc, fl1 ++ [f]) ->
  mem_is_valid_field m (loc, fl1).
Proof.
  unfold mem_is_valid_field. rewrite mem_eval_read_snoc.
  destruct (mem_eval_read m (loc, fl1)); hauto use: Reflect.orE, is_true_true unfold: isNil, is_true, app, extract_option, orb, isSome.
Qed.

Fixpoint semlval_to_lval (slv : SemLval) : option Lval :=
  match slv with
  | MkValueLvalue (ValLeftName _ loc) _ => Some (loc, nil)
  | MkValueLvalue (ValLeftMember slv member) _ =>
      let olv := semlval_to_lval slv in
      option_map (map_snd (cons (P4String.str member))) olv
  | _ => None
  end.

Definition dummy_type : P4Type := TypBool.

Definition lval_to_semlval (lv : Lval) : SemLval :=
  let (loc, fl) := lv in
  let acc := MkValueLvalue (ValLeftName (BareName (P4String.Build_t tags_t default "")) loc) dummy_type in
  let step acc f :=
      MkValueLvalue (ValLeftMember acc (P4String.Build_t tags_t default f)) dummy_type in
  fold_left step fl acc.

Lemma lval_to_semlval_snoc loc fl f :
  lval_to_semlval (loc, fl ++ [f]) =
    MkValueLvalue (ValLeftMember (lval_to_semlval (loc, fl)) (P4String.Build_t tags_t default f)) dummy_type.
Proof.
  simpl. rewrite fold_left_app. reflexivity.
Qed.

Lemma mem_eval_read_sound_1 : forall st lv v,
  mem_eval_read (fst st) lv = Some v ->
  exec_read this st (lval_to_semlval lv) v.
Proof.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  induction (rev fl) as [ | hd tl]; intros * H_mem_eval_read.
  - apply exec_read_name, H_mem_eval_read.
  - simpl rev in *. rewrite lval_to_semlval_snoc. rewrite mem_eval_read_snoc in H_mem_eval_read.
    apply exec_read_by_member.
    destruct (mem_eval_read (fst st) (loc, rev tl)) as [[] | ]; only 1-12, 15-20 : solve [inversion H_mem_eval_read].
    + eapply exec_read_member_struct; only 1 : (apply IHtl; reflexivity).
      apply H_mem_eval_read.
    + eapply exec_read_member_header; only 1 : (apply IHtl; reflexivity).
      destruct is_valid; only 2 : inversion H_mem_eval_read.
      apply read_header_field_intro, H_mem_eval_read.
Qed.

Lemma mem_eval_read_sound : forall st lv v,
  mem_eval_read (fst st) lv = Some v ->
  forall v', exec_read this st (lval_to_semlval lv) v' ->
    v' = v.
Proof.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  induction (rev fl) as [ | hd tl]; intros * H_mem_eval_read * H_exec_read.
  - inv H_exec_read.
    assert (Some v' = Some v) by (eapply eq_trans; only 2 : apply H_mem_eval_read; eauto).
    sfirstorder.
  - simpl rev in *. rewrite lval_to_semlval_snoc in H_exec_read. rewrite mem_eval_read_snoc in H_mem_eval_read.
    destruct (mem_eval_read (fst st) (loc, rev tl)) as [fields | ]; only 2 : solve [inversion H_mem_eval_read].
    specialize (IHtl fields ltac:(reflexivity)).
    destruct fields; only 1-12, 15-19 : solve [inversion H_mem_eval_read]; simpl in H_mem_eval_read.
    + inv H_exec_read. pinv @exec_read_member; specialize (IHtl _ H0); only 1, 3 : solve [inversion IHtl].
      scongruence.
    + destruct is_valid; only 2 : inversion H_mem_eval_read.
      inv H_exec_read. pinv @exec_read_member; specialize (IHtl _ H0); only 2, 3 : solve [inversion IHtl].
      destruct is_valid; only 2 : inversion IHtl.
      pinv @read_header_field.
      scongruence.
Qed.

Lemma val_eqb_eq (v1 v2 : Val) :
  val_eqb v1 v2 -> v1 = v2.
Proof.
  intros H_val_eqb.
  destruct v1; destruct v2; simpl in H_val_eqb; try discriminate.
  - constructor.
  - clear H. sfirstorder use: Bool.eqb_prop unfold: is_true.
  - hauto b: on.
  - hauto b: on.
  - hauto b: on.
Qed.

Axiom loc_to_val_update_val_by_loc_same : forall st loc1 loc2 v,
  locator_equivb loc1 loc2 ->
  loc_to_val this loc1 (Semantics.update_val_by_loc this st loc2 v) = Some v.

Axiom loc_to_val_update_val_by_loc_diff : forall st p1 p2 v,
  ~~ path_equivb p1 p2 ->
  loc_to_val this (LInstance p1) (Semantics.update_val_by_loc this st (LInstance p2) v) =
    loc_to_val this (LInstance p1) st.

Axiom p4string_equivb_refl : forall (s : P4String),
  P4String.equivb s s.

Axiom p4string_equivb_symm : forall (s1 s2 : P4String),
  P4String.equivb s1 s2 = P4String.equivb s2 s1.

Axiom p4string_equivb_trans : forall (s1 s2 s3 : P4String),
  P4String.equivb s1 s2 -> P4String.equivb s2 s3 -> P4String.equivb s1 s3.

Axiom path_equivb_refl : forall (p : path),
  path_equivb p p.

Axiom path_equivb_symm : forall (p1 p2 : path),
  path_equivb p1 p2 = path_equivb p2 p1.

Axiom path_equivb_trans : forall (p1 p2 p3 : path),
  path_equivb p1 p2 -> path_equivb p2 p3 -> path_equivb p1 p3.

Axiom locator_equivb_refl : forall (loc : Locator),
  locator_equivb loc loc.

Axiom locator_equivb_symm : forall (loc1 loc2 : Locator),
  locator_equivb loc1 loc2 = locator_equivb loc2 loc1.

Axiom locator_equivb_trans : forall (loc1 loc2 loc3 : Locator),
  locator_equivb loc1 loc2 -> locator_equivb loc2 loc3 -> locator_equivb loc1 loc3.

Axiom loc_no_overlapping_symm : forall (loc1 loc2 : Locator),
  loc_no_overlapping loc1 loc2 = loc_no_overlapping loc2 loc1.

Axiom lval_no_overlapping_symm : forall (lv1 lv2 : Lval),
  lval_no_overlapping lv1 lv2 = lval_no_overlapping lv2 lv1.

Axiom lval_equivb_symm : forall (lv1 lv2 : Lval),
  lval_equivb lv1 lv2 = lval_equivb lv2 lv1.

(* This axiom is provable if tags_t is a unit type. *)
Axiom path_equivb_eq : forall (p1 p2 : path), path_equivb p1 p2 -> p1 = p2.

Axiom locator_equivb_eq : forall (loc1 loc2 : Locator), locator_equivb loc1 loc2 -> loc1 = loc2.

Axiom lval_equivb_eq : forall (lv1 lv2 : Lval), lval_equivb lv1 lv2 -> lv1 = lv2.

Lemma implies_unit_sound m a a_unit :
  to_shallow_assertion a m ->
  implies_unit a a_unit ->
  satisfies_unit m a_unit.
Proof.
  clear H.
  intros H_pre H_implies_unit.
  induction a as [ | hd tl].
  - inversion H_implies_unit.
  - destruct (assretion_unit_equivb hd a_unit) eqn:H_assretion_unit_equivb.
    + assert (satisfies_unit m hd) by (clear -H_pre; sfirstorder).
      destruct hd as [lv1 v1 | lv1 v1]; destruct a_unit as [lv2 v2 | lv2 v2];
        only 2-4 : sfirstorder.
      simpl in H_assretion_unit_equivb.
      assert (lv1 = lv2) by (apply lval_equivb_eq; hauto unfold: is_true, andb).
      assert (v1 = v2) by (apply val_eqb_eq; hauto unfold: is_true, andb).
      sfirstorder.
    + apply IHtl.
      * sfirstorder.
      * hauto.
Qed.

Lemma implies_sound m pre post :
  to_shallow_assertion pre m ->
  implies pre post ->
  to_shallow_assertion post m.
Proof.
  intros H_pre H_implies.
  induction post as [ | hd tl].
  - exact I.
  - split.
    + apply implies_unit_sound with (a := pre); only 1 : assumption.
      hauto b: on.
    + apply IHtl. hauto b: on.
Qed.

Fixpoint eval_write (a : assertion) (lv : Lval) (v : Val) : assertion :=
  match a with
  | hd :: tl =>
      match hd with
      | AVal hd_lv hd_v =>
          if lval_equivb lv hd_lv then
            (AVal lv v) :: tl
          else
            hd :: eval_write tl lv v
      | AType hd_lv hd_type =>
          hd :: eval_write tl lv v
      end
  | [] => [AVal lv v]
  end.

Lemma exec_write_1 st lv v st' :
  exec_write this st (lval_to_semlval lv) v st' ->
  exists v',
    st' = update_val_by_loc this st (fst lv) v'.
Proof.
  destruct lv as [loc fl]. simpl fst.
  rewrite <- (rev_involutive fl).
  generalize dependent v.
  induction (rev fl) as [ | hd tl]; intros * H_exec_write.
  - sauto lq: on.
  - simpl rev in H_exec_write; rewrite lval_to_semlval_snoc in H_exec_write.
    inv H_exec_write.
    destruct (IHtl _ ltac:(eassumption)).
    sfirstorder.
Qed.

Axiom alist_get_equiv : forall {V} (l : P4String.AList tags_t V) (s1 s2 : P4String),
  P4String.equivb s1 s2 ->
  AList.get l s1 = AList.get l s2.

Axiom alist_get_set_same : forall {V} (l l' : P4String.AList tags_t V) (s1 s2 : P4String) v,
  AList.set l s2 v = Some l' ->
  P4String.equivb s1 s2 ->
  AList.get l' s1 = Some v.

Axiom alist_get_set_diff : forall {V} (l l' : P4String.AList tags_t V) (s1 s2 : P4String) v,
  AList.set l s2 v = Some l' ->
  ~~P4String.equivb s1 s2 ->
  AList.get l' s1 = AList.get l s1.

Axiom P4String_equivb_same : forall (tags1 tags2 : tags_t) s1 s2,
  s1 = s2 ->
  P4String.equivb (P4String.Build_t _ tags1 s1) (P4String.Build_t _ tags2 s2).

Axiom P4String_equivb_diff : forall (tags1 tags2 : tags_t) s1 s2,
  s1 <> s2 ->
  ~~(P4String.equivb (P4String.Build_t _ tags1 s1) (P4String.Build_t _ tags2 s2)).

Hint Resolve alist_get_set_same alist_get_set_diff P4String_equivb_same P4String_equivb_diff : core.

Lemma satisfies_unit_helper_header st loc fl f fields v :
  satisfies_unit st (AVal (loc, fl) (ValBaseHeader fields true)) ->
  alist_get fields f = Some v ->
  satisfies_unit st (AVal (loc, fl ++ [f]) v).
Proof.
  intros H_satisfies_unit H_alist_get.
  simpl. rewrite fold_left_app, H_satisfies_unit.
  apply H_alist_get.
Qed.

Lemma satisfies_unit_helper_struct st loc fl f fields v :
  satisfies_unit st (AVal (loc, fl) (ValBaseStruct fields)) ->
  alist_get fields f = Some v ->
  satisfies_unit st (AVal (loc, fl ++ [f]) v).
Proof.
  intros H_satisfies_unit H_alist_get.
  simpl. rewrite fold_left_app, H_satisfies_unit.
  apply H_alist_get.
Qed.

Lemma exec_write_satisfies_unit st lv v st' :
  mem_is_valid_field (fst st) lv ->
  exec_write this st (lval_to_semlval lv) v st' ->
  satisfies_unit (fst st') (AVal lv v).
Proof.
  intros * H_mem_is_valid_field H_exec_write.
  revert H_mem_is_valid_field H_exec_write.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  generalize dependent v.
  induction (rev fl) as [ | hd tl]; intros * H_mem_is_valid_field H_exec_write.
  - inv H_exec_write. apply loc_to_val_update_val_by_loc_same, locator_equivb_refl.
  - simpl rev in H_exec_write; rewrite lval_to_semlval_snoc in H_exec_write.
    inv H_exec_write.
    simpl rev in H_mem_is_valid_field.
    apply mem_is_valid_field_parent in H_mem_is_valid_field as H_mem_is_valid_field'.
    unfold mem_is_valid_field in H_mem_is_valid_field.
    rewrite mem_eval_read_snoc in H_mem_is_valid_field.
    assert (~~(isNil (rev tl ++ [hd]))) by (apply not_isNil_snoc).
    assert (mem_eval_read (fst st) (loc, rev tl) = Some v0) as H_mem_eval_read. {
      destruct (mem_eval_read (fst st) (loc, rev tl)) eqn:H_mem_eval_read; only 2 : hauto b: on.
      f_equal. symmetry. eapply mem_eval_read_sound; eassumption.
    }
    pinv @update_member.
    + pinv @write_header_field.
      rewrite H_mem_eval_read in H_mem_is_valid_field.
      destruct is_valid; only 2 : (hauto b: on).
      unfold satisfies_unit.
      eapply satisfies_unit_helper_header; only 1 : (apply IHtl; eassumption).
      eapply alist_get_set_same; eauto.
    + eapply satisfies_unit_helper_struct; only 1 : (apply IHtl; eassumption).
      eapply alist_get_set_same; eauto.
    + rewrite H_mem_eval_read in H_mem_is_valid_field.
      hauto b: on.
Qed.

(* Things will be easier if we use the reversed order in exec_write. *)

Lemma satisfies_unit_child m loc fl f fields v :
  satisfies_unit m (AVal (loc, fl) fields) ->
  extract_option (Some fields) f = Some v ->
  satisfies_unit m (AVal (loc, fl ++ [f]) v).
Proof.
  simpl. rewrite fold_left_app. hauto lq: on.
Qed.

(* Proving the following lemma should be enough. For exec_write_no_overlapping_unit,
  it is easy to remove a last field from either lv1 or lv2, so we can reach the part that
  only one field is different. *)

Lemma exec_write_2 st loc fl f1 f2 v1 v2 st' :
  f1 <> f2 ->
  satisfies_unit (fst st) (AVal (loc, fl ++ [f1]) v1) ->
  exec_write this st (lval_to_semlval (loc, fl ++ [f2])) v2 st' ->
  satisfies_unit (fst st') (AVal (loc, fl ++ [f1]) v1).
Proof.
  intros H_neq H_pre H_exec_write.
  simpl rev in H_exec_write; rewrite lval_to_semlval_snoc in H_exec_write.
  inv H_exec_write.
  eapply satisfies_unit_child with (m := (fst st')). 1 : eapply exec_write_satisfies_unit with (st := st).
  - eapply mem_is_valid_field_parent with (f := f1). unfold satisfies_unit in H_pre.
    hauto b: on.
  - eassumption.
  - unfold satisfies_unit in H_pre.
    rewrite mem_eval_read_snoc in H_pre.
    assert (mem_eval_read (fst st) (loc, fl) = Some v) as H_mem_eval_read. {
      destruct (mem_eval_read (fst st) (loc, fl)) eqn:H_mem_eval_read;
        (* conflict with H_mem_is_valid_field' *)
        only 2 : hauto.
      f_equal. symmetry. eapply mem_eval_read_sound; eassumption.
    }
    rewrite H_mem_eval_read in H_pre.
    pinv @update_member.
    + destruct is_valid; only 2 : sfirstorder.
      pinv @write_header_field. simpl.
      rewrite <- H_pre.
      apply (alist_get_set_diff _ _ _ _ _ H7).
      srun eauto use: P4String_equivb_diff unfold: default.
    + rewrite <- H_pre.
      apply (alist_get_set_diff _ _ _ _ _ H0).
      srun eauto use: P4String_equivb_diff unfold: default.
    + inv H_pre.
Qed.

Lemma exec_write_3 st loc fl1 fl2 v st' :
  exec_write this st (lval_to_semlval (loc, fl1 ++ fl2)) v st' ->
  exists v',
    exec_write this st (lval_to_semlval (loc, fl1)) v' st'.
Proof.
  generalize dependent v.
  rewrite <- (rev_involutive fl2).
  induction (rev fl2) as [ | hd tl]; intros * H_exec_write.
  - simpl rev in H_exec_write. rewrite app_nil_r in H_exec_write. sfirstorder.
  - simpl rev in H_exec_write. rewrite app_assoc in H_exec_write.
    unfold lval_to_semlval in *. rewrite fold_left_app in H_exec_write.
    inv H_exec_write; eauto.
Qed.

Lemma exec_write_no_overlapping_unit_case_1 st loc fl f1 f2 v1 v2 st' :
  let lv1 := (loc, fl ++ [f1]) in
  let lv2 := (loc, fl ++ [f2]) in
  lval_no_overlapping lv1 lv2 ->
  satisfies_unit (fst st) (AVal lv1 v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit (fst st') (AVal lv1 v1).
Proof.
  intros * H_lval_no_overlapping. subst lv1 lv2. apply exec_write_2.
  unfold lval_no_overlapping in H_lval_no_overlapping.
  replace (loc_no_overlapping loc loc) with false in H_lval_no_overlapping
    by (destruct (loc_no_overlapping loc loc) eqn:?;
      unfold loc_no_overlapping in *; destruct loc; hauto use: path_equivb_refl unfold: is_true, negb).
  assert (field_list_no_overlapping (fl ++ [f1]) (fl ++ [f2])) as H_field_list_no_overlapping by (hauto b: on).
  clear H_lval_no_overlapping.
  induction fl.
  - simpl in H_field_list_no_overlapping. hauto use: eqb_refl, eqb_neq, Bool.orb_false_l unfold: negb, Field, is_true.
  - apply IHfl. simpl in H_field_list_no_overlapping. hauto use: eqb_eq unfold: negb, orb, Field, is_true.
Qed.

Lemma satisfies_unit_child_iff m loc fl f v :
  satisfies_unit m (AVal (loc, fl ++ [f]) v) <->
  exists v',
    satisfies_unit m (AVal (loc, fl) v') /\ extract v' f = Some v.
Proof.
  split.
  - simpl. rewrite fold_left_app. intros H_satisfies_unit.
    destruct (fold_left extract_option fl (PathMap.get (loc_to_path this loc) m)) as [v' | ]; only 2 : sfirstorder.
    exists v'; sfirstorder.
  - simpl. rewrite fold_left_app. hauto lq: on.
Qed.

Lemma exec_write_no_overlapping_unit_case_2 st loc fl1 f1 fl2 f2 v1 v2 st' :
  let lv1 := (loc, fl1 ++ [f1] ++ fl2) in
  let lv2 := (loc, fl1 ++ [f2]) in
  f1 <> f2 ->
  (* lval_no_overlapping lv1 lv2 -> *)
  satisfies_unit (fst st) (AVal lv1 v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit (fst st') (AVal lv1 v1).
Proof.
  intros * H_lval_no_overlapping H_pre H_exec_write; subst lv1.
  rewrite <- (rev_involutive fl2) in *.
  generalize dependent v1.
  induction (rev fl2) as [ | hd tl]; intros * H_pre.
  - eapply exec_write_2; eassumption.
  - simpl rev in *.
    replace (fl1 ++ [f1] ++ rev tl ++ [hd]) with ((fl1 ++ [f1] ++ rev tl) ++ [hd]) in * by (rewrite <- !app_assoc; reflexivity).
    rewrite satisfies_unit_child_iff in *.
    destruct H_pre as [v1' H_pre]; exists v1'.
    split; only 2 : sfirstorder.
    apply IHtl; sfirstorder.
Qed.

Lemma field_list_no_overlapping_spec fl1 fl2 :
  field_list_no_overlapping fl1 fl2 ->
  exists fl3 f1 f2 fl4 fl5,
    f1 <> f2 /\
    fl1 = fl3 ++ [f1] ++ fl4 /\
    fl2 = fl3 ++ [f2] ++ fl5.
Proof.
  revert fl2.
  induction fl1 as [ | hd1 tl1]; intros * H_field_list_no_overlapping.
  - inversion H_field_list_no_overlapping.
  - destruct fl2 as [ | hd2 tl2]; only 1 : inversion H_field_list_no_overlapping.
    simpl in H_field_list_no_overlapping.
    destruct (~~(String.eqb hd1 hd2)) eqn:H_string_eqb.
    + exists [], hd1, hd2, tl1, tl2.
      hauto use: eqb_refl, eqb_neq, app_comm_cons, app_nil_l unfold: Field, app, negb.
    + destruct (IHtl1 tl2 ltac:(sfirstorder)) as (fl3 & f1 & f2 & fl4 & fl5 & ?).
      assert (hd1 = hd2) by (hauto use: eqb_eq, Bool.eq_true_negb_classical, eqb_neq unfold: Field); subst hd2.
      exists (hd1 :: fl3). sauto.
Qed.

Lemma exec_write_no_overlapping_unit st lv1 v1 lv2 v2 st' :
  lval_no_overlapping lv1 lv2 ->
  satisfies_unit (fst st) (AVal lv1 v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit (fst st') (AVal lv1 v1).
Proof.
  intros * H_no_overlapping H_pre H_exec_write.
  destruct lv1 as [loc1 fl1]; destruct lv2 as [loc2 fl2].
  simpl in H_no_overlapping.
  destruct loc1 as [ | p1]; only 1 : sfirstorder.
  destruct loc2 as [ | p2]; only 1 : sfirstorder.
  destruct (loc_no_overlapping (LInstance p1) (LInstance p2)) eqn:H_loc_no_overlapping.
  - apply exec_write_3 with (fl1 := []) in H_exec_write.
    clear v2; destruct H_exec_write as [v2 H_exec_write].
    inv H_exec_write. simpl.
    replace (PathMap.get (this ++ p1) (fst (update_val_by_loc this st (LInstance p2) v2)))
      with (PathMap.get (this ++ p1) (fst st))
      by (symmetry; apply loc_to_val_update_val_by_loc_diff; sfirstorder).
    apply H_pre.
  - assert (p1 = p2) by (apply path_equivb_eq; hauto unfold: loc_no_overlapping, negb, is_true); subst p2.
    assert (field_list_no_overlapping fl1 fl2) as H_field_list_no_overlapping by sfirstorder.
    apply field_list_no_overlapping_spec in H_field_list_no_overlapping
      as (fl3 & f1 & f2 & fl4 & fl5 & ? & ? & ?); subst fl1 fl2.
    rewrite app_assoc in H_exec_write.
    eapply exec_write_3 in H_exec_write.
    clear v2; destruct H_exec_write as [v2 H_exec_write].
    eapply exec_write_no_overlapping_unit_case_2; eassumption.
Qed.

Lemma exec_write_no_overlapping st a lv v st' :
  no_overlapping lv a ->
  to_shallow_assertion a (fst st) ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion a (fst st').
Proof.
  intros H_no_overlapping H_pre H_exec.
  induction a as [ | hd tl]; intros.
  - sfirstorder.
  - split.
    + destruct hd as [hd_lv hd_v | hd_lv hd_type].
      * eapply (exec_write_no_overlapping_unit).
        ++ rewrite lval_no_overlapping_symm. hauto b: on.
        ++ apply H_pre.
        ++ sfirstorder.
      (* TODO when type case is implemented *)
      * constructor.
    + apply IHtl.
      * destruct hd; hauto b: on.
      * sfirstorder.
Qed.

Lemma exec_write_same st lv v st' :
  mem_is_valid_field (fst st) lv ->
  exec_write this st (lval_to_semlval lv) v st' ->
  satisfies_unit (fst st') (AVal lv v).
Proof.
  apply exec_write_satisfies_unit.
Qed.

Fixpoint eval_read (a : assertion) (lv : Lval) : option Val :=
  match a with
  | hd :: tl =>
      match hd with
      | AVal hd_lv hd_v =>
          if lval_equivb hd_lv lv then Some hd_v else eval_read tl lv
      | AType hd_lv hd_type =>
          eval_read tl lv
      end
  | [] => None
  end.

Definition is_valid_field (a : assertion) (lv : Lval) : bool :=
  let (loc, fl) := lv in
  isNil fl || isSome (eval_read a lv).

Definition is_valid_field_sound m a lv :
  to_shallow_assertion a m ->
  is_valid_field a lv ->
  mem_is_valid_field m lv.
Proof.
  intros H_pre H_is_valid_field.
  induction a as [ | [hd_lv hd_v | hd_lv hd_type] tl].
  - destruct lv as [loc fl]. hauto b: on.
  - destruct lv as [loc fl]. simpl in H_is_valid_field |- *.
    unfold to_shallow_assertion, satisfies in H_pre; simpl in H_pre.
    destruct (lval_equivb hd_lv (loc, fl)) eqn:H_lval_equivb.
    + assert (hd_lv = (loc, fl)) by (apply lval_equivb_eq; assumption); subst.
      hauto lq: on.
    + destruct H_pre. apply IHtl; assumption.
  (* TODO when type case is implemented *)
  - sfirstorder.
Qed.

Lemma eval_write_add st a lv v st':
  is_valid_field a lv ->
  no_overlapping lv a ->
  to_shallow_assertion a (fst st) ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion ((AVal lv v) :: a) (fst st').
Proof.
  intros H_is_valid_field H_no_overlapping H_pre H_exec_write.
  split.
  - eapply exec_write_same; only 2 : eassumption.
    eapply is_valid_field_sound; eassumption.
  - apply (exec_write_no_overlapping st _ lv v); sfirstorder.
Qed.

Lemma eval_write_add' st a lv v st':
  mem_is_valid_field (fst st) lv ->
  no_overlapping lv a ->
  to_shallow_assertion a (fst st) ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion ((AVal lv v) :: a) (fst st').
Proof.
  intros H_is_valid_field H_no_overlapping H_pre H_exec_write.
  split.
  - eapply exec_write_same; eassumption.
  - apply (exec_write_no_overlapping st _ lv v); sfirstorder.
Qed.

Fixpoint no_nequiv_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      match hd with
      | AVal hd_lv _ =>
          if lval_equivb lv hd_lv then
            no_overlapping lv tl
          else
            lval_no_overlapping lv hd_lv && no_nequiv_overlapping lv tl
      | AType hd_lv hd_type =>
          no_nequiv_overlapping lv tl
      end
  | [] => true
  end.

Definition is_writable_lval (lv : Lval) (a : assertion) : bool :=
  is_valid_field a lv && is_lval_instance lv && no_nequiv_overlapping lv a.

Lemma eval_write_sound : forall st a lv v st',
  wellformed a ->
  is_writable_lval lv a ->
  to_shallow_assertion a (fst st) ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion (eval_write a lv v) (fst st').
Proof.
  intros * H_wellformed H_is_writable_lval.
  unfold is_writable_lval in H_is_writable_lval.
  assert (is_valid_field a lv) as H_is_valid_field by hauto b: on.
  assert (is_lval_instance lv) as H_is_lval_instance by hauto b: on.
  assert (no_nequiv_overlapping lv a) as H_no_nequiv_overlapping by hauto b: on.
  clear H_is_writable_lval.
  intros H_pre H_exec_write.
  induction a as [ | hd tl]; intros.
  - eapply eval_write_add; eassumption.
  - destruct hd as [hd_lv hd_v | hd_lv hd_type].
    + simpl in H_no_nequiv_overlapping |- *. destruct (lval_equivb lv hd_lv) eqn:H_lval_equivb.
      * eapply eval_write_add' with (st := st); only 2-4 : sfirstorder.
        eapply is_valid_field_sound; eassumption.
      * split.
        ++ refine (exec_write_no_overlapping_unit _ _ _ _ _ _ _ _ H_exec_write); only 2 : sfirstorder.
           hauto brefl: on use: lval_no_overlapping_symm unfold: andb, is_true.
        ++ apply IHtl; only 4 : sfirstorder; only 1, 3: hauto b: on.
           destruct lv as [loc fl].
           simpl in H_is_valid_field.
           replace (lval_equivb hd_lv (loc, fl)) with (false) in H_is_valid_field by (rewrite lval_equivb_symm; sfirstorder).
           sfirstorder.
    (* TODO when type case is implemented *)
    + split; only 1 : constructor.
      apply IHtl; only 4 : sfirstorder; hauto b: on.
Qed.

Lemma eval_read_sound : forall st a lv v,
  to_shallow_assertion a st ->
  eval_read a lv = Some v ->
  mem_eval_read st lv = Some v.
Proof.
  intros * H_pre H_eval_read.
  induction a as [ | hd tl].
  - inversion H_eval_read.
  - destruct hd as [hd_lv hd_v | hd_lv hd_type].
    + simpl in H_pre, H_eval_read.
      destruct (lval_equivb hd_lv lv) eqn:H_lval_equivb.
      * erewrite <- (lval_equivb_eq _ lv) by (apply H_lval_equivb).
        sfirstorder.
      * apply IHtl; sfirstorder.
    (* TODO when type case is implemented *)
    + sfirstorder.
Qed.

Fixpoint eval_expr_hook (a : assertion) (expr : Expression) : option Val :=
  match expr with
  | MkExpression _ (ExpName _ loc) _ _ =>
      eval_read a (loc, [])
  | MkExpression _ (ExpExpressionMember expr member) _ _ =>
      extract_option (eval_expr_hook a expr) (P4String.str member)
  | _ => None
  end.

Definition eval_expr (ge : genv) (a : assertion) (expr : Expression) :=
  eval_expr_gen ge (eval_expr_hook a) expr.

(* Definition eval_expr_gen_refine_statement ge get_val1 get_val2 (expr : @Expression tags_t) v :=
  (forall name loc v, get_val1 name loc = Some v -> get_val2 name loc = Some v) ->
  eval_expr_gen ge get_val1 expr = Some v ->
  eval_expr_gen ge get_val2 expr = Some v.

Lemma eval_expr_gen_refine ge get_val1 get_val2 (expr : @Expression tags_t) v :
  eval_expr_gen_refine_statement ge get_val1 get_val2 expr v
with eval_expr_gen_refine_preT ge get_val1 get_val2 tags expr typ dir v :
  eval_expr_gen_refine_statement ge get_val1 get_val2 (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_gen_refine_preT.
  - unfold eval_expr_gen_refine_statement. intros H_refine H_eval_expr_gen.
    destruct expr; inversion H_eval_expr_gen.
    + reflexivity.
    + hauto lq: on.
    + destruct (eval_expr_gen ge get_val1 arg) eqn:H_eval_arg; only 2 : inversion H1.
      assert (eval_expr_gen ge get_val2 arg = Some v0) by (eapply eval_expr_gen_refine; eauto).
      hauto lq: on.
    + destruct args as [larg rarg].
      destruct (eval_expr_gen ge get_val1 larg) eqn:H_eval_larg; only 2 : inversion H1.
      destruct (eval_expr_gen ge get_val1 rarg) eqn:H_eval_rarg; only 2 : inversion H1.
      assert (eval_expr_gen ge get_val2 larg = Some v0) by (eapply eval_expr_gen_refine; eauto).
      assert (eval_expr_gen ge get_val2 rarg = Some v1) by (eapply eval_expr_gen_refine; eauto).
      hauto lq: on.
    + destruct (eval_expr_gen ge get_val1 expr) eqn:H_eval_larg; only 2 : inversion H1.
      assert (eval_expr_gen ge get_val2 expr = Some v0) by (eapply eval_expr_gen_refine; eauto).
      hauto lq: on.
Qed. *)

Definition eval_expr_hook_sound_1_statement ge st a expr v :=
  wellformed a ->
  to_shallow_assertion a (fst st) ->
  eval_expr_hook a expr = Some v ->
  exec_expr ge this st expr v.

Lemma eval_expr_hook_sound_1 : forall ge st a expr v,
  eval_expr_hook_sound_1_statement ge st a expr v
with eval_expr_hook_sound_1_preT : forall ge st a tags expr typ dir v,
  eval_expr_hook_sound_1_statement ge st a (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_hook_sound_1_preT.
  - unfold eval_expr_hook_sound_1_statement.
    intros * H_wellformed H_pre H_eval_expr_hook.
    destruct expr; inversion H_eval_expr_hook.
    + eapply eval_read_sound in H_eval_expr_hook; only 2 : eassumption.
      constructor. assumption.
    + destruct (eval_expr_hook a expr) as [[] | ] eqn:?; inversion H1.
      * econstructor; only 1 : (eapply eval_expr_hook_sound_1; eassumption).
        constructor; erewrite alist_get_equiv; only 1 : apply H2. destruct name; eauto.
      * econstructor; only 1 : (eapply eval_expr_hook_sound_1; eassumption).
        destruct is_valid; only 2 : inversion H2.
        constructor.
        constructor; erewrite alist_get_equiv; only 1 : apply H2. destruct name; eauto.
Qed.

Lemma eval_expr_sound_1 : forall ge st a expr v,
  wellformed a ->
  to_shallow_assertion a (fst st) ->
  eval_expr ge a expr = Some v ->
  exec_expr ge this st expr v.
Proof.
  intros * H_wellformed H_pre H_eval_expr.
  eapply eval_expr_gen_sound_1; only 2 : eassumption.
  intros; eapply eval_expr_hook_sound_1; eassumption.
Qed.

Definition eval_expr_hook_sound_statement ge st a expr v :=
  wellformed a ->
  to_shallow_assertion a (fst st) ->
  eval_expr_hook a expr = Some v ->
  forall v', exec_expr ge this st expr v' ->
    v' = v.

Lemma eval_expr_hook_sound : forall ge st a expr v,
  eval_expr_hook_sound_statement ge st a expr v
with eval_expr_hook_sound_preT : forall ge st a tags expr typ dir v,
  eval_expr_hook_sound_statement ge st a (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_expr_hook_sound_preT.
  - unfold eval_expr_hook_sound_statement.
    intros * H_wellformed H_pre H_eval_expr_hook.
    destruct expr; inversion H_eval_expr_hook.
    + eapply eval_read_sound in H_eval_expr_hook; only 2 : eassumption.
      simpl in H_eval_expr_hook.
      inversion 1; subst.
      assert (Some v' = Some v) by (eapply eq_trans; only 2 : apply H_eval_expr_hook; eauto).
      congruence.
    + destruct (eval_expr_hook a expr) as [[] | ] eqn:H_eval_expr_hook'; inversion H1.
      * apply eval_expr_hook_sound with (ge := ge) (st := st) in H_eval_expr_hook'; only 2, 3 : assumption.
        inversion 1; subst;
          lazymatch goal with
          | H : exec_expr _ _ _ expr _ |- _ =>
              apply H_eval_expr_hook' in H;
              inv H
          end.
        pinv @get_member.
        erewrite alist_get_equiv, H2 in H5. 2 : { destruct name; eauto. }
        congruence.
      * apply eval_expr_hook_sound with (ge := ge) (st := st) in H_eval_expr_hook'; only 2, 3 : assumption.
        inversion 1; subst;
          lazymatch goal with
          | H : exec_expr _ _ _ expr _ |- _ =>
              apply H_eval_expr_hook' in H;
              inv H
          end.
        pinv @get_member.
        destruct is_valid; only 2 : inversion H2.
        pinv @read_header_field.
        erewrite alist_get_equiv, H2 in H4. 2 : { destruct name; eauto. }
        congruence.
Qed.

Lemma eval_expr_sound : forall ge st a expr v,
  wellformed a ->
  to_shallow_assertion a (fst st) ->
  eval_expr ge a expr = Some v ->
  forall v', exec_expr ge this st expr v'->
    v' = v.
Proof.
  intros * H_wellformed H_pre H_eval_expr.
  eapply eval_expr_gen_sound; only 2 : eassumption.
  intros; eapply eval_expr_hook_sound; eassumption.
Qed.

Fixpoint sem_eval_read (m : mem) (lv : SemLval) : option Val :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ =>
      PathMap.get (loc_to_path this loc) m
  | MkValueLvalue (ValLeftMember lv member) _ =>
      extract_option (sem_eval_read m lv) (P4String.str member)
  | _ => None
  end.

Definition sem_eval_read_sound_1_statement st lv v :=
  sem_eval_read (fst st) lv = Some v ->
  exec_read this st lv v.

Lemma sem_eval_read_sound_1 : forall st lv v,
  sem_eval_read_sound_1_statement st lv v
with sem_eval_read_sound_1_preT : forall st lv typ v,
  sem_eval_read_sound_1_statement st (MkValueLvalue lv typ) v.
Proof.
  - destruct lv; apply sem_eval_read_sound_1_preT.
  - unfold sem_eval_read_sound_1_statement.
    rename sem_eval_read_sound_1 into IH.
    destruct lv; intros * H_sem_eval_read; only 3, 4 : solve [inversion H_sem_eval_read].
    + apply exec_read_name, H_sem_eval_read.
    + simpl in H_sem_eval_read.
      destruct (sem_eval_read (fst st) expr) as [fields | ] eqn:H_sem_eval_read'; only 2 : solve [inversion H_sem_eval_read].
      apply exec_read_by_member.
      specialize (IH st expr fields H_sem_eval_read').
      destruct fields; only 1-12, 15-19 : solve [inversion H_sem_eval_read]; simpl in H_sem_eval_read.
      * eapply exec_read_member_struct; only 1 : (apply IH; reflexivity).
        rewrite alist_get_equiv with (s2 := {| P4String.tags := default; P4String.str := (P4String.str name) |}).
          2 : { destruct name. auto. }
        apply H_sem_eval_read.
      * eapply exec_read_member_header; only 1 : (apply IH; reflexivity).
        destruct is_valid; only 2 : inversion H_sem_eval_read.
        apply read_header_field_intro.
        rewrite alist_get_equiv with (s2 := {| P4String.tags := default; P4String.str := (P4String.str name) |}).
          2 : { destruct name. auto. }
        apply H_sem_eval_read.
Qed.

Definition sem_eval_read_sound_statement st lv v :=
  sem_eval_read (fst st) lv = Some v ->
  forall v', exec_read this st lv v' ->
    v' = v.

Lemma sem_eval_read_sound : forall st lv v,
  sem_eval_read_sound_statement st lv v
with sem_eval_read_sound_preT : forall st lv typ v,
  sem_eval_read_sound_statement st (MkValueLvalue lv typ) v.
Proof.
  - destruct lv; apply sem_eval_read_sound_preT.
  - unfold sem_eval_read_sound_statement.
    rename sem_eval_read_sound into IH.
    destruct lv; intros * H_sem_eval_read; only 3, 4 : solve [inversion H_sem_eval_read].
    + intros * H_exec_read.
      inv H_exec_read.
      assert (Some v' = Some v) by (eapply eq_trans; only 2 : apply H_sem_eval_read; eauto).
      congruence.
    + intros * H_exec_read.
      simpl in H_sem_eval_read.
      destruct (sem_eval_read (fst st) expr) as [fields | ] eqn:H_sem_eval_read'; only 2 : solve [inversion H_sem_eval_read].
      specialize (IH st expr fields H_sem_eval_read').
      destruct fields; only 1-12, 15-19 : solve [inversion H_sem_eval_read]; simpl in H_sem_eval_read.
      * inv H_exec_read. pinv @exec_read_member; specialize (IH _ H0); only 1, 3 : solve [inversion IH].
        rewrite alist_get_equiv with (s2 := {| P4String.tags := default; P4String.str := (P4String.str name) |}) in H1.
          2 : { destruct name. auto. }
        scongruence.
      * destruct is_valid; only 2 : inversion H_sem_eval_read.
        inv H_exec_read. pinv @exec_read_member; specialize (IH _ H0); only 2, 3 : solve [inversion IH].
        destruct is_valid; only 2 : inversion IH.
        pinv @read_header_field.
        rewrite alist_get_equiv with (s2 := {| P4String.tags := default; P4String.str := (P4String.str name) |}) in H2.
          2 : { destruct name. auto. }
        scongruence.
Qed.

Definition sem_is_valid_field (m : mem) (lv : SemLval) : bool :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ => true
  | _ => sem_eval_read m lv
  end.

Axiom get_loc_to_path_congruent : forall (m : mem) loc1 loc2,
  locator_equivb loc1 loc2 ->
  PathMap.get (loc_to_path this loc1) m = PathMap.get (loc_to_path this loc2) m.

Axiom loc_to_val_congruent : forall st loc1 loc2,
  locator_equivb loc1 loc2 ->
  loc_to_val this loc1 st = loc_to_val this loc2 st.

Definition sem_eval_read_congruent_statement m lv1 lv2 :=
  semlval_equivb lv1 lv2 ->
  sem_eval_read m lv1 = sem_eval_read m lv2.

Lemma sem_eval_read_congruent : forall m lv1 lv2,
  sem_eval_read_congruent_statement m lv1 lv2
with sem_eval_read_congruent_preT : forall m lv1 typ1 lv2,
  sem_eval_read_congruent_statement m (MkValueLvalue lv1 typ1) lv2.
Proof.
  - destruct lv1; apply sem_eval_read_congruent_preT.
  - unfold sem_eval_read_congruent_statement.
    rename sem_eval_read_congruent into IH.
    intros * H_semlval_equivb.
    destruct lv1; destruct lv2 as [[] ?]; only 2-5, 7-10, 12-15 : solve [inversion H_semlval_equivb].
    + simpl in H_semlval_equivb |- *.
      apply get_loc_to_path_congruent; assumption.
    + simpl in H_semlval_equivb |- *.
      erewrite IH with (lv2 := expr0); only 2 : hauto b: on.
      f_equal.
      destruct name; destruct name0.
      unfold P4String.equivb in H_semlval_equivb.
      simpl in H_semlval_equivb |- *.
      apply Strings.String.eqb_eq; hauto b: on.
    + constructor.
    + constructor.
Qed.

(* Lemma mem_eval_read_sound_2 : forall st lv v,
  mem_eval_read st lv = Some v ->
  sem_eval_read st (lval_to_semlval lv) = Some v.
Proof.
  (* intros * H_mem_eval_read.
  destruct lv as [loc fl].
  induction fl as [ | hd tl].
  - exact H_mem_eval_read.
  - simpl. apply IHtl. *)
Admitted. *)

Lemma mem_is_valid_field_sound m lv :
  mem_is_valid_field m lv ->
  sem_is_valid_field m (lval_to_semlval lv).
Admitted.

(* Definition sem_is_valid_field (m : mem) (lv : SemLval) : bool :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ => true
  | _ => sem_eval_read m lv
  end. *)

Lemma exec_read_congruent : forall st lv1 lv2 v,
  sem_is_valid_field (fst st) lv2 ->
  semlval_equivb lv1 lv2 ->
  exec_read this st lv1 v ->
  exec_read this st lv2 v.
Proof.
  intros * H_sem_is_valid_field H_semlval_equivb H_exec_read.
  destruct (sem_eval_read (fst st) lv2) eqn:?.
  - assert (sem_eval_read (fst st) lv1 = sem_eval_read (fst st) lv2) by (apply sem_eval_read_congruent; assumption).
    assert (sem_eval_read (fst st) lv1 = Some v0) by congruence.
    epose proof (sem_eval_read_sound _ _ _ ltac:(eassumption) _ H_exec_read).
    apply sem_eval_read_sound_1. congruence.
  - unfold sem_is_valid_field in H_sem_is_valid_field.
    destruct lv2 as [[] ?]; only 2-4 : (rewrite Heqo in H_sem_is_valid_field; hauto).
    constructor.
    destruct lv1 as [[] ?]; only 2-4 : inversion H_semlval_equivb.
    inv H_exec_read. erewrite loc_to_val_congruent; only 1 : eassumption.
    rewrite locator_equivb_symm. apply H_semlval_equivb.
Qed.

(* Lemma sem_eval_read_sem_is_valid_field st lv :
  sem_eval_read st lv ->
  sem_is_valid_field st lv.
Proof.
  intros H_sem_eval_read.
  unfold sem_is_valid_field.
  destruct (sem_eval_read st lv); only 2 : sfirstorder.
  destruct lv as [[] ?]; constructor.
Qed. *)

Lemma sem_is_valid_field_parent : forall st lv member typ,
  sem_is_valid_field st (MkValueLvalue (ValLeftMember lv member) typ) ->
  sem_is_valid_field st lv.
Proof.
  intros * H_sem_is_valid_field.
  unfold sem_is_valid_field in H_sem_is_valid_field.
  destruct (sem_eval_read st lv) eqn:?; destruct lv as [[] ?];
  hauto lq: on.
Qed.

Axiom update_member_congruent : forall fields (f1 f2 : P4String) v fields',
  P4String.equivb f1 f2 ->
  update_member fields f1 v fields' ->
  update_member fields f2 v fields'.

Lemma exec_write_congruent : forall st lv1 lv2 v st',
  sem_is_valid_field (fst st) lv2 ->
  semlval_equivb lv1 lv2 ->
  exec_write this st lv1 v st' ->
  exec_write this st lv2 v st'.
Proof.
  intros * H_sem_is_valid_field H_semlval_equivb H_exec_write.
  generalize dependent lv2.
  induction H_exec_write; intros * H_sem_is_valid_field H_semlval_equivb.
  - destruct lv2 as [[] ?]; inv H_semlval_equivb.
    econstructor.
    sfirstorder use: locator_equivb_eq unfold: is_true.
  - destruct lv2 as [[] ?]; inv H_semlval_equivb.
    apply sem_is_valid_field_parent in H_sem_is_valid_field.
    unfold sem_is_valid_field in H_sem_is_valid_field.
    econstructor.
    1 : {
      eapply exec_read_congruent; only 1, 3 : eassumption.
      destruct (semlval_equivb lv expr); sfirstorder.
    }
    2 : {
      eapply IHH_exec_write.
      - apply H_sem_is_valid_field.
      - destruct (semlval_equivb lv expr); sfirstorder.
    }
    eapply update_member_congruent; only  2 : eassumption.
    destruct (P4String.equivb fname name); hauto b: on.
  - destruct lv2 as [[] ?]; hauto lq: on.
  - destruct lv2 as [[] ?]; hauto lq: on.
  - destruct lv2 as [[] ?]; hauto lq: on.
Qed.

Fixpoint eval_lexpr (expr : @Expression tags_t) : option Lval :=
  match expr with
  | MkExpression _ (ExpName _ loc) _ _ =>
      Some (loc, [])
  | MkExpression _ (ExpExpressionMember expr member) _ _ =>
      match eval_lexpr expr with
      | Some (loc, fl) =>
          if (String.eqb (P4String.str member) "next") then
            None
          else
            Some (loc, fl ++ [P4String.str member])
      | None => None
      end
  | _ => None
  end.

Definition eval_lexpr_sound_statement ge st expr lv :=
  eval_lexpr expr = Some lv ->
  forall lv' sig, exec_lexpr ge this st expr lv' sig ->
    sig = SContinue /\ semlval_equivb lv' (lval_to_semlval lv).

Lemma eval_lexpr_sound : forall ge st expr v,
  eval_lexpr_sound_statement ge st expr v
with eval_lexpr_sound_preT : forall ge st tags expr typ dir v,
  eval_lexpr_sound_statement ge st (MkExpression tags expr typ dir) v.
Proof.
  - intros. destruct expr; apply eval_lexpr_sound_preT.
  - unfold eval_lexpr_sound_statement.
    rename eval_lexpr_sound into IH.
    intros * H_eval_lexpr.
    destruct expr; inversion H_eval_lexpr.
    + intros * H_exec_lexpr.
      inv H_exec_lexpr. repeat split. simpl. apply locator_equivb_refl.
    + intros * H_exec_lexpr.
      destruct (eval_lexpr expr) as [[loc fl] | ] eqn:H_eval_lexpr'; only 2 : discriminate.
      specialize (IH ge st expr (loc, fl) ltac:(assumption)).
      inv H_exec_lexpr.
      * specialize (IH _ _ ltac:(eassumption)) as [].
        destruct (String.eqb (P4String.str name) "next"); only 1 : discriminate.
        inv H1.
        rewrite lval_to_semlval_snoc.
        unfold semlval_equivb; fold semlval_equivb.
        destruct name; hauto b: on.
      * discriminate.
Qed.

End AssertionLangSoundness.

