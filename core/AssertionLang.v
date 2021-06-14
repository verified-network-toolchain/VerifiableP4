Require Import Coq.ssr.ssrbool.
Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section AssertionLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation SemLval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition Field : Type := string.
Definition Lval : Type := Locator * list Field.

Definition assertion := list (Lval * Val).

Variable this : path.

Ltac inv H := inversion H; subst; clear H.
Ltac pinv P :=
  lazymatch goal with
  | H : context [P] |- _ => inv H
  (* | H : P |- _ => inv H
  | H : P _ |- _ => inv H
  | H : P _ _ |- _ => inv H
  | H : P _ _ _ |- _ => inv H
  | H : P _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ _ _ |- _ => inv H *)
  end.

(* Fixpoint sem_eval_read (st : state) (lv : Lval) : option Val :=
  match lv with
  | MkValueLvalue (ValLeftName _ loc) _ =>
      loc_to_val this loc st
  | MkValueLvalue (ValLeftMember lv member) _ =>
      match sem_eval_read st lv with
      | Some (ValBaseStruct fields) =>
          AList.get fields member
      | Some (ValBaseHeader fields true) =>
          AList.get fields member
      | _ => None
      end
  | _ => None
  end.

Lemma sem_eval_read_sound : forall st lv v,
  sem_eval_read st lv = Some v ->
  forall v', exec_read this st lv v' ->
    v' = v.
Admitted. *)

Definition alist_get {A} (l : P4String.AList tags_t A) (s : string) : option A :=
  AList.get l (P4String.Build_t _ default s).

Definition extract (v : Val) (f : Field) : option Val :=
  match v with
  | ValBaseStruct fields =>
      alist_get fields f
  | ValBaseHeader fields true =>
      alist_get fields f
  | _ => None
  end.

Definition extract_option (ov : option Val) (f : Field) : option Val :=
  match ov with
  | Some v => extract v f
  | None => None
  end.

Definition state_eval_read (st : state) (lv : Lval) : option Val :=
  let (loc, fl) := lv in
  fold_left extract_option fl (loc_to_val this loc st).

Lemma state_eval_read_snoc st loc fl f :
  state_eval_read st (loc, fl ++ [f]) =
    extract_option (state_eval_read st (loc, fl)) f .
Proof.
  simpl. rewrite fold_left_app. reflexivity.
Qed.

Definition isNil {A} (l : list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Lemma not_isNil_snoc {A} (l : list A) (x : A) :
  ~~(isNil (l ++ [x])).
Proof.
  induction l; auto.
Qed.

Definition state_is_valid_field (st : state) (lv : Lval) : bool :=
  let (loc, fl) := lv in
  isNil fl || isSome (state_eval_read st lv).

Lemma state_is_valid_field_parent st loc fl1 f :
  state_is_valid_field st (loc, fl1 ++ [f]) ->
  state_is_valid_field st (loc, fl1).
Proof.
  unfold state_is_valid_field. rewrite state_eval_read_snoc.
  destruct (state_eval_read st (loc, fl1)); hauto use: Reflect.orE, is_true_true unfold: isNil, is_true, app, extract_option, orb, isSome.
Qed.

Definition satisfies_unit (st : state) (a_unit : Lval * Val) : Prop :=
  let (lv, v) := a_unit in
  state_eval_read st lv = Some v.

Definition satisfies (st : state) (a : assertion) : Prop :=
  fold_right and True (map (satisfies_unit st) a).

Definition to_shallow_assertion (a : assertion) : state -> Prop :=
  fun st => satisfies st a.

Definition loc_no_overlapping (loc1 : Locator) (loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => ~~ (path_equivb p1 p2)
  | _, _ => false
  end.

Fixpoint semlval_to_lval (slv : SemLval) : option Lval :=
  match slv with
  | MkValueLvalue (ValLeftName _ loc) _ => Some (loc, nil)
  | MkValueLvalue (ValLeftMember slv member) _ =>
      let olv := semlval_to_lval slv in
      option_map (map_snd (cons (P4String.str member))) olv
  | _ => None
  end.

Definition dummy_type : @P4Type tags_t := TypBool.

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

Lemma state_eval_read_sound_1 : forall st lv v,
  state_eval_read st lv = Some v ->
  exec_read this st (lval_to_semlval lv) v.
Proof.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  induction (rev fl) as [ | hd tl]; intros * H_state_eval_read.
  - apply exec_read_name, H_state_eval_read.
  - simpl rev in *. rewrite lval_to_semlval_snoc. rewrite state_eval_read_snoc in H_state_eval_read.
    apply exec_read_by_member.
    destruct (state_eval_read st (loc, rev tl)) as [[] | ]; only 1-12, 15-20 : solve [inversion H_state_eval_read].
    + eapply exec_read_member_struct; only 1 : (apply IHtl; reflexivity).
      apply H_state_eval_read.
    + eapply exec_read_member_header; only 1 : (apply IHtl; reflexivity).
      destruct is_valid; only 2 : inversion H_state_eval_read.
      apply read_header_field_intro, H_state_eval_read.
Qed.

Lemma state_eval_read_sound : forall st lv v,
  state_eval_read st lv = Some v ->
  forall v', exec_read this st (lval_to_semlval lv) v' ->
    v' = v.
Proof.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  induction (rev fl) as [ | hd tl]; intros * H_state_eval_read * H_exec_read.
  - inv H_exec_read. sfirstorder.
  - simpl rev in *. rewrite lval_to_semlval_snoc in H_exec_read. rewrite state_eval_read_snoc in H_state_eval_read.
    destruct (state_eval_read st (loc, rev tl)) as [fields | ]; only 2 : solve [inversion H_state_eval_read].
    specialize (IHtl fields ltac:(reflexivity)).
    destruct fields; only 1-12, 15-19 : solve [inversion H_state_eval_read]; simpl in H_state_eval_read.
    + inv H_exec_read. pinv @exec_read_member; specialize (IHtl _ H0); only 1, 3 : solve [inversion IHtl].
      scongruence unfold: alist_get.
    + destruct is_valid; only 2 : inversion H_state_eval_read.
      inv H_exec_read. pinv @exec_read_member; specialize (IHtl _ H0); only 2, 3 : solve [inversion IHtl].
      destruct is_valid; only 2 : inversion IHtl.
      pinv @read_header_field.
      scongruence unfold: alist_get.
Qed.

Fixpoint field_list_no_overlapping (fl1 fl2 : list Field) : bool :=
  match fl1, fl2 with
  | hd1 :: tl1, hd2 :: tl2 =>
      ~~(String.eqb hd1 hd2) || field_list_no_overlapping tl1 tl2
  | _, _ => false
  end.

Definition is_instance (loc : Locator) : bool :=
  match loc with
  | LInstance _ => true
  | LGlobal _ => false
  end.

Definition lval_no_overlapping (lv1 : Lval) (lv2 : Lval) : bool :=
  match lv1, lv2 with
  | (loc1, fl1), (loc2, fl2) =>
      is_instance loc1 && is_instance loc2 && (loc_no_overlapping loc1 loc2 || field_list_no_overlapping fl1 fl2)
  end.

Fixpoint no_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl => lval_no_overlapping lv (fst hd) && no_overlapping lv tl
  | [] => true
  end.

Definition is_lval_instance (lv : Lval) : bool :=
  match lv with
  | (loc, _) =>
      is_instance loc
  end.

Fixpoint wellformed (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      let (lv, _) := hd in
      is_lval_instance lv && no_overlapping lv tl && wellformed tl
  | [] => true
  end.

Definition locator_equivb (loc1 loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_equivb p1 p2
  | LGlobal p1, LGlobal p2 => path_equivb p1 p2
  | _, _ => false
  end.

Definition field_equivb (f1 f2 : Field) : bool :=
  match f1, f2 with
  | s1, s2 =>
      String.eqb s1 s2
  end.

Definition lval_equivb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | (loc1, fl1), (loc2, fl2) =>
      locator_equivb loc1 loc2 && list_eqb field_equivb fl1 fl2
  end.

Fixpoint eval_write (a : assertion) (lv : Lval) (v : Val) : assertion :=
  match a with
  | hd :: tl =>
      let (hd_lv, hd_v) := hd in
      if lval_equivb lv hd_lv then
        (lv, v) :: tl
      else
        hd :: eval_write tl lv v
  | [] => [(lv, v)]
  end.

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
  satisfies_unit st ((loc, fl), (ValBaseHeader fields true)) ->
  alist_get fields f = Some v ->
  satisfies_unit st ((loc, fl ++ [f]), v).
Proof.
  intros H_satisfies_unit H_alist_get.
  simpl. rewrite fold_left_app, H_satisfies_unit.
  apply H_alist_get.
Qed.

Lemma satisfies_unit_helper_struct st loc fl f fields v :
  satisfies_unit st ((loc, fl), (ValBaseStruct fields)) ->
  alist_get fields f = Some v ->
  satisfies_unit st ((loc, fl ++ [f]), v).
Proof.
  intros H_satisfies_unit H_alist_get.
  simpl. rewrite fold_left_app, H_satisfies_unit.
  apply H_alist_get.
Qed.

Lemma exec_write_satisfies_unit st lv v st' :
  state_is_valid_field st lv ->
  exec_write this st (lval_to_semlval lv) v st' ->
  satisfies_unit st' (lv, v).
Proof.
  intros * H_state_is_valid_field H_exec_write.
  revert H_state_is_valid_field H_exec_write.
  destruct lv as [loc fl].
  rewrite <- (rev_involutive fl).
  generalize dependent v.
  induction (rev fl) as [ | hd tl]; intros * H_state_is_valid_field H_exec_write.
  - inv H_exec_write. apply loc_to_val_update_val_by_loc_same, locator_equivb_refl.
  - simpl rev in H_exec_write; rewrite lval_to_semlval_snoc in H_exec_write.
    inv H_exec_write.
    simpl rev in H_state_is_valid_field.
    apply state_is_valid_field_parent in H_state_is_valid_field as H_state_is_valid_field'.
    unfold state_is_valid_field in H_state_is_valid_field.
    rewrite state_eval_read_snoc in H_state_is_valid_field.
    assert (~~(isNil (rev tl ++ [hd]))) by (apply not_isNil_snoc).
    assert (state_eval_read st (loc, rev tl) = Some v0) as H_state_eval_read. {
      destruct (state_eval_read st (loc, rev tl)) eqn:H_state_eval_read; only 2 : hauto b: on.
      f_equal. symmetry. eapply state_eval_read_sound; eassumption.
    }
    pinv @update_member.
    + pinv @write_header_field.
      rewrite H_state_eval_read in H_state_is_valid_field.
      destruct is_valid; only 2 : (hauto b: on).
      unfold satisfies_unit.
      eapply satisfies_unit_helper_header; only 1 : (apply IHtl; eassumption).
      eapply alist_get_set_same; eauto.
    + eapply satisfies_unit_helper_struct; only 1 : (apply IHtl; eassumption).
      eapply alist_get_set_same; eauto.
    + rewrite H_state_eval_read in H_state_is_valid_field.
      hauto b: on.
Qed.

(* Things will be easier if we use the reversed order in exec_write. *)

Lemma satisfies_unit_child st loc fl f fields v :
  satisfies_unit st ((loc, fl), fields) ->
  extract_option (Some fields) f = Some v ->
  satisfies_unit st ((loc, fl ++ [f]), v).
Proof.
  simpl. rewrite fold_left_app. hauto lq: on.
Qed.

(* Proving the following lemma should be enough. For exec_write_no_overlapping_unit,
  it is easy to remove a last field from either lv1 or lv2, so we can reach the part that
  only one field is different. *)

Lemma exec_write_2 st loc fl f1 f2 v1 v2 st' :
  f1 <> f2 ->
  satisfies_unit st ((loc, fl ++ [f1]), v1) ->
  exec_write this st (lval_to_semlval (loc, fl ++ [f2])) v2 st' ->
  satisfies_unit st' ((loc, fl ++ [f1]), v1).
Proof.
  intros H_neq H_pre H_exec_write.
  simpl rev in H_exec_write; rewrite lval_to_semlval_snoc in H_exec_write.
  inv H_exec_write.
  eapply satisfies_unit_child with (st := st'). 1 : eapply exec_write_satisfies_unit with (st := st).
  - eapply state_is_valid_field_parent with (f := f1). unfold satisfies_unit in H_pre.
    hauto b: on.
  - eassumption.
  - unfold satisfies_unit in H_pre.
    rewrite state_eval_read_snoc in H_pre.
    assert (state_eval_read st (loc, fl) = Some v) as H_state_eval_read. {
      destruct (state_eval_read st (loc, fl)) eqn:H_state_eval_read;
        (* conflict with H_state_is_valid_field' *)
        only 2 : hauto.
      f_equal. symmetry. eapply state_eval_read_sound; eassumption.
    }
    rewrite H_state_eval_read in H_pre.
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
  satisfies_unit st (lv1, v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit st' (lv1, v1).
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

Lemma satisfies_unit_child_iff st loc fl f v :
  satisfies_unit st ((loc, fl ++ [f]), v) <->
  exists v',
    satisfies_unit st ((loc, fl), v') /\ extract v' f = Some v.
Proof.
  split.
  - simpl. rewrite fold_left_app. intros H_satisfies_unit.
    destruct (fold_left extract_option fl (loc_to_val this loc st)) as [v' | ]; only 2 : sfirstorder.
    exists v'; sfirstorder.
  - simpl. rewrite fold_left_app. hauto lq: on.
Qed.

Lemma exec_write_no_overlapping_unit_case_2 st loc fl1 f1 fl2 f2 v1 v2 st' :
  let lv1 := (loc, fl1 ++ [f1] ++ fl2) in
  let lv2 := (loc, fl1 ++ [f2]) in
  f1 <> f2 ->
  (* lval_no_overlapping lv1 lv2 -> *)
  satisfies_unit st (lv1, v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit st' (lv1, v1).
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

(* This axiom is provable if tags_t is a unit type. *)
Axiom path_equivb_eq : forall (p1 p2 : path), path_equivb p1 p2 -> p1 = p2.

Axiom locator_equivb_eq : forall loc1 loc2, locator_equivb loc1 loc2 -> loc1 = loc2.

Axiom lval_equivb_eq : forall lv1 lv2, lval_equivb lv1 lv2 -> lv1 = lv2.

Lemma exec_write_no_overlapping_unit st lv1 v1 lv2 v2 st' :
  lval_no_overlapping lv1 lv2 ->
  satisfies_unit st (lv1, v1) ->
  exec_write this st (lval_to_semlval lv2) v2 st' ->
  satisfies_unit st' (lv1, v1).
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
    rewrite loc_to_val_update_val_by_loc_diff; only 2 : sfirstorder.
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
  to_shallow_assertion a st ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion a st'.
Proof.
  intros H_no_overlapping H_pre H_exec.
  induction a as [ | hd tl]; intros.
  - sfirstorder.
  - split.
    + destruct hd as [a_lv a_v].
      eapply (exec_write_no_overlapping_unit).
      * rewrite lval_no_overlapping_symm. hauto b: on.
      * apply H_pre.
      * sfirstorder.
    + apply IHtl.
      * hauto b: on.
      * sfirstorder.
Qed.

Lemma exec_write_same st lv v st' :
  state_is_valid_field st lv ->
  exec_write this st (lval_to_semlval lv) v st' ->
  satisfies_unit st' (lv, v).
Proof.
  apply exec_write_satisfies_unit.
Qed.

Fixpoint eval_read (a : assertion) (lv : Lval) : option Val :=
  match a with
  | (hd_lv, hd_v) :: tl =>
      if lval_equivb hd_lv lv then Some hd_v else eval_read tl lv
  | [] => None
  end.

Definition is_valid_field (a : assertion) (lv : Lval) : bool :=
  let (loc, fl) := lv in
  isNil fl || isSome (eval_read a lv).

Definition is_valid_field_sound st a lv :
  to_shallow_assertion a st ->
  is_valid_field a lv ->
  state_is_valid_field st lv.
Proof.
  intros H_pre H_is_valid_field.
  induction a as [ | [hd_lv hd_v] tl].
  - destruct lv as [loc fl]. hauto b: on.
  - destruct lv as [loc fl]. simpl in H_is_valid_field |- *.
    unfold to_shallow_assertion, satisfies in H_pre; simpl in H_pre.
    destruct (lval_equivb hd_lv (loc, fl)) eqn:H_lval_equivb.
    + assert (hd_lv = (loc, fl)) by (apply lval_equivb_eq; assumption); subst.
      hauto lq: on.
    + destruct H_pre. apply IHtl; assumption.
Qed.

Lemma eval_write_add st a lv v st':
  is_valid_field a lv ->
  no_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion ((lv, v) :: a) st'.
Proof.
  intros H_is_valid_field H_no_overlapping H_pre H_exec_write.
  split.
  - eapply exec_write_same; only 2 : eassumption.
    eapply is_valid_field_sound; eassumption.
  - apply (exec_write_no_overlapping st _ lv v); sfirstorder.
Qed.

Lemma eval_write_add' st a lv v st':
  state_is_valid_field st lv ->
  no_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion ((lv, v) :: a) st'.
Proof.
  intros H_is_valid_field H_no_overlapping H_pre H_exec_write.
  split.
  - eapply exec_write_same; eassumption.
  - apply (exec_write_no_overlapping st _ lv v); sfirstorder.
Qed.

Fixpoint no_nequiv_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      if lval_equivb lv (fst hd) then
        no_overlapping lv tl
      else
        lval_no_overlapping lv (fst hd) && no_nequiv_overlapping lv tl
  | [] => true
  end.

Lemma eval_write_sound : forall st a lv v st',
  wellformed a ->
  is_valid_field a lv ->
  is_lval_instance lv ->
  no_nequiv_overlapping lv a ->
  to_shallow_assertion a st ->
  exec_write this st (lval_to_semlval lv) v st' ->
  to_shallow_assertion (eval_write a lv v) st'.
Proof.
  intros * H_wellformed H_is_valid_field H_is_lval_instance H_no_nequiv_overlapping H_pre H_exec_write.
  induction a as [ | hd tl]; intros.
  - eapply eval_write_add; eassumption.
  - destruct hd as [hd_lv hd_v].
    simpl in H_no_nequiv_overlapping |- *. destruct (lval_equivb lv hd_lv) eqn:H_lval_equivb.
    + eapply eval_write_add' with (st := st); only 2-4 : sfirstorder.
      eapply is_valid_field_sound; eassumption.
    + split.
      * refine (exec_write_no_overlapping_unit _ _ _ _ _ _ _ _ H_exec_write); only 2 : sfirstorder.
        hauto brefl: on use: lval_no_overlapping_symm unfold: andb, is_true.
      * apply IHtl; only 4 : sfirstorder; only 1, 3: hauto b: on.
        destruct lv as [loc fl].
        simpl in H_is_valid_field.
        replace (lval_equivb hd_lv (loc, fl)) with (false) in H_is_valid_field by (rewrite lval_equivb_symm; sfirstorder).
        sfirstorder.
Qed.

Lemma eval_read_sound : forall st a lv v,
  to_shallow_assertion a st ->
  eval_read a lv = Some v ->
  state_eval_read st lv = Some v.
Proof.
  intros * H_pre H_eval_read.
  induction a as [ | hd tl].
  - inversion H_eval_read.
  - destruct hd as [hd_lv hd_v].
    simpl in H_pre, H_eval_read.
    destruct (lval_equivb hd_lv lv) eqn:H_lval_equivb.
    + erewrite <- (lval_equivb_eq _ lv) by (apply H_lval_equivb).
      sfirstorder.
    + apply IHtl; sfirstorder.
Qed.

Fixpoint semlval_equivb (lv1 lv2 : SemLval) : bool :=
  match lv1, lv2 with
  | MkValueLvalue (ValLeftName _ loc1) _, MkValueLvalue (ValLeftName _ loc2) _ =>
      locator_equivb loc1 loc2
  | MkValueLvalue (ValLeftMember lv1 member1) _, MkValueLvalue (ValLeftMember lv2 member2) _ =>
      semlval_equivb lv1 lv2 && P4String.equivb member1 member2
  | MkValueLvalue (ValLeftBitAccess lv1 msb1 lsb1) _, MkValueLvalue (ValLeftBitAccess lv2 msb2 lsb2) _ =>
      semlval_equivb lv1 lv2 && Nat.eqb msb1 msb2 && Nat.eqb lsb1 lsb2
  | MkValueLvalue (ValLeftArrayAccess lv1 idx1) _, MkValueLvalue (ValLeftArrayAccess lv2 idx2) _ =>
      semlval_equivb lv1 lv2 && Nat.eqb idx1 idx2
  | _, _ => false
  end.

Axiom exec_write_semlval_equiv : forall st lv1 lv2 v st',
  semlval_equivb lv1 lv2 ->
  exec_write this st lv1 v st' ->
  exec_write this st lv2 v st'.

Axiom exec_read_semlval_equiv : forall st lv1 lv2 v,
  semlval_equivb lv1 lv2 ->
  exec_read this st lv1 v ->
  exec_read this st lv2 v.

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
  to_shallow_assertion a st ->
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
        erewrite alist_get_equiv; only 1 : apply H2. destruct name; eauto.
      * econstructor; only 1 : (eapply eval_expr_hook_sound_1; eassumption).
        destruct is_valid; only 2 : inversion H2.
        constructor.
        erewrite alist_get_equiv; only 1 : apply H2. destruct name; eauto.
Qed.

Lemma eval_expr_sound_1 : forall ge st a expr v,
  wellformed a ->
  to_shallow_assertion a st ->
  eval_expr ge a expr = Some v ->
  exec_expr ge this st expr v.
Proof.
  intros * H_wellformed H_pre H_eval_expr.
  eapply eval_expr_gen_sound_1; only 2 : eassumption.
  intros; eapply eval_expr_hook_sound_1; eassumption.
Qed.

Definition eval_expr_hook_sound_statement ge st a expr v :=
  wellformed a ->
  to_shallow_assertion a st ->
  eval_expr_hook a expr = Some v ->
  forall v', exec_expr ge this st expr v'->
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
      inversion 1; subst. congruence.
    + destruct (eval_expr_hook a expr) as [[] | ] eqn:H_eval_expr_hook'; inversion H1.
      * apply eval_expr_hook_sound with (ge := ge) (st := st) in H_eval_expr_hook'; only 2, 3 : assumption.
        inversion 1; subst;
          lazymatch goal with
          | H : exec_expr _ _ _ expr _ |- _ =>
              apply H_eval_expr_hook' in H;
              inv H
          end.
        unfold alist_get in H2.
        erewrite alist_get_equiv, H2 in H12. 2 : { destruct name; eauto. }
        congruence.
      * apply eval_expr_hook_sound with (ge := ge) (st := st) in H_eval_expr_hook'; only 2, 3 : assumption.
        inversion 1; subst;
          lazymatch goal with
          | H : exec_expr _ _ _ expr _ |- _ =>
              apply H_eval_expr_hook' in H;
              inv H
          end.
        destruct is_valid; only 2 : inversion H2.
        inv H12.
        unfold alist_get in H2.
        erewrite alist_get_equiv, H2 in H3. 2 : { destruct name; eauto. }
        congruence.
Qed.

Lemma eval_expr_sound : forall ge st a expr v,
  wellformed a ->
  to_shallow_assertion a st ->
  eval_expr ge a expr = Some v ->
  forall v', exec_expr ge this st expr v'->
    v' = v.
Proof.
  intros * H_wellformed H_pre H_eval_expr.
  eapply eval_expr_gen_sound; only 2 : eassumption.
  intros; eapply eval_expr_hook_sound; eassumption.
Qed.

End AssertionLang.

