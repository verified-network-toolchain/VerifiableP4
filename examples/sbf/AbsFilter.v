Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.core.Coqlib.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section AbsFilter.

Context {header_type : Set}.
Context {Inhabitant_header_type : Inhabitant header_type}.

Context (num_rows : Z) (num_slots : Z).
Hypothesis H_num_slots : 0 < num_slots.

Section Row.

Context (hash : header_type -> Z).
Hypothesis H_hash : forall h, 0 <= hash h < num_slots.

Inductive row : Type :=
  | Clear (cleared : list bool)
  | Normal (hs : list header_type).

Inductive row_sim : row -> ConFilter.row num_slots -> Prop :=
  | rom_sim_clear : forall (cleared : list bool) cr,
      Zlength cleared = num_slots ->
      (forall j, 0 <= j < num_slots -> Znth j cleared -> Znth j (`cr) = false) ->
      row_sim (Clear cleared) cr
  | rom_sim_normal : forall hs cr,
      `cr = fold_left (fun l i => upd_Znth i l true) (map hash hs) (Zrepeat false num_slots) ->
      row_sim (Normal hs) cr.

Definition row_insert (r : row) (h : header_type) : option row :=
  match r with
  | Clear cleared =>
      if fold_andb cleared then
        Some (Normal [h])
      else
        None
  | Normal hs => Some (Normal (hs ++ [h]))
  end.

Lemma row_insert_sound : forall r cr h r',
  row_sim r cr ->
  row_insert r h = Some r' ->
  row_sim r' (ConFilter.row_insert cr (hash h)).
Proof.
  intros.
  destruct r as [? | hs]; inv H0.
  - destruct (fold_andb cleared) eqn:? ; inv H2. inv H. constructor. destruct cr as [cr ?H].
    simpl in *. f_equal. list_simplify. apply H2.
    + rewrite <- H. auto.
    + rewrite fold_andb_true in Heqb. apply Heqb. list_solve.
  - inv H. constructor.
    simpl. rewrite H1.
    rewrite map_app.
    rewrite fold_left_app.
    reflexivity.
Qed.

Definition row_clear (r : row) (i : Z) : option row :=
  match r with
  | Clear cleared =>
      Some (Clear (upd_Znth i cleared true))
  | Normal _ =>
      Some (Clear (upd_Znth i (Zrepeat false num_slots) true))
  end.

Lemma fold_left_pres : forall {A B} (f : A -> B -> A) bl a P,
  P a ->
  (forall a' b, P a' -> P (f a' b)) ->
  P (fold_left f bl a).
Proof.
  intros.
  generalize dependent a; induction bl; intros.
  - auto.
  - simpl. auto.
Qed.

Lemma fold_right_pres : forall {A B} (f : B -> A -> A) a bl P,
  P a ->
  (forall a' b, P a' -> P (f b a')) ->
  P (fold_right f a bl).
Proof.
  intros.
  induction bl.
  - auto.
  - simpl. auto.
Qed.

Lemma row_clear_sound : forall r cr i r',
  row_sim r cr ->
  row_clear r i = Some r' ->
  row_sim r' (ConFilter.row_clear cr i).
Proof.
  intros.
  destruct r; inv H; unfold row_clear in *; inv H0; constructor; intros;
    destruct cr as [cr ?H]; simpl in *; list_solve.
Qed.

Definition row_query (r : row) (h : header_type) : option bool :=
  match r with
  | Clear _ => None
  | Normal hs =>
      Some (fold_orb (map (Z.eqb (hash h) ∘ hash) hs))
  end.

Lemma row_query_sound : forall r cr h res,
  row_sim r cr ->
  row_query r h = Some res ->
  ConFilter.row_query cr (hash h) = res.
Proof.
  intros.
  destruct r; inv H0.
  inv H.
  unfold fold_orb.
  rewrite <- !fold_left_rev_right in *.
  rewrite <- !map_rev in *. destruct cr as [cr ?H].  simpl in *. subst cr.
  unfold ConFilter.row_query. simpl. clear H.
  generalize (rev hs) as hs0. clear hs; intro hs.
  induction hs as [ | h' hs]; simpl.
  - specialize (H_hash h). list_solve.
  - unfold compose.
    assert (Zlength (fold_right (fun (y : Z) (x : list bool) => upd_Znth y x true)
          (Zrepeat false num_slots) (map hash hs)) = num_slots). {
      apply fold_right_pres.
      { list_solve. }
      { list_solve. }
    }
    specialize (H_hash h).
    destruct (hash h =? hash h') eqn:H_hash_h.
    + rewrite Bool.orb_true_r.
      rewrite Znth_upd_Znth_same; auto; lia.
    + rewrite Bool.orb_false_r.
      rewrite Znth_upd_Znth_diff; auto; lia.
Qed.

End Row.

Section Frame.

Context (hashes : list (header_type -> Z)).
Hypothesis H_Zlength_hashes : Zlength hashes = num_rows.
Hypothesis H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.

Definition frame : Type := row.

Definition frame_sim (f : frame) (cf : ConFilter.frame num_rows num_slots) : Prop :=
  Forall2 (fun hash cr => row_sim hash f cr) hashes (`cf).

Definition frame_insert : forall (f : frame) (h : header_type), option frame :=
  row_insert.

Program Definition map_hashes (h: header_type) : listn Z num_rows :=
  map (fun hash => hash h) hashes.
Next Obligation.
  list_solve.
Qed.

#[local] Instance row_inhabitant: Inhabitant (ConFilter.row num_slots) :=
  empty_row num_slots H_num_slots.

Lemma frame_insert_sound : forall f cf h f',
  frame_sim f cf ->
  frame_insert f h = Some f' ->
  frame_sim f' (ConFilter.frame_insert cf (map_hashes h)).
Proof.
  intros.
  unfold frame_sim in *.
  unfold map_hashes.
  unfold ConFilter.frame_insert in *. simpl.
  rewrite Forall2_forall_range2.
  destruct cf as [cf ?H]. simpl in *. split. 1: list_solve.
  unfold forall_range2, forall_i; intros.
  rewrite Znth_map2 by list_solve.
  rewrite Znth_map by list_solve.
  replace (i + 0) with i by lia.
  apply row_insert_sound with f.
  - rewrite Forall2_forall_range2 in H.
    destruct H; list_solve.
  - list_solve.
Qed.

Definition frame_clear : forall (f : frame) (i : Z), option frame :=
  row_clear.

Program Definition repeat_num_rows {T: Type} (i: T): listn T num_rows :=
  Zrepeat i num_rows.
Next Obligation.
  list_solve.
Qed.

Lemma frame_clear_sound : forall f cf i f',
  frame_sim f cf ->
  frame_clear f i = Some f' ->
  frame_sim f' (ConFilter.frame_clear cf (repeat_num_rows i)).
Proof.
  intros.
  unfold frame_sim in *.
  unfold repeat_num_rows.
  unfold ConFilter.frame_clear in *. simpl.
  rewrite Forall2_forall_range2.
  destruct cf as [cf ?H]. simpl in *.
  split; only 1 : list_solve.
  unfold forall_range2, forall_i; intros.
  rewrite Znth_map2 by list_solve.
  apply row_clear_sound with f.
  - rewrite Forall2_forall_range2 in H.
    destruct H; list_solve.
  - list_solve.
Qed.

Definition frame_query (f : frame) (h : header_type) : option bool :=
  option_map fold_andb (Utils.lift_option (map (fun hash => row_query hash f h) hashes)).

Lemma inv_option_map {A B} : forall (f : A -> B) oa b,
  option_map f oa = Some b ->
  exists a, oa = Some a /\ f a = b.
Proof.
  intros. destruct oa; inv H.
  eexists; eauto.
Qed.

Ltac inv_option_map H :=
  apply inv_option_map in H; destruct H as [? [? ?]].

Lemma frame_query_sound : forall f cf h res,
  frame_sim f cf ->
  frame_query f h = Some res ->
  ConFilter.frame_query cf (map (fun hash => hash h) hashes) = res.
Proof.
  intros.
  unfold frame_query in H0.
  inv_option_map H0.
  apply Utils.lift_option_inv in H0.
  rewrite <- H1.
  unfold ConFilter.frame_query; f_equal.
  unfold frame_sim in H.
  destruct cf as [cf ?H]. simpl in *.
  assert (Zlength (map2 ConFilter.row_query cf (map (fun hash : header_type -> Z => hash h) hashes))
    = Zlength x). {
    list_solve.
  }
  apply Znth_eq_ext.
  { list_solve. }
  intros.
  rewrite Znth_map2 by list_solve.
  rewrite Znth_map by list_solve.
  apply row_query_sound with f.
  - rewrite Forall_forall_range in H_hashes.
    apply H_hashes. list_solve.
  - rewrite Forall2_forall_range2 in H.
    destruct H; list_solve.
  - list_solve.
Qed.

End Frame.


#[global] Instance frame_Inhabitant: Inhabitant frame := Normal [].

(*
Section sliding_mixin.

  Context (frames: list frame).
  Context (num_frames: Z).
  Context (clear_index insert_index: Z).

  Record SlidingMixin := {
      clear_index_range: 0 <= clear_index < num_frames;
      insert_index_range: 0 <= insert_index < num_frames;
      insert_clear_diff: insert_index <> clear_index;
      frame_size: Zlength frames = num_frames;
      clear_row_status: forall l, Znth clear_index frames <> Normal l;
      other_row_status: forall i, 0 <= i < num_frames -> i <> clear_index ->
                             forall j, Znth i frames <> Clear j;
  }.

End sliding_mixin.

Section Sliding.

  Lemma frame_insert_None_impsbl:
    forall (frames : list frame) (v : header_type)
      (num_frames clear_index insert_index : Z),
      SlidingMixin frames num_frames clear_index insert_index ->
      frame_insert (Znth insert_index frames) v = None -> False.
  Proof.
    intros frames v num_frames clear_index insert_index Hs H.
    pose proof (other_row_status _ _ _ _ Hs _
                  (insert_index_range _ _ _ _ Hs)
                  (insert_clear_diff _ _ _ _ Hs)).
    unfold frame_insert, row_insert in H. destruct (Znth insert_index frames) eqn:?H.
    - exfalso. apply (H0 i). auto.
    - inversion H.
  Qed.

  Lemma frame_insert_Some_f_not_Clear:
    forall (frames : list frame) (v : header_type) (num_frames clear_index insert_index : Z),
      SlidingMixin frames num_frames clear_index insert_index ->
      forall f : frame,
        frame_insert (Znth insert_index frames) v = Some f -> forall j : Z, f <> Clear j.
  Proof.
    intros ????? Hs f H ?. destruct (Znth insert_index frames) eqn:?H.
    - exfalso. eapply (other_row_status _ _ _ _ Hs insert_index); eauto.
      + eapply insert_index_range; eauto.
      + eapply insert_clear_diff; eauto.
    - simpl in H. inversion H. intro. inversion H1.
  Qed.

  Definition window_insert'
    (frames: list frame) (v: header_type) (num_frames clear_index insert_index: Z)
    (Hs: SlidingMixin frames num_frames clear_index insert_index):
    { frame | forall j, frame <> Clear j}.
  Proof.
    destruct (frame_insert (Znth insert_index frames) v) eqn:?H .
    - exists f. eapply frame_insert_Some_f_not_Clear; eauto.
    - exfalso. eapply frame_insert_None_impsbl; eauto.
  Defined.

  Lemma window_insert'_preserve:
    forall (frames: list frame) (v: header_type) (num_frames clear_index insert_index: Z)
      (Hs: SlidingMixin frames num_frames clear_index insert_index),
      SlidingMixin (upd_Znth insert_index frames
                      (proj1_sig
                         (window_insert' frames v num_frames clear_index insert_index Hs)))
        num_frames clear_index insert_index.
  Proof.
    intros. split.
    - eapply clear_index_range; eauto.
    - eapply insert_index_range; eauto.
    - eapply insert_clear_diff; eauto.
    - rewrite Zlength_upd_Znth. eapply frame_size; eauto.
    - intros. rewrite Znth_upd_Znth_diff.
      + eapply clear_row_status; eauto.
      + intro. symmetry in H. revert H. eapply insert_clear_diff; eauto.
    - intros. destruct (Z.eq_dec i insert_index).
      + subst. rewrite Znth_upd_Znth_same; auto.
        * remember (window_insert' frames v num_frames clear_index insert_index Hs).
          destruct s. simpl. apply n.
        * erewrite frame_size; eauto.
      + rewrite Znth_upd_Znth_diff; auto. eapply other_row_status; eauto.
  Qed.

  Record SlidingWindow := {
      frames: list frame;
      num_frames: Z;
      clear_index: Z;
      insert_index: Z;
      sliding_mixin: SlidingMixin frames num_frames clear_index insert_index;
    }.

  Definition window_insert (win: SlidingWindow) (v: header_type): SlidingWindow :=
    Build_SlidingWindow
      (upd_Znth (insert_index win) (frames win)
         (proj1_sig
            (window_insert' (frames win) v
               (num_frames win) (clear_index win) (insert_index win) (sliding_mixin win))))
      (num_frames win) (clear_index win) (insert_index win)
      (window_insert'_preserve (frames win) v
         (num_frames win) (clear_index win) (insert_index win) (sliding_mixin win)).

  Fixpoint remove_option {A: Type} (l: list (option A)) : list A :=
    match l with
    | nil => nil
    | None :: l' => remove_option l'
    | Some a :: l' => a :: remove_option l'
    end.

  Definition window_query (win: SlidingWindow)
    (hashes: list (header_type -> Z)) (h: header_type) :=
    fold_orb (remove_option (map (fun f => frame_query hashes f h) (frames win))).

End Sliding.

*)

End AbsFilter.
