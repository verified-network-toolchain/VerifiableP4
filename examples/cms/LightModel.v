Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import ProD3.core.Coqlib.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.cms.AbsModel.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section LightModel.

Context {header_type : Set}.
Context (num_frames num_rows num_slots frame_time : Z).
Hypothesis H_num_slots : 0 < num_slots.
Hypothesis H_num_rows : 0 < num_rows.
Hypothesis H_num_frames : 1 < num_frames.
Context (hashes : list (header_type -> Z)).
Hypothesis H_Zlength_hashes : Zlength hashes = num_rows.
Hypothesis H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.

Context (tick_time : Z).
Hypothesis (H_tick_time : 0 < tick_time).

Hypothesis (H_frame_time : 0 < frame_time).
Hypothesis (H_tick_time_div : (tick_time * 2 | frame_time)).

Definition filter := option (@cms header_type).

Notation abs_insert := (@cms_insert header_type num_frames num_slots frame_time tick_time).
Notation abs_query := (@cms_query header_type num_frames num_slots frame_time hashes tick_time).
Notation abs_clear := (@cms_clear header_type num_frames num_slots frame_time tick_time).
Notation abs_refresh := (@cms_refresh header_type num_frames num_slots frame_time tick_time).

(* The time of guaranteed query, e.g. 59s. *)
Definition T := frame_time * (num_frames - 2).

(* The maximum time interval between consecutive packets, e.g. 112us. *)
Definition Tc := frame_time / num_slots.

(* This should be provable *)
Lemma Tc_mul_num_slots_le_frame_time : Tc * num_slots <= frame_time.
Proof. unfold Tc. rewrite Z.mul_comm. apply Z.mul_div_le. assumption. Qed.
(* This seems NOT provable. *)
Axiom Tc_le_tick_time : Tc <= tick_time.

Lemma Tc_le_frame_time : Tc <= frame_time.
Proof.
  unfold Tc. apply Z.div_le_upper_bound; auto.
  rewrite Z.mul_comm. apply Z.le_mul_diag_r; lia.
Qed.

Axiom H_Tc : 0 < Tc.
(* Lemma Tc_le_T : Tc <= T.
Admitted. *)

Definition cms_insert (f : filter) (th : Z * header_type) : filter :=
  match f with
  | Some f => abs_insert f th
  | None => None
  end.

Definition cms_query (f : filter) '((t, h) : Z * header_type) : option Z :=
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      if last_timestamp <=? t then
        let num_invalid_frames := Z.min (Z.max ((t - window_hi) / frame_time + 1) 0) (num_frames - 1) in
        let valid_frames := sublist num_invalid_frames (num_frames - 1) normal_frames in
        let res := Zsum (map (fun hs => list_min (map (fun hash => Zsum (map (Z.b2z ∘ Z.eqb (hash h) ∘ hash) hs)) hashes)) valid_frames) in
        Some res
      else
        None
  | None => None
  end.

Definition cms_clear (f : filter) (t : Z) : filter :=
  match f with
  | Some f =>
      abs_clear f t
  | None => None
  end.

(* Axiom cms_empty : filter. *)

Definition weak_cms_inv (f : filter) : Prop :=
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      window_hi - frame_time <= last_timestamp < window_hi /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition cms_inv (f : filter) : Prop :=
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      last_timestamp < window_hi /\
      (window_hi - 1 - last_timestamp) / Tc + num_clears >= num_slots /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition ok_until (f : filter) (t : Z) : Prop :=
  (* cms_inv f /\ *)
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      0 <= t - last_timestamp <= Tc /\ cms_inv f
        (* last_timestamp < window_hi /\
        (window_hi - 1 - last_timestamp) / Tc + num_clears >= num_slots *)
  | None => False
  end.

Definition weak_cms_inv1 (f : filter) (new_timestamp : Z) : Prop :=
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      window_hi - frame_time <= new_timestamp < window_hi /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition cms_inv1 (f : filter) (new_timestamp : Z) : Prop :=
  match f with
  | Some (mk_cms window_hi last_timestamp num_clears normal_frames) =>
      new_timestamp < window_hi /\
      (window_hi - 1 - new_timestamp) / Tc + (num_clears + 1) >= num_slots /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition ok_until1 (f : filter) (new_timestamp : Z) (t : Z) : Prop :=
  match f with
  | Some (mk_cms window_hi _ num_clears normal_frames) =>
      0 <= t - new_timestamp <= Tc /\ cms_inv1 f new_timestamp
        (* new_timestamp < window_hi /\
        (window_hi - 1 - new_timestamp) / Tc + (num_clears + 1) >= num_slots *)
  | None => False
  end.

Lemma weak_cms_inv1_abs_refresh : forall f t,
  weak_cms_inv (Some f) ->
  match abs_refresh f t with
  | Some f =>
      weak_cms_inv1 (Some f) t
  | None => True
  end.
Proof.
  intros.
  unfold weak_cms_inv, weak_cms_inv1 in *.
  destruct f.
  unfold abs_refresh.
  destruct (last_timestamp <=? t) eqn:?H; only 2 : simpl; auto.
  destruct (t <=? last_timestamp + tick_time) eqn:?H; only 2 : simpl; auto.
  simpl andb. cbn match.
  destruct (t >=? window_hi) eqn:?H.
  - destruct (num_clears >=? num_slots); only 2 : auto.
    split.
    + assert (tick_time <= frame_time). {
        destruct H_tick_time_div as [z ?]. subst.
        replace (z * (tick_time * 2)) with (tick_time * (2 * z)) by lia.
        apply Z.le_mul_diag_r; lia. } lia.
    + list_solve.
  - lia.
Qed.

(* This lemma shows cms_query (cms_clear ..) is equal to abs_query. *)
Lemma abs_query_pattern_ok : forall f t h res,
  weak_cms_inv (Some f) ->
  cms_query (cms_clear (Some f) t) (t, h) = Some res ->
  exists f', abs_query f (t, h) = Some (f', res).
Proof.
  intros * ?H H_cms_query.
  unfold cms_clear, cms_query, abs_clear, abs_query in *.
  pose proof (weak_cms_inv1_abs_refresh f t ltac:(auto)).
  destruct (abs_refresh f t) as [[window_hi last_timestamp num_clears normal_frames] | ].
    2 : inv H_cms_query.
  unfold weak_cms_inv1 in *.
  assert ((t - window_hi) / frame_time + 1 = 0). {
    rewrite <- Zdiv.Z_div_plus by lia.
    apply Z.div_small; lia.
  }
  destruct (t <=? t) eqn:?H.
    2 : inv H_cms_query.
  eexists. f_equal. f_equal.
  inv H_cms_query.
  f_equal. list_solve.
Qed.

Lemma ok_refresh : forall f t t',
  t <= t' <= t + Tc ->
  ok_until (Some f) t ->
  ok_until1 (abs_refresh f t) t t'.
Proof.
  intros * H_t' H_ok_until.
  destruct f as [window_hi last_timestamp num_clears normal_frames].
  simpl in *.
  replace (last_timestamp <=? t) with true by lia.
  replace (t <=? last_timestamp + tick_time) with true by (pose Tc_le_tick_time; lia).
  destruct (t >=? window_hi) eqn:?H.
  - assert (0 <= window_hi - 1 - last_timestamp < Tc) by (pose Tc_le_tick_time; lia).
    rewrite Z.div_small in H_ok_until by lia.
    replace (num_clears >=? num_slots) with true by lia.
    simpl.
    split; only 1 : lia.
    split; only 1 : (pose Tc_le_frame_time; lia).
    split; only 2 : list_solve.
    pose proof Tc_mul_num_slots_le_frame_time.
    assert (window_hi - t >= 1 - Tc) by lia.
    assert ((window_hi + frame_time - 1 - t) / Tc + 1 >= frame_time / Tc). {
      replace (frame_time / Tc) with ((frame_time - Tc) / Tc + 1).
      - apply Z.le_ge, Z.add_le_mono_r, Z.ge_le, Zdiv.Z_div_ge; lia.
      - rewrite <- Z.add_opp_r. change (- Tc) with ((- 1) * Tc).
        rewrite Z.div_add; lia. }
    apply Zorder.Zge_trans with (frame_time / Tc); auto.
    apply Z.div_le_mono with (c := Tc) in H1. 2: lia.
    rewrite Z.mul_comm, Z.div_mul in H1; lia.
  - simpl.
    split; only 1 : lia.
    split; only 1 : lia.
    split; only 2 : lia.
    assert ((window_hi - 1 - last_timestamp + (-1) * Tc) / Tc <= (window_hi - 1 - t) / Tc). {
      apply Z.div_le_mono. 2 : lia.
      apply H_Tc.
    }
    rewrite Zdiv.Z_div_plus in * by (pose proof H_Tc; lia).
    lia.
Qed.

Lemma query_clear : forall f t t' h,
  t <= t' ->
  ok_until f t ->
  cms_query f (t', h) = cms_query (cms_clear f t) (t', h).
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  destruct c as [window_hi last_timestamp num_clears normal_frames].
  unfold cms_clear, abs_clear, abs_refresh, ok_until, cms_inv in *.
  replace (last_timestamp <=? t) with true by lia.
  replace (t <=? last_timestamp + tick_time) with true by (pose Tc_le_tick_time; lia).
  destruct (t >=? window_hi) eqn:?H.
  - assert (0 <= window_hi - 1 - last_timestamp < Tc) by (pose Tc_le_tick_time; lia).
    rewrite Z.div_small in H_ok_until by lia.
    replace (num_clears >=? num_slots) with true by lia.
    cbn -[cms_query sublist].
    unfold cms_query.
    replace (last_timestamp <=? t') with true by lia.
    replace (t <=? t') with true by lia.
    remember (Z.max ((t' - window_hi) / frame_time + 1) 0) as k eqn:?H.
    assert ((t' - window_hi) / frame_time >= 0). {
      apply Zdiv.Z_div_ge0; lia.
    }
    replace (Z.max ((t' - (window_hi + frame_time)) / frame_time + 1) 0) with (k - 1). 2 : {
      replace (t' - (window_hi + frame_time)) with (t' - window_hi + (-1) * frame_time) by lia.
      rewrite Z.div_add by lia.
      lia.
    }
    destruct (k - 1 >=? (num_frames - 1)) eqn:?H.
    { replace (sublist (Z.min k (num_frames - 1)) (num_frames - 1) _)
        with (@nil (list header_type)) by list_solve.
      replace (sublist (Z.min (k - 1) (num_frames - 1)) (num_frames - 1) _)
        with (@nil (list header_type)) by list_solve.
      auto.
    }
    destruct (k >=? (num_frames - 1)) eqn:?H.
    { replace (sublist (Z.min k (num_frames - 1)) (num_frames - 1) _)
        with (@nil (list header_type)) by list_solve.
      replace (sublist (Z.min (k - 1) (num_frames - 1)) (num_frames - 1) _)
        with ([@nil header_type]) by list_solve.
      destruct hashes as [ | hash0 hashes']. 1 : list_solve. unfold Zsum. simpl.
      clear. induction hashes'; simpl; auto.
    }
    replace (sublist (Z.min k (num_frames - 1)) (num_frames - 1) _)
        with (sublist k (num_frames - 1) normal_frames) by list_solve.
    replace (sublist (Z.min (k - 1) (num_frames - 1)) (num_frames - 1) _)
      with (sublist k (num_frames - 1) normal_frames ++ [[]]) by list_solve.
    rewrite map_app. simpl.
    replace (list_min (map (fun _ : header_type -> Z => Zsum []) hashes)) with 0.
    2: { unfold Zsum. simpl. destruct hashes as [ | hash0 hashes']. 1 : list_solve.
         simpl. clear. induction hashes'; simpl; auto. }
    rewrite Zsum_app. replace (Zsum [0]) with 0 by (unfold Zsum; now simpl).
    rewrite Z.add_0_r. auto.
  - simpl.
    replace (last_timestamp <=? t') with true by lia.
    replace (t <=? t') with true by lia.
    auto.
Qed.

Lemma ok_until_query_some : forall f t t' h,
    t <= t' ->
    ok_until f t ->
    exists k, cms_query f (t', h) = Some k.
Proof.
  intros f t t' h Ht' H_ok_until.
  destruct f. 2: inv H_ok_until. red in H_ok_until. destruct c.
  destruct H_ok_until as [[Ht _] _]. simpl.
  destruct (last_timestamp <=? t') eqn:Hlt. 2: lia.
  match goal with
  | |- exists _, Some ?i = Some _ => exists i; reflexivity
  end.
Qed.

Lemma query_insert_same : forall f t t' h k,
  t <= t' <= t + T ->
  ok_until f t ->
  cms_query f (t', h) = Some k ->
  cms_query (cms_insert f (t, h)) (t', h) = Some (k + 1).
Proof.
  intros f t t' h k Ht' H_ok_until H_cms_query.
  assert (H_query_clear : cms_query (cms_clear f t) (t', h) = Some k). {
    erewrite <- query_clear; eauto. lia.
  }
  clear H_cms_query.
  unfold cms_clear, abs_clear, cms_insert, abs_insert in *.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh c t t ltac:(pose proof H_Tc; lia) ltac:(auto)).
  destruct (abs_refresh c t) as [f' | ] in *. 2 : inv H_ok_refresh.
  destruct f'.
  unfold cms_query, ok_until1, cms_inv1 in *.
  destruct (t <=? t') eqn:?H. 2 : inv H_query_clear.
  injection H_query_clear; clear H_query_clear; intros H_query_clear. f_equal.
  remember (fun hs: list header_type => _) as f.
  remember (Z.min (Z.max ((t' - window_hi) / frame_time + 1) 0) (num_frames - 1)) as lo.
  assert ((t' - window_hi) / frame_time < num_frames - 2). {
    apply Z.div_lt_upper_bound. 1 : lia.
    fold T.
    lia.
  }
  assert (0 <= lo < num_frames - 1) by (subst lo; lia).
  rewrite (sublist_split lo (num_frames - 2) (num_frames - 1)) in H_query_clear |- *
      by list_solve.
  rewrite map_app, Zsum_app in *.
  rewrite sublist_upd_Znth_l by lia.
  replace (num_frames - 1) with (num_frames - 2 + 1) in H_query_clear |- * by lia.
  rewrite sublist_len_1 in * by list_solve.
  remember (Zsum (map f (sublist lo (num_frames - 2) normal_frames))) as m. clear Heqm.
  unfold Zsum in H_query_clear |- *. simpl in H_query_clear |- *.
  rewrite upd_Znth_same in * by lia. subst f.
  remember (fun hash : header_type -> Z =>
              Zsum (map (Z.b2z ∘ Z.eqb (hash h) ∘ hash)
                      (Znth (num_frames - 2) normal_frames ++ [h]))) as f.
  remember (fun hash : header_type -> Z =>
              Zsum (map (Z.b2z ∘ Z.eqb (hash h) ∘ hash)
                      (Znth (num_frames - 2) normal_frames))) as g.
  assert (forall hash, f hash = g hash + 1). {
    intros. subst. rewrite map_app, Zsum_app. f_equal. unfold Zsum, compose. simpl.
    rewrite Z.eqb_refl. reflexivity. }
  rewrite <- (map_ext (fun hash => g hash + 1)).
  2: { intros; rewrite H2; reflexivity. }
  rewrite list_min_map_add; lia.
Qed.

Lemma list_min_diff_at_most_one: forall (l1 l2: list Z),
    0 < Zlength l1 ->
    Zlength l1 = Zlength l2 ->
    (forall i, 0 <= i < Zlength l1 -> Znth i l1 = Znth i l2 \/ Znth i l1 = Znth i l2 + 1) ->
    list_min l1 = list_min l2 \/ list_min l1 = list_min l2 + 1.
Proof.
  intros l1 l2 Hgt Hl Hd. destruct l1. 1: list_solve. simpl.
  destruct l2. 1: list_solve. simpl.
  assert (Hl': Zlength l1 = Zlength l2) by list_solve.
  assert (Hd': forall i, 0 <= i < Zlength l1 ->
                    Znth i l1 = Znth i l2 \/ Znth i l1 = Znth i l2 + 1). {
    intros. assert (Hp: 0 <= i + 1 < Zlength (z :: l1)) by list_solve. specialize (Hd _ Hp).
    list_solve. }
  specialize (Hd 0 ltac:(lia)). rewrite !Znth_0_cons in Hd. clear Hgt Hl.
  revert l1 l2 z z0 Hd Hl' Hd'. induction l1; intros l2 z z0 Hd1 Hl Hd; simpl.
  - destruct l2. 2: list_solve. simpl. assumption.
  - destruct l2 as [|b l2]. 1: list_solve. simpl. apply IHl1. 2: list_solve.
    + specialize (Hd 0 ltac:(list_solve)). list_solve.
    + intros. specialize (Hd (i + 1) ltac:(list_solve)). list_solve.
Qed.

Lemma query_insert_other : forall f t t' h h' k,
  t <= t' ->
  ok_until f t ->
  cms_query f (t', h') = Some k ->
  cms_query (cms_insert f (t, h)) (t', h') = Some k \/
    cms_query (cms_insert f (t, h)) (t', h') = Some (k + 1).
Proof.
  intros f t t' h h' k H_t' H_ok_until H_cms_query.
  assert (H_query_clear : cms_query (cms_clear f t) (t', h') = Some k). {
    erewrite <- query_clear; eauto.
  }
  clear H_cms_query.
  unfold cms_clear, abs_clear, cms_insert, abs_insert in *.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh c t t ltac:(pose proof H_Tc; lia) ltac:(auto)).
  destruct (abs_refresh c t) as [f' | ] eqn:?H. 2 : inv H_query_clear.
  destruct f' as [window_hi last_timestamp num_clears normal_frames].
  unfold cms_query in *.
  destruct (t <=? t') eqn:?H. 2 : inv H_query_clear.
  injection H_query_clear; clear H_query_clear; intros H_query_clear.
  remember (fun hs: list header_type => _) as f.
  assert (Hl: Zlength normal_frames = num_frames - 1) by apply H_ok_refresh.
  remember (Z.min (Z.max ((t' - window_hi) / frame_time + 1) 0) (num_frames - 1)) as lo.
  destruct (Z_le_lt_dec (num_frames - 2) ((t' - window_hi) / frame_time)).
  - assert (num_frames - 1 <= lo) by lia.
    rewrite sublist_over in H_query_clear |- * by list_solve.
    left. f_equal. assumption.
  - assert (0 <= lo < num_frames - 1) by (subst lo; lia).
    rewrite (sublist_split lo (num_frames - 2) (num_frames - 1)) in H_query_clear |- *
        by list_solve.
    rewrite map_app, Zsum_app in *.
    rewrite sublist_upd_Znth_l by lia.
    replace (num_frames - 1) with (num_frames - 2 + 1) in H_query_clear |- * by lia.
    rewrite sublist_len_1 in * by list_solve.
    remember (Zsum (map f (sublist lo (num_frames - 2) normal_frames))) as m. clear Heqm.
    unfold Zsum in H_query_clear |- *. simpl in H_query_clear |- *.
    rewrite upd_Znth_same in * by lia. subst f.
    remember (fun hash : header_type -> Z =>
                Zsum (map (Z.b2z ∘ Z.eqb (hash h') ∘ hash)
                        (Znth (num_frames - 2) normal_frames ++ [h]))) as f.
    remember (fun hash : header_type -> Z =>
                Zsum (map (Z.b2z ∘ Z.eqb (hash h') ∘ hash)
                        (Znth (num_frames - 2) normal_frames))) as g.
    assert (forall hash, f hash = g hash \/ f hash = g hash + 1). {
      intros. subst. rewrite map_app, Zsum_app. unfold Zsum, compose. simpl.
      destruct (hash h' =? hash h); simpl; lia. }
    cut (list_min (map f hashes) = list_min (map g hashes) \/
           list_min (map f hashes) = list_min (map g hashes) + 1).
    + intros Hmin. destruct Hmin; [left | right]; f_equal; lia.
    + apply list_min_diff_at_most_one; list_solve.
Qed.

Lemma ok_insert : forall f t t' h,
  t <= t' <= t + Tc ->
  ok_until f t ->
  ok_until (cms_insert f (t, h)) t'.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh c t t' ltac:(auto) ltac:(auto)).
  unfold cms_insert, abs_insert in *.
  destruct (abs_refresh c t). 2 : inv H_ok_refresh.
  destruct c0.
  unfold ok_until, cms_inv.
  rewrite Zlength_upd_Znth.
  apply H_ok_refresh.
Qed.

Lemma ok_clear : forall f t t',
  t <= t' <= t + Tc ->
  ok_until f t ->
  ok_until (cms_clear f t) t'.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh c t t' ltac:(auto) ltac:(auto)).
  unfold cms_clear, abs_clear in *.
  destruct (abs_refresh c t). 2 : inv H_ok_refresh.
  destruct c0. apply H_ok_refresh.
Qed.

End LightModel.
