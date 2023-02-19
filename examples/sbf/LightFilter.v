Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import ProD3.core.Coqlib.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.AbsFilter.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section LightFilter.

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

Definition filter := option (@filter header_type).

Notation abs_insert := (@filter_insert header_type num_frames num_slots frame_time tick_time).
Notation abs_query := (@filter_query header_type num_frames num_slots frame_time hashes tick_time).
Notation abs_clear := (@filter_clear header_type num_frames num_slots frame_time tick_time).
Notation abs_refresh := (@filter_refresh header_type num_frames num_slots frame_time tick_time).

(* The time of guaranteed query, e.g. 59s. *)
Definition T := frame_time * (num_frames - 2).

(* The maximum time interval between consecutive packets, e.g. 112us. *)
Definition Tc := Z.min (frame_time / num_slots) tick_time.

Lemma Tc_mul_num_slots_le_frame_time : Tc * num_slots <= frame_time.
Proof.
  unfold Tc.
  assert (frame_time / num_slots * num_slots <= frame_time). {
    rewrite Z.mul_comm. apply Z.mul_div_le. assumption.
  }
  nia.
Qed.

Lemma Tc_le_tick_time : Tc <= tick_time.
Proof. unfold Tc; lia. Qed.

Lemma tick_time_le_frame_time : tick_time <= frame_time.
Proof.
  destruct H_tick_time_div as [x ?].
  assert (x > 0) by nia.
  assert (frame_time = tick_time + (x * 2 - 1) * tick_time) by nia.
  assert (x * 2 - 1 > 0) by lia.
  nia.
Qed.

Lemma Tc_le_frame_time : Tc <= frame_time.
Proof.
  rewrite Tc_le_tick_time. apply tick_time_le_frame_time.
Qed.

Lemma tick_time_mul_2_le_frame_time : tick_time * 2 <= frame_time.
Proof.
  destruct H_tick_time_div as [x ?].
  assert (x > 0) by nia.
  nia.
Qed.

Hypothesis H_Tc : 0 < Tc.

Definition filter_insert (f : filter) (th : Z * header_type) : filter :=
  match f with
  | Some f => abs_insert f th
  | None => None
  end.

Definition filter_query (f : filter) '((t, h) : Z * header_type) : option bool :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      if last_timestamp <=? t then
        let num_invalid_frames := Z.min (Z.max ((t - window_hi) / frame_time + 1) 0) (num_frames - 1) in
        let valid_frames := sublist num_invalid_frames (num_frames - 1) normal_frames in
        let res := existsb (fun hs => forallb (fun hash => fold_orb (map (Z.eqb (hash h) ∘ hash) hs)) hashes) valid_frames in
        Some res
      else
        None
  | None => None
  end.

Definition filter_clear (f : filter) (t : Z) : filter :=
  match f with
  | Some f =>
      abs_clear f t
  | None => None
  end.

Definition filter_empty (t : Z) : filter :=
  Some (AbsFilter.filter_empty num_frames num_slots frame_time tick_time t).

Definition weak_filter_inv (f : filter) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      window_hi - frame_time <= last_timestamp < window_hi /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition filter_inv (f : filter) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      last_timestamp < window_hi /\
      (window_hi - 1 - last_timestamp) / Tc + num_clears >= num_slots /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition ok_until (f : filter) (t : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      (0 <= t - last_timestamp <= Tc \/ num_clears >= num_slots /\ t < window_hi /\ 0 <= t - last_timestamp <= tick_time) /\ filter_inv f
  | None => False
  end.

Definition weak_filter_inv1 (f : filter) (new_timestamp : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      window_hi - frame_time <= new_timestamp < window_hi /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition filter_inv1 (f : filter) (new_timestamp : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      new_timestamp < window_hi /\
      (window_hi - 1 - new_timestamp) / Tc + (num_clears + 1) >= num_slots /\
      Zlength normal_frames = num_frames - 1
  | None => False
  end.

Definition ok_until1 (f : filter) (new_timestamp : Z) (t : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi _ num_clears normal_frames) =>
      (0 <= t - new_timestamp <= Tc \/ num_clears + 1 >= num_slots /\ t < window_hi /\ 0 <= t - new_timestamp <= tick_time) /\ filter_inv1 f new_timestamp
  | None => False
  end.

Lemma weak_filter_inv1_abs_refresh : forall f t,
  weak_filter_inv (Some f) ->
  match abs_refresh f t with
  | Some f =>
      weak_filter_inv1 (Some f) t
  | None => True
  end.
Proof.
  intros.
  unfold weak_filter_inv, weak_filter_inv1 in *.
  destruct f.
  unfold abs_refresh.
  destruct (last_timestamp <=? t) eqn:?H; only 2 : simpl; auto.
  destruct (t <=? last_timestamp + tick_time) eqn:?H; only 2 : simpl; auto.
  simpl andb. cbn match.
  destruct (t >=? window_hi) eqn:?H.
  - destruct (num_clears >=? num_slots); only 2 : auto.
    split.
    + pose proof tick_time_le_frame_time; lia.
    + list_solve.
  - lia.
Qed.

(* This lemma shows filter_query (filter_clear ..) is equal to abs_query. *)
Lemma abs_query_pattern_ok : forall f t h res,
  weak_filter_inv (Some f) ->
  filter_query (filter_clear (Some f) t) (t, h) = Some res ->
  exists f', abs_query f (t, h) = Some (f', res).
Proof.
  intros * ?H H_filter_query.
  unfold filter_clear, filter_query, abs_clear, abs_query in *.
  pose proof (weak_filter_inv1_abs_refresh f t ltac:(auto)).
  destruct (abs_refresh f t) as [[window_hi last_timestamp num_clears normal_frames] | ].
    2 : inv H_filter_query.
  unfold weak_filter_inv1 in *.
  assert ((t - window_hi) / frame_time + 1 = 0). {
    rewrite <- Zdiv.Z_div_plus by lia.
    apply Z.div_small; lia.
  }
  destruct (t <=? t) eqn:?H.
    2 : inv H_filter_query.
  eexists. f_equal. f_equal.
  inv H_filter_query.
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
  - replace (num_clears >=? num_slots) with true. 2 : {
      destruct H_ok_until as [[] H_ok_until]. 2 : lia.
      assert (0 <= window_hi - 1 - last_timestamp < Tc) by lia.
      rewrite Z.div_small in H_ok_until by lia.
      lia.
    }
    simpl.
    split; only 1 : lia.
    split; only 1 : (pose Tc_le_frame_time; pose tick_time_le_frame_time; lia).
    split; only 2 : list_solve.
    pose proof Tc_mul_num_slots_le_frame_time.
    assert (window_hi - t >= 1 - Tc) by lia.
    assert ((window_hi + frame_time - 1 - t) / Tc + 1 >= frame_time / Tc). {
      replace (frame_time / Tc) with ((frame_time - Tc) / Tc + 1).
      - apply Z.le_ge, Z.add_le_mono_r, Z.ge_le, Zdiv.Z_div_ge; lia.
      - rewrite <- Z.add_opp_r. change (- Tc) with ((- 1) * Tc).
        rewrite Z.div_add; lia. }
    apply Zorder.Zge_trans with (frame_time / Tc); auto.
    apply Z.div_le_mono with (c := Tc) in H0. 2: lia.
    rewrite Z.mul_comm, Z.div_mul in H0; lia.
  - simpl.
    split; only 1 : lia.
    split; only 1 : lia.
    split; only 2 : lia.
    destruct H_ok_until as [[] ?].
    + assert ((window_hi - 1 - last_timestamp + (-1) * Tc) / Tc <= (window_hi - 1 - t) / Tc). {
        apply Z.div_le_mono. 2 : lia.
        apply H_Tc.
      }
      rewrite Zdiv.Z_div_plus in * by (pose proof H_Tc; lia).
      lia.
    + pose proof (H2 := Z.div_le_mono 0 (window_hi - 1 - t) Tc H_Tc).
      rewrite Z.div_0_l in H2 by (pose H_Tc; lia).
      lia.
Qed.

Lemma existsb_Znth_true : forall {A} {d : Inhabitant A} (f : A -> bool) l i,
  0 <= i < Zlength l ->
  f (Znth i l) = true ->
  existsb f l = true.
Proof.
  induction l; intros.
  - list_solve.
  - destruct (i =? 0) eqn:?H.
    + simpl.
      replace (f a) with true by list_solve.
      auto.
    + specialize (IHl (i-1) ltac:(list_solve) ltac:(list_solve)).
      simpl.
      rewrite IHl.
      destruct (f a); auto.
Qed.

Lemma existsb_true_Znth : forall {A} {d : Inhabitant A} (f : A -> bool) l,
  existsb f l = true ->
  exists i, 0 <= i < Zlength l /\
    f (Znth i l) = true.
Proof.
  induction l; intros.
  - inv H.
  - simpl in H. destruct (f a) eqn:?H.
    + exists 0. list_solve.
    + specialize (IHl ltac:(sfirstorder)).
      destruct IHl as [i []].
      exists (i + 1).
      list_solve.
Qed.

Lemma forallb_Znth_true : forall {A} {d : Inhabitant A} (f : A -> bool) l,
  forall_range 0 (Zlength l) l (fun x => f x = true) ->
  forallb f l = true.
Proof.
  induction l; intros.
  - list_solve.
  - simpl.
    replace (f a) with true by (specialize (H 0 ltac:(list_solve)); list_solve).
    apply IHl. list_solve.
Qed.

Lemma forallb_true_Znth : forall {A} {d : Inhabitant A} (f : A -> bool) l,
  forallb f l = true ->
  forall_range 0 (Zlength l) l (fun x => f x = true).
Proof.
  induction l; intros.
  - list_solve.
  - simpl in H.
    destruct (f a) eqn:?H; only 2 : inv H.
    specialize (IHl ltac:(auto)).
    list_solve.
Qed.

Lemma query_clear : forall f t t' h,
  t <= t' ->
  ok_until f t ->
  filter_query f (t', h) = filter_query (filter_clear f t) (t', h).
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  destruct f as [window_hi last_timestamp num_clears normal_frames].
  unfold filter_clear, abs_clear, abs_refresh, ok_until, filter_inv in *.
  replace (last_timestamp <=? t) with true by lia.
  replace (t <=? last_timestamp + tick_time) with true by (pose Tc_le_tick_time; lia).
  destruct (t >=? window_hi) eqn:?H.
  - assert (0 <= window_hi - 1 - last_timestamp < Tc) by (pose Tc_le_tick_time; lia).
    rewrite Z.div_small in H_ok_until by lia.
    replace (num_clears >=? num_slots) with true by lia.
    cbn -[filter_query sublist].
    unfold filter_query.
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
      destruct hashes as [ | hash0 hashes']. 1 : list_solve.
      auto.
    }
    replace (sublist (Z.min k (num_frames - 1)) (num_frames - 1) _)
        with (sublist k (num_frames - 1) normal_frames) by list_solve.
    replace (sublist (Z.min (k - 1) (num_frames - 1)) (num_frames - 1) _)
        with (sublist k (num_frames - 1) normal_frames ++ [[]]) by list_solve.
    rewrite existsb_app.
    destruct hashes as [ | hash0 hashes']. 1 : list_solve.
    simpl.
    rewrite orbF.
    auto.
  - simpl.
    replace (last_timestamp <=? t') with true by lia.
    replace (t <=? t') with true by lia.
    auto.
Qed.

Lemma query_insert_same : forall f t t' h,
  t <= t' <= t+T ->
  ok_until f t ->
  filter_query (filter_insert f (t, h)) (t', h) = Some true.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  unfold filter_insert, abs_insert.
  pose proof (H_ok_refresh := ok_refresh f t t ltac:(pose proof H_Tc; lia) ltac:(auto)).
  destruct (abs_refresh f t) as [f' | ] in *. 2 : inv H_ok_refresh.
  destruct f'.
  unfold filter_query, ok_until1, filter_inv1 in *.
  replace (t <=? t') with true by lia.
  assert ((t' - window_hi) / frame_time < num_frames - 2). {
    apply Z.div_lt_upper_bound. 1 : lia.
    fold T.
    lia.
  }
  f_equal.
  apply existsb_Znth_true with (i := num_frames - 2 - Z.max ((t' - window_hi) / frame_time + 1) 0).
  { list_solve. }
  rewrite forallb_fold_andb.
  apply fold_andb_true; list_simplify; intros.
  rewrite <- existsb_fold_orb.
  list_simplify.
  rewrite existsb_app.
  simpl.
  unfold compose.
  replace (Znth i hashes h =? Znth i hashes h) with true by lia.
  rewrite orbF.
  rewrite orbT.
  auto.
Qed.

Lemma query_insert_other : forall f t t' h h',
  t <= t' ->
  ok_until f t ->
  filter_query f (t', h') = Some true ->
  filter_query (filter_insert f (t, h)) (t', h') = Some true.
Proof.
  intros * H_t' H_ok_until H_filter_query.
  assert (H_query_clear : filter_query (filter_clear f t) (t', h') = Some true). {
    erewrite <- query_clear; eauto.
  }
  clear H_filter_query.
  unfold filter_clear, abs_clear, filter_insert, abs_insert in *.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh f t t ltac:(pose proof H_Tc; lia) ltac:(auto)).
  destruct (abs_refresh f t) as [f' | ] eqn:?H. 2 : inv H_query_clear.
  destruct f' as [window_hi last_timestamp num_clears normal_frames].
  unfold filter_query in *.
  destruct (t <=? t') eqn:?H. 2 : inv H_query_clear.
  injection H_query_clear; clear H_query_clear; intros H_query_clear. f_equal.
  apply existsb_true_Znth in H_query_clear.
  destruct H_query_clear as [i []].
  assert (Zlength normal_frames = num_frames - 1). {
    apply H_ok_refresh.
  }
  apply existsb_Znth_true with (i := i).
  { list_solve. }
  list_simplify.
  rewrite e in H2.
  clear -H2.
  apply forallb_true_Znth in H2.
  apply forallb_Znth_true.
  list_simplify.
  rewrite <- existsb_fold_orb in *.
  rewrite existsb_app.
  clear -H5; hauto lq: on.
Qed.

Lemma ok_insert : forall f t t' h,
  t <= t' <= t + Tc ->
  ok_until f t ->
  ok_until (filter_insert f (t, h)) t'.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh f t t' ltac:(auto) ltac:(auto)).
  unfold filter_insert, abs_insert in *.
  destruct (abs_refresh f t). 2 : inv H_ok_refresh.
  destruct f0.
  unfold ok_until, filter_inv.
  rewrite Zlength_upd_Znth.
  unfold ok_until1 in H_ok_refresh.
  apply H_ok_refresh.
Qed.

Lemma ok_clear : forall f t t',
  t <= t' <= t + Tc ->
  ok_until f t ->
  ok_until (filter_clear f t) t'.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  pose proof (H_ok_refresh := ok_refresh f t t' ltac:(auto) ltac:(auto)).
  unfold filter_clear, abs_clear in *.
  destruct (abs_refresh f t). 2 : inv H_ok_refresh.
  destruct f0. apply H_ok_refresh.
Qed.

Lemma ok_empty: forall t,
  ok_until (filter_empty t) t.
Proof.
  intros.
  unfold ok_until, filter_empty, AbsFilter.filter_empty, filter_inv.
  pose proof (Zdiv_mul_pos_bound t (tick_time * 2) ltac:(lia)).
  pose proof Tc_le_tick_time; pose proof H_Tc; pose proof tick_time_mul_2_le_frame_time.
  split.
  { right.
    repeat apply conj; try lia.
  }
  { repeat apply conj; try lia.
    - match goal with
      | |- context [?a / ?b] =>
        pose proof (Zdiv.Z_div_ge0 a b ltac:(lia) ltac:(lia))
      end.
      lia.
    - list_solve.
  }
Qed.

End LightFilter.
