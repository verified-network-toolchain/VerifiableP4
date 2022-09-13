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
Hypothesis H_num_frames : 2 <= num_frames.
Context (hashes : list (header_type -> Z)).
Hypothesis H_Zlength_hashes : Zlength hashes = num_rows.
Hypothesis H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.

Context (tick_time : Z).
Hypothesis (H_tick_time : 0 < tick_time).
Context (round_time : Z -> Z).

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
Definition Tc := (frame_time - 1) / num_slots + 1.

(* This should be provable *)
Axiom Tc_mul_num_slots_ge_frame_time : Tc * num_slots >= frame_time.
(* This seems NOT provable. *)
Axiom Tc_le_tick_time : Tc <= tick_time.
Lemma Tc_le_frame_time : Tc <= frame_time.
Admitted.
Lemma Tc_le_T : Tc <= frame_time.
Admitted.

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

(* Axiom filter_empty : filter. *)

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
  (* filter_inv f /\ *)
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      0 <= t - last_timestamp <= Tc /\ filter_inv f
        (* last_timestamp < window_hi /\
        (window_hi - 1 - last_timestamp) / Tc + num_clears >= num_slots *)
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
      0 <= t - new_timestamp <= Tc /\ filter_inv1 f new_timestamp
        (* new_timestamp < window_hi /\
        (window_hi - 1 - new_timestamp) / Tc + (num_clears + 1) >= num_slots *)
  | None => False
  end.

Lemma inv_refresh : forall f t,
  ok_until (Some f) t ->
  filter_inv1 (abs_refresh f t) t.
Proof.
Admitted.

(* Definition low_inv (f : filter) : forall  *)

Lemma weak_filter_inv1_abs_refresh : forall f t,
  weak_filter_inv (Some f) ->
  match abs_refresh f t with
  | Some f =>
      weak_filter_inv1 (Some f) t
  | None => True
  end.
Admitted.

(* filter_inv (abs_refresh f t) t. *)
Lemma abs_query_pattern_ok : forall f t h f' res,
  weak_filter_inv (Some f) ->
  abs_query f (t, h) = Some (f', res) ->
  filter_clear (Some f) t = Some f' /\ filter_query (filter_clear (Some f) t) (t, h) = Some res.
Proof.
  intros * ?H H_abs_query.
  unfold filter_clear, filter_query, abs_clear, abs_query in *.
  pose proof (weak_filter_inv1_abs_refresh f t ltac:(auto)).
  destruct (abs_refresh f t) as [[window_hi last_timestamp num_clears normal_frames] | ].
    2 : inv H_abs_query.
  unfold weak_filter_inv1 in *.
  assert ((t - window_hi) / frame_time + 1 = 0). {
    rewrite <- Zdiv.Z_div_plus by lia.
    apply Z.div_small; lia.
  }
  inv H_abs_query.
  split; only 1 : auto.
  replace (t <=? t) with true by lia.
  f_equal. f_equal.
  list_solve.
Qed.

Lemma ok_refresh : forall f t t',
  t <= t' <= t + Tc ->
  ok_until (Some f) t ->
  ok_until1 (abs_refresh f t) t t'.
Proof.
  (* intros * H_t' H_ok_until.
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
    pose Tc_mul_num_slots_ge_frame_time.
    admit.
  - simpl.
    split; only 1 : lia.
    split; only 1 : lia.
    assert ((window_hi - 1 - last_timestamp + (-1) * Tc) / Tc <= (window_hi - 1 - t) / Tc). {
      apply Z.div_le_mono. 2 : lia.
      admit.
    }
    rewrite Zdiv.Z_div_plus in * by admit.
    lia. *)
Admitted.

Lemma query_clear : forall f t t' h b,
  t <= t' ->
  ok_until f t ->
  filter_query f (t', h) = Some b ->
  filter_query (filter_clear f t) (t', h) = Some b.
Proof.
  intros.
Admitted.

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

Lemma query_insert_same : forall f t t' h,
  t <= t' <= t+T ->
  ok_until f t ->
  filter_query (filter_insert f (t, h)) (t', h) = Some true.
Proof.
  intros * H_t' H_ok_until.
  destruct f. 2 : inv H_ok_until.
  unfold filter_insert, abs_insert.
  pose proof (H_filter_inv1 := inv_refresh f t ltac:(auto)).
  destruct (abs_refresh f t) as [f' | ] in *. 2 : inv H_filter_inv1.
  destruct f'.
  unfold filter_query, filter_inv1 in *.
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
Admitted.

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

(* Lemma ok_empty: forall t,
  ok_until empty t. *)

End LightFilter.
