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

Definition filter_insert (f : filter) (th : Z * header_type) : filter :=
  match f with
  | Some f => abs_insert f th
  | None => None
  end.

(* TODO this is incorrect. *)
Definition filter_query (f : filter) (th : Z * header_type) : option bool :=
  match f with
  | Some f =>
      option_map snd (abs_query f th)
  | None => None
  end.

Definition filter_clear (f : filter) (t : Z) : filter :=
  match f with
  | Some f =>
      abs_clear f t
  | None => None
  end.

(* Axiom filter_empty : filter. *)

Definition ok_until (f : filter) (t : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      0 <= t - last_timestamp <= Tc /\
        last_timestamp < window_hi /\
        (window_hi - 1 - last_timestamp) / Tc + num_clears >= num_slots
  | None => False
  end.

Lemma query_clear : forall f t t' h b,
  ok_until f t ->
  filter_query f (t', h) = Some b ->
  filter_query (filter_clear f t) (t', h) = Some b.
Proof.
  intros.
Admitted.

Lemma query_insert_same : forall f t t' h,
  t <= t' < t+T ->
  ok_until f t ->
  filter_query (filter_insert f (t, h)) (t', h) = Some true.
Admitted.

Lemma query_insert_other : forall f t t' h h',
  ok_until f t ->
  filter_query f (t', h') = Some true ->
  filter_query (filter_insert f (t, h)) (t', h') = Some true.
Admitted.

Lemma ok_insert : forall f t t' h,
  t <= t' <= t + Tc ->
  ok_until f t ->
  ok_until (filter_insert f (t, h)) t'.
Admitted.

Notation abs_refresh := (@filter_refresh header_type num_frames num_slots frame_time tick_time).

Definition ok_until1 (f : filter) (new_timestamp : Z) (t : Z) : Prop :=
  match f with
  | Some (mk_filter window_hi _ num_clears normal_frames) =>
      0 <= t - new_timestamp <= Tc /\
        new_timestamp < window_hi /\
        (window_hi - 1 - new_timestamp) / Tc + (num_clears + 1) >= num_slots
  | None => False
  end.

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
    lia.
Admitted.

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
