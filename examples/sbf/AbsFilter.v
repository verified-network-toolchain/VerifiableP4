Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section AbsFilter.

Context {header_type : Set}.
Context {Inhabitant_header_type : Inhabitant header_type}.

Context (num_frames num_rows num_slots frame_time : Z).
Hypothesis H_num_slots : 0 < num_slots.
Hypothesis H_num_rows : 0 < num_rows.

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

#[local] Program Instance Inhabitant_row : Inhabitant (ConFilter.row num_slots) :=
  ConFilter.Inhabitant_row _.

Lemma frame_sim_clear_Zlength: forall cl cf, frame_sim (Clear cl) cf -> Zlength cl = num_slots.
Proof.
  intros. red in H. rewrite Forall2_forall_Znth in H. destruct H.
  destruct cf as [cf ?H]. simpl in *. assert (0 <= 0 < Zlength hashes) by lia.
  apply H0 in H2. now inv H2.
Qed.

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

#[global] Instance frame_Inhabitant: Inhabitant frame := Normal [].

(* We might need it to be at least 2. *)
Hypothesis H_num_frames : 2 <= num_frames.

(* I would like to define it like this, but it looks hard to prove. *)
(* Inductive filter : Type :=
  | mk_filter (window_lo : Z) (num_clears : Z) (hs : list (Z * header_type)). *)

Record filter : Type := mk_filter {
  (* window_hi describes that the current range of query is [window_lo, window_hi), where
    window_lo = window_hi - (num_frames - 1) * frame_time.
    last_timestamp is the timestamp of last packet.
    num_clears is number of clear operations we have done to the frame that is being cleared.
    normal_frames is the list of contents of the (num_frames - 1) normal frames. *)
  window_hi : Z;
  last_timestamp : Z;
  num_clears : Z;
  normal_frames : list (list header_type)
}.

(* The concrete filter's timer uses a bit to detect time. We say the bit flipping from 0 to 1
  is a tick and flipping from 1 to 0 is a tock. tick_time is the time interval of a tick
  (and the time interval of a tock as well). *)
Context (tick_time : Z).
Hypothesis (H_tick_time : 0 < tick_time).
(* round_time can be defined. But it is annoying to have tick_time in abstract operations. *)
Context (round_time : Z -> Z).
(* Definition round_time (t : Z) :=
  t mod (tick_time * 2) * (tick_time * 2). *)

Hypothesis (H_frame_time : 0 < frame_time).
Hypothesis (H_tick_time_div : (tick_time * 2 | frame_time)).

Definition frame_tick_tocks := frame_time / (tick_time * 2).

Lemma H_frame_tick_tocks : tick_time * 2 * frame_tick_tocks = frame_time.
Proof.
  unfold frame_tick_tocks.
  destruct H_tick_time_div. subst frame_time.
  rewrite Z.div_mul by lia. lia.
Qed.

#[global] Instance con_frame_Inhabitant : Inhabitant (ConFilter.frame num_rows num_slots) :=
  ConFilter.Inhabitant_frame H_num_rows H_num_slots.

Lemma H_frame_tick_tocks0: 0 < frame_tick_tocks. Proof. pose proof H_frame_tick_tocks. lia. Qed.

(* timer_sim relates an abstract timer with a concrete timer. The state of the abstract timer is
  described by window_hi and last_timestamp. The state of the concrete timer is described by ct.
  In the abstract timer, the range of the last pane is
  [window_hi - frame_time, window_hi). last_timestamp should be inside this range, although
  we do not need to reinforce it in this relation. The value of concrete timer is counted from
  its start time. We don't know when the concrete timer started, but we can compare it with the
  abstract timer as follows. In order to make the range [window_hi - frame_time, window_hi) maintainable
  in the concrete timer, we need to have (tick_time * 2 | window_hi), which is the same as
  (tick_time * 2 | window_hi - frame_time). Considering the position of last_timestamp in
  [window_hi - frame_time, window_hi), the current tick is the
  ((last_timestamp - (window_hi - frame_time)) / tick_time)-th tick in the range. (snd ct) is
  corresponding to (Z.odd ((last_timestamp - (window_hi - frame_time)) / tick_time)), i.e.
  (Z.odd (last_timestamp / tick_time)). The range of the last pane is decribed as
  [(fst ct) / frame_tick_tocks * frame_tick_tocks, ((fst ct) / frame_tick_tocks + 1) * frame_tick_tocks).
  So the correspondence between last_timestamp and (fst ct) is
  ((last_timestamp - (window_hi - frame_time)) / (tick_time * 2) = (fst ct) mod frame_tick_tocks).
  So we have the following definition of timer_sim:

Definition timer_sim (window_hi last_timestamp : Z) (ct : Z * bool) : Prop :=
  (tick_time * 2 | window_hi) /\
  Z.odd (last_timestamp / tick_time) = snd ct /\
  (last_timestamp - (window_hi - frame_time)) / (tick_time * 2) = (fst ct) mod frame_tick_tocks.

  The following definition is equivalent and easier to handle:
*)
Definition timer_sim (window_hi last_timestamp : Z) (ct : Z * bool) : Prop :=
  (tick_time * 2 | window_hi) /\
  let n := (fst ct) mod frame_tick_tocks * 2 + Z.b2z (snd ct) in
  window_hi - frame_time + n * tick_time <= last_timestamp < window_hi - frame_time + (n + 1) * tick_time.

Definition get_timer_bone (ct : Z * bool) : Z * bool :=
  (fst ct mod frame_tick_tocks, snd ct).

(* This is currently not used. *)
Definition update_timer_bone (tb : Z * bool) (tick : bool) : Z * bool :=
  if tick then
    (fst tb, true)
  else
    if (snd tb) then
      (if fst tb + 1 =? frame_tick_tocks then 0 else fst tb + 1, false)
    else
      (fst tb, false).

(* This is currently not used. *)
Lemma update_timer_bone_sound : forall ct tick,
  get_timer_bone (update_timer (num_frames := num_frames) frame_tick_tocks ct tick)
    = update_timer_bone (get_timer_bone ct) tick.
Proof.
  intros. destruct ct as [t b]. unfold get_timer_bone, update_timer_bone, update_timer. simpl. destruct tick; simpl.
  - destruct (t =? frame_tick_tocks * num_frames) eqn:?H; simpl; auto.
    f_equal. rewrite Zdiv.Zmod_0_l. rewrite Z.eqb_eq in H. subst. rewrite Z.mul_comm, Zdiv.Z_mod_mult. easy.
  - destruct b; simpl; auto. f_equal. pose proof H_frame_tick_tocks0. pose proof (Z.div_mod t frame_tick_tocks ltac:(lia)).
    destruct (t mod frame_tick_tocks + 1 =? frame_tick_tocks) eqn:?H.
    + rewrite Z.eqb_eq in H1. assert (t + 1 = (t / frame_tick_tocks + 1) * frame_tick_tocks) by lia. rewrite H2. apply Zdiv.Z_mod_mult.
    + rewrite Z.eqb_neq in H1. pose proof (Zdiv.Z_mod_lt t frame_tick_tocks ltac:(lia)).
      remember (t mod frame_tick_tocks). assert (0 <= z < frame_tick_tocks - 1) by lia. clear H2.
      assert (t + 1 = z + 1 + (t / frame_tick_tocks) * frame_tick_tocks) by lia.
      rewrite H2. rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.

Lemma timer_sim_range : forall window_hi last_timestamp ct,
  timer_sim window_hi last_timestamp ct ->
  window_hi - frame_time <= last_timestamp < window_hi.
Proof.
  intros.
  unfold timer_sim in H. destruct H. pose proof (H_frame_tick_tocks).
  pose proof (H_frame_tick_tocks0).
  assert (0 <= (fst ct mod frame_tick_tocks * 2 + Z.b2z (snd ct)) < frame_tick_tocks * 2). {
    pose proof (Zdiv.Z_mod_lt (fst ct) frame_tick_tocks ltac:(lia)).
    assert (0 <= Z.b2z (snd ct) < 2). { destruct (snd ct); simpl; lia. }
    lia. }
  assert (0 <= (fst ct mod frame_tick_tocks * 2 + Z.b2z (snd ct)) * tick_time). {
    apply Z.mul_nonneg_nonneg; lia. }
  assert ((fst ct mod frame_tick_tocks * 2 + Z.b2z (snd ct) + 1) * tick_time <= frame_time). {
    replace frame_time with (frame_tick_tocks * 2 * tick_time) by lia.
    apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma timer_sim_unique : forall window_hi last_timestamp ct ct',
  timer_sim window_hi last_timestamp ct ->
  timer_sim window_hi last_timestamp ct' ->
  get_timer_bone ct = get_timer_bone ct'.
Proof.
  intros.
  destruct H. destruct H0.
  set (n := fst ct mod frame_tick_tocks * 2 + Z.b2z (snd ct)) in H1.
  set (n' := fst ct' mod frame_tick_tocks * 2 + Z.b2z (snd ct')) in H2.
  simpl in H1, H2. destruct ct as [t b]. destruct ct' as [t' b']. unfold get_timer_bone. simpl in *.
  destruct (n =? n') eqn:?H.
  - rewrite Z.eqb_eq in H3. subst n'. subst n.
    destruct b, b'; try (f_equal; lia); simpl in H3; exfalso; lia.
  - destruct (n <? n') eqn:?H.
    + assert (n * tick_time + tick_time <= n' * tick_time). {
        replace (n * tick_time + tick_time) with ((n + 1) * tick_time) by lia.
        apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
    + assert (n > n') by lia.
      assert (n' * tick_time + tick_time <= n * tick_time). {
        replace (n' * tick_time + tick_time) with ((n' + 1) * tick_time) by lia.
        apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
Qed.

Inductive filter_sim : filter -> ConFilter.filter num_frames num_rows num_slots -> Prop :=
  | filter_sim_intro : forall window_hi last_timestamp num_clears normal_frames cf ic,
      (* Normal frames are good. *)
      Forall2 frame_sim (map Normal normal_frames)
          (sublist (ic + 1) (ic + num_frames) (` (fil_frames cf) ++ ` (fil_frames cf))) ->
      (* The clear frame is good. *)
      (* I'm not sure if this form is easy to handle. I do it in this way to avoid
        (1) talking about the cyclic behavior;
        (2) destructing the frame into rows.
      *)
      num_clears >= 0 ->
      (exists cl, frame_sim (Clear cl) (Znth ic (` (fil_frames cf))) /\
          (Forall (fun b => (is_true b))
            (sublist
              (fil_clear_index cf + num_slots - (Z.min num_slots num_clears))
              (fil_clear_index cf + num_slots)
              (cl ++ cl)))) ->
      (* timer is good *)
      timer_sim window_hi last_timestamp (fil_timer cf) ->
      get_clear_frame num_frames frame_tick_tocks (fil_timer cf) = ic ->
      (* concrete time is well formed *)
      timer_wf num_frames frame_tick_tocks (fil_timer cf) ->
      (* clear index is well formed *)
      clear_index_wf num_slots (fil_clear_index cf) ->
      filter_sim (mk_filter window_hi last_timestamp num_clears normal_frames) cf.

Definition filter_init (time : Z) : filter :=
  mk_filter (round_time time + frame_time) time num_slots (Zrepeat [] (num_frames - 1)).

Definition Is_filter_init (f : filter) : Prop :=
  exists time, f = filter_init time.

Definition filter_refresh (f : filter) (timestamp : Z) : option filter :=
  let '(mk_filter window_hi last_timestamp num_clears normal_frames) := f in
  if (last_timestamp <=? timestamp) && (timestamp <=? last_timestamp + tick_time) then
    if (timestamp >=? window_hi) then
      if (num_clears >=? num_slots) then
        let frames := sublist 1 (num_frames - 1) normal_frames ++ [[]] in
        Some (mk_filter (window_hi + frame_time) last_timestamp 0 frames)
      else
        None
    else
      Some f
  else
    None.

Definition filter_insert (f : filter) '(timestamp, h) : option filter :=
  match filter_refresh f timestamp with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      let frames := upd_Znth (num_frames - 2) normal_frames (Znth (num_frames - 2) normal_frames ++ [h]) in
      Some (mk_filter window_hi timestamp (num_clears + 1) frames)
  | _ => None
  end.

Definition filter_query (f : filter) '((timestamp, h) : Z * header_type) : option (filter * bool) :=
  match filter_refresh f timestamp with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      let res := forallb (fun hs => existsb (fun hash => fold_orb (map (Z.eqb (hash h) ∘ hash) hs)) hashes) normal_frames in
      Some (mk_filter window_hi timestamp (num_clears + 1) normal_frames, res)
  | _ => None
  end.

Definition filter_clear (f : filter) '((timestamp, h) : Z * header_type) : option filter :=
  match filter_refresh f timestamp with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      Some (mk_filter window_hi timestamp (num_clears + 1) normal_frames)
  | _ => None
  end.

Lemma H_num_frames0 : 0 < num_frames. Proof. lia. Qed.

Ltac destruct_match H :=
  match goal with
  | H: context [match ?A with | _ => _ end] |- _ => destruct A eqn:?H
  end.

(* This is basically the same as filter_sim but we replace ci with (ci + 1). *)
(* Inductive filter_sim_1 : filter -> ConFilter.filter num_frames num_rows num_slots -> Prop :=
  | filter_sim_1_intro : forall window_hi last_timestamp num_clears normal_frames cf ic,
      (* Normal frames are good. *)
      Forall2 frame_sim (map Normal normal_frames)
          (sublist (ic + 1 + 1) (ic + 1 + num_frames) (` (fil_frames cf) ++ ` (fil_frames cf))) ->
      (* The clear frame is good. *)
      (* I'm not sure if this form is easy to handle. I do it in this way to avoid
        (1) talking about the cyclic behavior;
        (2) destructing the frame into rows.
      *)
      num_clears >= 0 ->
      (exists cl, frame_sim (Clear cl) (Znth (ic + 1) (` (fil_frames cf))) /\
          (Forall (fun b => (is_true b))
            (sublist
              (fil_clear_index cf + num_slots - (Z.min num_slots num_clears))
              (fil_clear_index cf + num_slots)
              (cl ++ cl)))) ->
      (* timer is good *)
      timer_sim window_hi last_timestamp (fil_timer cf) ->
      get_clear_frame num_frames frame_tick_tocks (fil_timer cf) = ic ->
      (* concrete time is well formed *)
      timer_wf num_frames frame_tick_tocks (fil_timer cf) ->
      (* clear index is well formed *)
      clear_index_wf num_slots (fil_clear_index cf) ->
      filter_sim_1 (mk_filter window_hi last_timestamp num_clears normal_frames) cf. *)

(* Lemma filter_refresh_sound : forall f cf t f',
    filter_sim f cf ->
    filter_refresh f t = Some f' ->
    (if (t >=? window_hi f) then filter_sim_1 f' cf else filter_sim f' cf).
Proof.
  intros.
  destruct f as [win_hi last_stamp num_clrs normal_frs].
  unfold filter_refresh in H0.
  destruct ((last_stamp <=? t) && (t <=? last_stamp + tick_time)) eqn:?H. 2 : inv H0.
  simpl.
  destruct (t >=? win_hi) eqn:?H. 2 : inv H0; auto.
  destruct (num_clrs >=? num_slots) eqn:?H. 2 : inv H0.
  inv H0.
  inv H; econstructor.
  2 : lia.
  4, 5, 6 : eauto.
  { set (ci := get_clear_frame num_frames frame_tick_tocks (fil_timer cf)).
    destruct cf as [[] cfil_clear_idx cfil_timr].
    assert (0 <= ci < num_frames). {
      admit.
    }
    assert (Zlength normal_frs = num_frames - 1). {
      admit.
    }
    apply Forall2_forall_Znth.
    split.
    { simpl. rewrite Zlength_map. (* Why we need it? *)
      list_solve.
    }
    rewrite Zlength_map.
    simpl in *.
    intros.
    list_simplify.
    { rewrite Forall2_forall_Znth in H7.
      destruct H7 as [?H H7].
      specialize (H7 (i + 1) ltac:(list_solve)).
      fapply H7.
      f_equal. list_solve.
      fold ci.
      list_simplify.
      apply Inhabitant_list.
    }
    { rewrite Forall2_forall_Znth in H7.
      destruct H7 as [?H H7].
      specialize (H7 (i + 1) ltac:(list_solve)).
      fapply H7.
      f_equal. list_solve.
      fold ci.
      list_simplify.
      apply Inhabitant_list.
    }
    { destruct H9 as [cl H9].
      assert (i = num_frames - 2) by lia. subst i.
      fold ci in H9.
      replace (Z.min num_slots num_clrs) with num_slots in H9 by lia.
      assert (Zlength cl = num_slots) by admit.
      destruct H9.
      assert (cl = Zrepeat true num_slots). {
        clear -H14 H20 H21.
        red in H14.
        list_solve.
      }
      replace (num_frames - 2 + (ci + 1 + 1) - Zlength x) with ci by lia.
      subst cl; clear -H9.
      admit. (* This is a lemma just about frame_sim. *)
    }
  }
  { exists (Zrepeat false num_slots).
    split.
    { admit. (* This is a lemma just about frame_sim. *)
    }
    { clear -H14.
      red in H14.
      list_solve.
    }
  }
  { admit. (* all about timer arith *) }
Admitted. *)

Definition filter_refresh' (f : filter) (timestamp : Z) : option filter :=
  match filter_refresh f timestamp with
  | Some (mk_filter window_hi last_timestamp num_clears normal_frames) =>
      Some (mk_filter window_hi timestamp num_clears normal_frames)
  | _ => None
  end.

Lemma filter_refresh'_sound : forall f cf t f',
    filter_sim f cf ->
    filter_refresh' f t = Some f' ->
    filter_sim f' {|
      fil_frames := fil_frames cf;
      fil_clear_index := fil_clear_index cf;
      fil_timer := update_timer (num_frames := num_frames) frame_tick_tocks (fil_timer cf) (Z.odd (t / tick_time))
    |}.
Proof.
  intros.
  destruct f as [win_hi last_stamp num_clrs normal_frs].
  unfold filter_refresh', filter_refresh in H0.
  destruct ((last_stamp <=? t) && (t <=? last_stamp + tick_time)) eqn:?H. 2 : inv H0.
  simpl. inv H.
  remember (update_timer frame_tick_tocks (fil_timer cf) (Z.odd (t / tick_time)))
    as new_timer.
  pose proof H_frame_tick_tocks0 as ?F.
  assert (timer_wf num_frames frame_tick_tocks new_timer). {
    subst new_timer. apply update_timer_wf; auto; lia. }
  destruct (t >=? win_hi) eqn:?H.
  - destruct (num_clrs >=? num_slots) eqn:?H; inversion H0; subst f'; clear H0.
    pose proof (timer_sim_range _ _ _ ltac:(eauto)).
    assert (win_hi - tick_time <= last_stamp /\ t < win_hi + tick_time) by lia.
    assert (get_timer_bone (fil_timer cf) = (frame_tick_tocks - 1, true)). {
      assert (timer_sim win_hi last_stamp (frame_tick_tocks - 1, true)). {
        destruct H9. split; only 1 : auto.
        simpl fst. rewrite Z.mod_small by lia.
        simpl. pose proof H_frame_tick_tocks. lia. }
      eapply timer_sim_unique in H5; only 2 : apply H9.
      unfold get_timer_bone at 2 in H5.
      rewrite (Z.mod_small (frame_tick_tocks - 1)) in H5 by lia.
      apply H5.
    }
    (* Put this outside this bullet? *)
    (* pose proof (update_timer_bone_sound (fil_timer cf) (Z.odd (t / tick_time))). *)
    replace (Z.odd (t / tick_time)) with false in *.
    2: { destruct H4 as [_ ?]. destruct H9 as [? _].
         assert (exists r, 0 <= r < tick_time /\ t = win_hi + r) by (exists (t - win_hi); lia).
         destruct H10 as [r [? ?]]. destruct H9 as [x ?].
         replace t with (r + 2 * x * tick_time) by lia.
         rewrite Z.div_add, Z.odd_add_mul_2, Z.div_small by lia. now simpl. }
    (* pose proof Heqnew_timer. *)
    (* unfold update_timer in H10. *)
    (* replace (snd (fil_timer cf)) with true in *. 2 : { *)
    (*   inv H5. (* get_timer_bone *) auto. *)
    (* } *)
    remember (get_clear_frame num_frames frame_tick_tocks (fil_timer cf)) as ci.
    remember (get_clear_frame num_frames frame_tick_tocks new_timer) as new_ci.
    (* assert ((fst (fil_timer cf) + 1) / frame_tick_tocks = fst (fil_timer cf) / frame_tick_tocks + 1). { *)
    (*   inv H5. *)
    (*   admit. *)
    (* } *)
    assert (ci + 1 = num_frames /\ new_ci = 0 \/ ci + 1 < num_frames /\ new_ci = ci + 1). {
      subst ci. subst new_ci. subst new_timer.
      rewrite <- get_clear_frame_update_neq; auto; try lia. split; auto. split.
      - inv H5; auto.
      - inv H5. apply Znumtheory.Zmod_divide_minus in H11; auto.
        replace (fst (fil_timer cf) + 1) with (fst (fil_timer cf) - (frame_tick_tocks - 1) + frame_tick_tocks) by lia.
        apply Z.divide_add_r; auto. reflexivity. }
    (* econstructor; simpl; eauto; try lia.
    + remember (get_clear_frame num_frames frame_tick_tocks new_timer) as new_ci.
      destruct cf as [cfil_frms cfil_clear_idx cfil_timr]. simpl in *.
      assert (0 <= new_ci < num_frames). {
        subst new_ci. apply get_clear_frame_range; auto. lia. apply H_frame_tick_tocks0. }
      remember (get_clear_frame num_frames frame_tick_tocks cfil_timr) as ci.
      assert (0 <= ci < num_frames). {
        subst ci. apply get_clear_frame_range; auto. lia. apply H_frame_tick_tocks0. }
      apply  Forall2_forall_Znth. destruct cfil_frms as [cfil_frms ?H]. simpl in *.
      rewrite Forall2_forall_Znth in H6. destruct H6. rewrite Zlength_map in H6.
      assert (Zlength normal_frs = num_frames - 1) by list_solve. clear H6.
      rewrite Zlength_map in *. split. 1: list_solve. intros. list_simplify.
      * specialize (H10 (i + 1) ltac:(list_solve)).
        assert (ci + 1 = num_frames /\ new_ci = 0 \/ ci + 1 < num_frames /\ new_ci = ci +1). {
          admit. }
        admit.
      * admit.
      * admit.
      * admit.
    + admit.
    + admit.
  - inv H0. *)
Admitted.

Lemma filter_insert_sound: forall f cf th f',
    filter_sim f cf ->
    filter_insert f th = Some f' ->
    filter_sim f' (ConFilter.filter_insert H_num_frames0 H_num_rows H_num_slots frame_tick_tocks H_frame_tick_tocks0
                     cf (Z.odd (fst th / tick_time)) (map_hashes (snd th))).
Proof.
  intros.
  unfold filter_insert in H0. destruct th as [timestamp h].
  destruct_match H0. 2: inv H0.
  destruct f0 as [win_hi last_stamp num_clrs normal_frs].
  epose proof (filter_refresh'_sound _ _ timestamp _ ltac:(eauto)).
  unfold filter_refresh' in H2. rewrite H1 in H2. specialize (H2 ltac:(eauto)).
  clear f H H1.
  destruct cf as [cfil_frs cfil_clear_idx cfil_timr].
  inv H0. inv H2.
  simpl in * |-.
  unfold ConFilter.filter_insert.
  destruct cfil_frs as [cframes ?H]. simpl.
  set (new_clear_index := update_clear_index cfil_clear_idx) in *.
  set (new_timer := update_timer (num_frames := num_frames) frame_tick_tocks cfil_timr (Z.odd (timestamp / tick_time))) in *.
  set (cf := get_clear_frame num_frames frame_tick_tocks new_timer) in *.
  set (if' := get_insert_frame num_frames cf) in *.
  assert (0 <= cf < num_frames). {
    eapply get_clear_frame_range; eauto. lia. apply H_frame_tick_tocks0.
  }
  assert (0 <= if' < num_frames). {
    eapply get_insert_frame_range; eauto. lia.
  }
  assert (if' <> cf). {
    unfold if', get_insert_frame.
    destruct (cf =? 0) eqn:?H; lia.
  }
  econstructor; simpl.
  2 : lia.
  6 : eapply update_clear_index_wf; eauto.
  3, 4, 5 : eauto.
  { fold cf. fold if'.
    set (cleared_cf := (ConFilter.frame_clear (Znth cf cframes)
              (exist (fun i : list Z => Zlength i = num_rows)
                 (Zrepeat cfil_clear_idx num_rows)
                 (ConFilter.filter_insert_obligation_1 H_num_frames0 H_num_rows
                    frame_tick_tocks H_frame_tick_tocks0
                    {|
                      fil_frames :=
                        exist
                          (fun i : list (ConFilter.frame num_rows num_slots) =>
                           Zlength i = num_frames) cframes H;
                      fil_clear_index := cfil_clear_idx;
                      fil_timer := cfil_timr
                    |} cframes H cfil_clear_idx cfil_timr eq_refl)))).
    rewrite Znth_upd_Znth_diff by list_solve.
    rewrite Forall2_forall_Znth.
    rewrite Forall2_forall_Znth in H4; destruct H4.
    simpl in H3.
    rewrite Zlength_map in H3 by list_solve.
    rewrite Zlength_map.
    split. { list_solve. }
    intros.
    assert (cf = 0 /\ if' = num_frames - 1 \/ cf > 0 /\ if' = cf - 1). {
      unfold if', get_insert_frame.
      destruct (cf =? 0) eqn:?H; lia.
    }
    rewrite Zlength_map in H4.
    pose proof frame_insert_sound as frame_insert_sound.
    list_simplify.
    { assert (cf = 0) by lia.
      eapply frame_insert_sound with (f := Normal (Znth (num_frames - 2) normal_frs)).
        2 : reflexivity.
      fapply (H4 (num_frames - 2) ltac:(list_solve)). f_equal.
      { list_solve. }
      { simpl. list_solve. }
    }
    { fapply (H4 i ltac:(list_solve)). f_equal.
      { list_solve. }
      { simpl. list_solve. }
    }
    { eapply frame_insert_sound with (f := Normal (Znth (num_frames - 2) normal_frs)).
        2 : reflexivity.
      fapply (H4 (num_frames - 2) ltac:(list_solve)). f_equal.
      { list_solve. }
      { simpl. list_solve. }
    }
    { fapply (H4 i ltac:(list_solve)). f_equal.
      { list_solve. }
      { simpl. list_solve. }
    }
  }
  { destruct H6 as [cl H6].
    eexists. split.
    { fold cf.
      rewrite Znth_upd_Znth_diff by list_solve.
      rewrite Znth_upd_Znth_same by list_solve.
      eapply frame_clear_sound.
      { apply (proj1 H6). }
      { reflexivity. }
    }
    assert (Zlength cl = num_slots). {
      eapply frame_sim_clear_Zlength; apply (proj1 H6).
    }
    destruct H6 as [_ H6].
    red in H11.
    assert (cfil_clear_idx + 1 = num_slots /\ new_clear_index = 0 \/
        cfil_clear_idx + 1 < num_slots /\ new_clear_index = cfil_clear_idx + 1). {
      unfold new_clear_index, update_clear_index.
      destruct (cfil_clear_idx + 1 =? num_slots) eqn:?H; lia.
    }
    clear -H3 H8 H11 H5 H6.
    destruct (cfil_clear_idx + num_slots - Z.min num_slots num_clrs <? num_slots) eqn:?H;
      list_solve.
  }
Qed.


(*   destruct_match H4. subst. destruct_match H4. 2: inv H4. inv H0.
  apply andb_prop in H7. destruct H7. rewrite Z.leb_le in H, H0.
  destruct_match H4.
  - destruct_match H4; inv H4. simpl. remember (Z.odd (timestamp / tick_time)) as b.
    destruct cf as [cfil_frs cfil_clear_idx cfil_timr]. unfold ConFilter.filter_insert.
    destruct cfil_frs as [cframes ?H]. simpl in *. pose proof (get_clear_frame_range H_num_frames0 _ H_frame_tick_tocks0 _ H5).
    rewrite Forall2_forall_Znth in H1. destruct H1. rewrite Zlength_map, Zlength_sublist in H1 by list_solve.
    replace (get_clear_frame num_frames frame_tick_tocks cfil_timr + num_frames - (get_clear_frame num_frames frame_tick_tocks cfil_timr + 1)) with
      (num_frames - 1) in H1 by lia. rewrite Z.geb_le in *.
    apply filter_sim_intro with (ic := get_clear_frame num_frames frame_tick_tocks (@update_timer num_frames frame_tick_tocks cfil_timr b)); auto.
    + simpl. pose proof (update_timer_wf H_num_frames0 _ H_frame_tick_tocks0 _ b H5).
      remember (update_timer frame_tick_tocks cfil_timr b) as new_timer.
      pose proof (get_clear_frame_range H_num_frames0 _ H_frame_tick_tocks0 _ H11).
      rewrite Forall2_forall_Znth. split.
      * rewrite Zlength_map, Zlength_sublist; list_solve.
      * intros. rewrite Zlength_map, Zlength_upd_Znth, Zlength_app, (calc_Zlength_cons _ _ 0), Zlength_sublist in H13 by list_solve.
        replace (num_frames - 1 - 1 + (1 + 0)) with (num_frames - 1) in H13 by lia.
        rewrite Zlength_map, H1 in H10. rewrite Znth_sublist by list_solve.
        remember (get_clear_frame num_frames frame_tick_tocks new_timer) as new_clear_index.
        rewrite Znth_map. destruct (ZArith_dec.Z_lt_ge_dec (i + (new_clear_index + 1)) num_frames).
        -- rewrite Znth_app1 with (i := i + (new_clear_index + 1)) by list_solve.
           destruct (Z.eq_dec i (num_frames - 2)).
           ++ subst i. rewrite Znth_upd_Znth_same by list_solve.
              destruct (Z.eq_dec new_clear_index 0). 2: exfalso; lia. rewrite e in *. subst new_clear_index.
              replace (num_frames - 2 + (0 + 1)) with (num_frames - 1) in * by lia. unfold get_insert_frame. simpl.
              rewrite Znth_upd_Znth_same by list_solve. rewrite Znth_upd_Znth_diff by lia.
              rewrite Znth_app2 by list_solve. rewrite Zlength_sublist by list_solve.
              replace (num_frames - 2 - (num_frames - 1 - 1)) with 0 by lia. simpl. destruct H2 as [cl [? ?]].
              rewrite Z.min_l in H14 by lia. replace (cfil_clear_idx + num_slots - num_slots) with cfil_clear_idx in H14 by lia.
              pose proof (frame_sim_clear_Zlength _ _ H2). red in H6. rewrite <- Forall_wrap in H14 by lia.
              rewrite Forall_forall_Znth, <- fold_andb_true in H14.
Abort. *)

End Frame.
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
