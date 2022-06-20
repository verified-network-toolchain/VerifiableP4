Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Import ProD3.examples.sbf.Utils.
Import ListNotations.
Open Scope Z_scope.

Definition listn (T : Type) size := { i : list T | Zlength i = size }.

Program Definition map_listn {A B : Type} {size}
    (f : A -> B) (l : listn A size) : listn B size :=
  map f l.
Next Obligation.
  destruct l as [l ?H]. list_solve.
Qed.

Program Definition Inhabitant_listn {A : Type} {dA : Inhabitant A} size (H : 0 <= size) : Inhabitant (listn A size) :=
  Zrepeat (default (Inhabitant := dA)) size.
Next Obligation.
  list_solve.
Qed.

Section ConFilter.

Context {num_frames num_rows num_slots : Z}.
Hypothesis H_num_frames : 0 < num_frames.
Hypothesis H_num_rows : 0 < num_rows.
Hypothesis H_num_slots : 0 < num_slots.

Definition row := listn bool num_slots.

#[local] Program Instance Inhabitant_row : Inhabitant row :=
  Inhabitant_listn _ _.
Next Obligation.
  lia.
Qed.

Definition frame := listn row num_rows.

#[local] Program Instance Inhabitant_frame : Inhabitant frame :=
  Inhabitant_listn _ _.
Next Obligation.
  lia.
Qed.

Program Definition row_insert (r : row) (i : Z) : row :=
  upd_Znth i r true.
Next Obligation.
  destruct r. list_solve.
Qed.

Lemma row_insert_comm : forall (r : row) x y,
  row_insert (row_insert r x) y = row_insert (row_insert r y) x.
Proof.
  intros. destruct r as [r ?H]. unfold row_insert. simpl.
  apply subset_eq_compat. list_solve.
Qed.

Program Definition frame_insert (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_insert f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_clear (r : row) (i : Z) : row:=
  upd_Znth i r false.
Next Obligation.
  destruct r. list_solve.
Qed.

Program Definition frame_clear (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_clear f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_query (r : row) (i : Z) : bool :=
  Znth i r.

Lemma row_query_insert_true : forall (r: row) z,
  0 <= z < num_slots -> row_query (row_insert r z) z = true.
Proof.
  intros. destruct r as [r ?H]. unfold row_query, row_insert. simpl. list_solve.
Qed.

Program Definition frame_query (f : frame) (is : list Z) : bool :=
  fold_andb (map2 row_query f is).

Record filter := mk_filter {
  fil_frames : listn frame num_frames;
  fil_clear_index : Z;
  fil_timer : Z * bool;
  }.

Definition clear_index_wf (i: Z) := 0 <= i < num_slots.

Context (frame_tick_tocks : Z).

Hypothesis H_frame_tick_tocks: 0 < frame_tick_tocks.

Let cycle_tick_tocks := frame_tick_tocks * num_frames.

Definition timer_wf (timer: Z * bool) := if (snd timer)
                                      then 0 <= fst timer < cycle_tick_tocks
                                      else 0 <= fst timer <= cycle_tick_tocks.

Definition update_clear_index (i : Z) :=
  let i := i+1 in
  if (i =? num_slots) then 0 else i.

Lemma update_clear_index_wf: forall i, clear_index_wf i -> clear_index_wf (update_clear_index i).
Proof.
  intros. red in H |- *. unfold update_clear_index.
  destruct (i + 1 =? num_slots) eqn: ?H; lia.
Qed.

Definition update_timer (t : Z * bool) (tick : bool) : Z * bool :=
  if tick then
    if (fst t =? cycle_tick_tocks) then
      (0, true)
    else
      (fst t, true)
  else
    if snd t then
      (fst t + 1, false)
    else
      t.

Lemma update_timer_wf: forall t tick, timer_wf t -> timer_wf (update_timer t tick).
Proof.
  intros. red in H |- *. unfold update_timer. destruct t as [timer b]. simpl in *.
  destruct tick, b; simpl in *; try lia; destruct (timer =? cycle_tick_tocks) eqn: ?H;
    simpl; lia.
Qed.

Definition get_clear_frame (t : Z * bool) : Z :=
  let t := fst t in
  let t := if (t =? cycle_tick_tocks) then 0 else t in
  t / frame_tick_tocks.

Lemma get_clear_frame_nonneg: forall timer, 0 <= fst timer -> 0 <= get_clear_frame timer.
Proof.
  intros. destruct timer. unfold get_clear_frame. simpl in *.
  destruct (z =? cycle_tick_tocks); apply Z.div_pos; lia.
Qed.

Lemma get_clear_frame_range: forall timer, timer_wf timer ->
                                      0 <= get_clear_frame timer < num_frames.
Proof.
  intros. red in H. unfold get_clear_frame. destruct timer as [t b]. simpl in *.
  destruct b, (t =? cycle_tick_tocks) eqn: ?H; try (rewrite Z.div_0_l; lia);
    subst cycle_tick_tocks; split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma get_clear_frame_update:
  forall timer b, timer_wf timer ->
             get_clear_frame timer = get_clear_frame (update_timer timer b).
Proof.
  intros. unfold get_clear_frame, update_timer. destruct timer as [timer tb].
  red in H. simpl in *. destruct tb, b.
  - destruct (timer =? cycle_tick_tocks) eqn:?H. simpl fst.
    + destruct (0 =? cycle_tick_tocks); auto.
    + simpl. rewrite H0. auto.
  - admit.
  -
Abort.

Definition get_insert_frame (cf : Z) : Z :=
  if (cf =? 0) then num_frames - 1 else cf - 1.

Lemma get_insert_frame_range: forall cf, 0 <= cf < num_frames -> 0 <= get_insert_frame cf < num_frames.
Proof. intros. unfold get_insert_frame. destruct (cf =? 0) eqn: ?H; lia. Qed.

Program Definition filter_insert (f : filter) (tick : bool) (is : listn Z num_rows) : filter :=
  let '(mk_filter (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let if' := get_insert_frame cf in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  let frames := upd_Znth if' frames (frame_insert (Znth if' frames) is) in
  mk_filter frames new_clear_index timer.
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

Program Definition filter_query (f : filter) (tick : bool) (is : listn Z num_rows) : filter * bool :=
  let '(mk_filter (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  (mk_filter frames new_clear_index timer,
    fold_orb (upd_Znth cf (map (fun f => frame_query f is) frames) false)).
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

Program Definition filter_clear (f : filter) (tick : bool) (is : listn Z num_rows) : filter :=
  let '(mk_filter (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  mk_filter frames new_clear_index timer.
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

End ConFilter.

Arguments row : clear implicits.
Arguments frame : clear implicits.
Arguments filter : clear implicits.
Arguments timer_wf : clear implicits.
Arguments clear_index_wf : clear implicits.
Arguments get_clear_frame : clear implicits.
Arguments get_insert_frame : clear implicits.
