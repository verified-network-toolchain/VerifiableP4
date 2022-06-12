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
  fil_timer : Z * bool
}.

Definition update_clear_index (i : Z) :=
  let i := i+1 in
  if (i =? num_slots) then 0 else i.

Context (frame_time : Z).

Let cycle_time := frame_time * num_frames.

Definition update_timer (t : Z * bool) (tick : bool) : Z * bool :=
  if tick then
    if snd t then
      t
    else
      (fst t + 1, false)
  else
    if (fst t =? cycle_time) then
      (0, true)
    else
      (fst t, true).

Definition get_clear_frame (t : Z * bool) : Z :=
  let t := fst t in
  let t := if (t =? cycle_time) then 0 else t in
  t / frame_time.

Definition get_insert_frame (cf : Z) : Z :=
  if (cf =? 0) then num_frames - 1 else cf - 1.

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
