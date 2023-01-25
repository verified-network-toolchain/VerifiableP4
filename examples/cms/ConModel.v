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

Section ConCountMinSketch.

Context {num_frames num_rows num_slots : Z}.
Hypothesis H_num_frames : 1 < num_frames.
Hypothesis H_num_rows : 0 < num_rows.
Hypothesis H_num_slots : 0 < num_slots.

Definition row := listn Z num_slots.

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
  upd_Znth i r (Znth i r + 1).
Next Obligation.
  destruct r. list_solve.
Qed.

Lemma row_insert_comm : forall (r : row) x y,
  row_insert (row_insert r x) y = row_insert (row_insert r y) x.
Proof.
  intros.
  unfold row_insert.
  destruct r as [r ?H]. apply subset_eq_compat.
  simpl.
  list_solve.
Qed.

Program Definition frame_insert (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_insert f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_clear (r : row) (i : Z) : row:=
  upd_Znth i r 0.
Next Obligation.
  destruct r. list_solve.
Qed.

Program Definition frame_clear (f : frame) (is : listn Z num_rows) : frame :=
  map2 row_clear f is.
Next Obligation.
  destruct is, f; simpl.
  list_solve.
Qed.

Program Definition row_query (r : row) (i : Z) : Z :=
  Znth i r.

Lemma row_query_insert_inc : forall (r: row) z,
  0 <= z < num_slots -> row_query (row_insert r z) z > row_query r z.
Proof.
  intros. destruct r as [r ?H]. unfold row_query, row_insert. simpl. list_solve.
Qed.

Definition list_min (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: l' => fold_left Z.min l' x
  end.

Program Definition frame_query (f : frame) (is : list Z) : Z :=
  list_min (map2 row_query f is).

Record cms := mk_cms {
  cms_frames : listn frame num_frames;
  cms_clear_index : Z;
  cms_timer : Z * bool;
}.

Definition clear_index_wf (i: Z) := 0 <= i < num_slots.

Context (frame_tick_tocks : Z).

Hypothesis H_frame_tick_tocks: 0 < frame_tick_tocks.

Let cycle_tick_tocks := frame_tick_tocks * num_frames.

Definition timer_wf (timer: Z * bool) :=
  0 <= fst timer < cycle_tick_tocks.

Definition update_clear_index (i : Z) :=
  let i := i+1 in
  if (i =? num_slots) then 0 else i.

Lemma update_clear_index_wf: forall i, clear_index_wf i -> clear_index_wf (update_clear_index i).
Proof.
  intros. red in H |- *. unfold update_clear_index.
  clear -H.
  destruct (i + 1 =? num_slots) eqn: ?H; lia.
Qed.

Definition update_timer (t : Z * bool) (tick : bool) : Z * bool :=
  if tick then
    (fst t, true)
  else
    if snd t then
      if (fst t =? cycle_tick_tocks - 1) then
        (0, false)
      else
        (fst t + 1, false)
    else
      t.

Lemma update_timer_wf: forall t tick, timer_wf t -> timer_wf (update_timer t tick).
Proof.
  intros. red in H |- *. unfold update_timer. destruct t as [timer b]. simpl in *.
  destruct tick, b; simpl in *; try lia.
   destruct (timer =? cycle_tick_tocks - 1) eqn:?H;
    simpl; lia.
Qed.

Definition get_clear_frame (t : Z * bool) : Z :=
  fst t / frame_tick_tocks.

Lemma get_clear_frame_nonneg : forall timer, 0 <= fst timer -> 0 <= get_clear_frame timer.
Proof.
  intros. destruct timer. unfold get_clear_frame. simpl in *.
  destruct (z =? cycle_tick_tocks); apply Z.div_pos; lia.
Qed.

Lemma get_clear_frame_range : forall timer,
  timer_wf timer ->
  0 <= get_clear_frame timer < num_frames.
Proof.
  intros. red in H. unfold get_clear_frame. destruct timer as [t b].
    subst cycle_tick_tocks; split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma get_clear_frame_update_neq : forall timer b,
    timer_wf timer -> 1 < num_frames ->
    (b = false /\ snd timer = true /\ (frame_tick_tocks | fst timer + 1)) <->
      (get_clear_frame timer + 1 = num_frames /\ get_clear_frame (update_timer timer b) = 0 \/
         get_clear_frame timer + 1 < num_frames /\ get_clear_frame (update_timer timer b) = get_clear_frame timer + 1).
Proof.
  intros. unfold get_clear_frame, update_timer. destruct timer as [timer tb].
  red in H. simpl in *. split; intros.
  - destruct H1 as [? [? H1]].
    subst.
    destruct (timer =? cycle_tick_tocks - 1) eqn:?H; [left | right].
    + split.
      * rewrite Z.eqb_eq in H2.
        assert (timer = (num_frames - 1) * frame_tick_tocks + (frame_tick_tocks - 1)) by lia.
        rewrite H3. rewrite Z.div_add_l by lia. rewrite Zdiv.Zdiv_small; lia.
      * simpl. reflexivity.
    + destruct H1 as [frs ?H]. assert (frs < num_frames) by nia. rewrite H1.
      simpl. rewrite Z.div_mul by lia.
      assert (timer = (frs - 1) * frame_tick_tocks + (frame_tick_tocks - 1)) by lia.
      rewrite H4. rewrite Z.div_add_l by lia. rewrite Zdiv.Zdiv_small; lia.
  - destruct tb eqn:?B, b eqn:?B.
    + assert (timer =? cycle_tick_tocks = false) by lia. simpl in *.
      destruct H1; exfalso; lia.
    + do 2 (split; auto). assert (timer =? cycle_tick_tocks = false) by lia. simpl in *.
      destruct (timer =? cycle_tick_tocks - 1) eqn:?H; simpl in *.
      * rewrite Z.eqb_eq in H3. rewrite H3. subst cycle_tick_tocks. exists num_frames. lia.
      * destruct H1 as [[? ?] | [? ?]]; simpl in *.
        -- exfalso. rewrite Z.div_small_iff in H4 by lia. destruct H4; try lia.
           rewrite Z.div_small in H1; lia.
        -- pose proof (Z.div_mod (timer + 1) frame_tick_tocks ltac:(lia)).
           destruct (Znumtheory.Zdivide_dec frame_tick_tocks (timer + 1)); auto.
           exfalso. rewrite <- Z.mod_divide in n by lia.
           pose proof (Z.mod_pos_bound (timer + 1) frame_tick_tocks ltac:(lia)).
           assert (exists r, timer = ((timer + 1) / frame_tick_tocks) * frame_tick_tocks + r /\ 0 <= r < frame_tick_tocks). {
             exists ((timer + 1) mod frame_tick_tocks - 1). do 2 (split; try lia). }
           destruct H7 as [r [? ?]]. rewrite H7 in H4 at 2.
           rewrite Z.div_add_l in H4 by lia. rewrite (Z.div_small _ _ H8) in H4. lia.
    + exfalso.
      simpl fst in *. destruct H1; lia.
    + exfalso. simpl fst in *. destruct H1; lia.
Qed.

Lemma get_clear_frame_update_eq : forall timer b,
    timer_wf timer -> 1 < num_frames ->
    (b = true \/ snd timer = false \/ ~ (frame_tick_tocks | fst timer + 1)) <->
      get_clear_frame (update_timer timer b) = get_clear_frame timer.
Proof.
  intros. split; intros.
  - assert (b = true -> get_clear_frame (update_timer timer b) = get_clear_frame timer). {
      intros. unfold get_clear_frame, update_timer. destruct timer as [timer tb].
      red in H. simpl in *. subst. destruct (timer =? cycle_tick_tocks) eqn:?H; simpl fst;
        [destruct (0 =? cycle_tick_tocks) | ]; auto. }
    assert (snd timer = false -> get_clear_frame (update_timer timer b) = get_clear_frame timer). {
      intros. destruct b. 1 : auto. unfold get_clear_frame, update_timer.
      destruct timer as [timer tb]. red in H. simpl in *. subst. simpl; auto. }
    destruct H1; [apply H2; auto |]. destruct H1; [apply H3; auto |].
    destruct b; [apply H2; auto|]. destruct (snd timer) eqn:?H; [| apply H3; auto].
    unfold get_clear_frame, update_timer. destruct timer as [timer tb].
    red in H. simpl in *. subst. simpl.
    destruct (timer =? cycle_tick_tocks - 1) eqn:?H.
    + exfalso. apply H1. exists num_frames. lia.
    + pose proof (Z.div_mod timer frame_tick_tocks ltac:(lia)).
      assert (timer mod frame_tick_tocks <> frame_tick_tocks - 1). {
        intro. apply H1. rewrite H6 in H5. rewrite H5.
        exists (timer / frame_tick_tocks + 1). lia.
      }
      assert (exists r, timer = timer / frame_tick_tocks * frame_tick_tocks + r /\
                     0 <= r < frame_tick_tocks - 1). {
        exists (timer mod frame_tick_tocks). split. 1: lia.
        pose proof (Z.mod_pos_bound timer frame_tick_tocks ltac:(lia)). lia.
      }
      clear H6. destruct H7 as [r []]. rewrite H6. simpl.
      rewrite <- Z.add_assoc. rewrite !Z.div_add_l by lia. f_equal. rewrite !Z.div_small; lia.
  - cut (~ (b = false /\ snd timer = true /\ (frame_tick_tocks | fst timer + 1))).
    + intros. apply Decidable.not_and in H2; [| red; destruct b; intuition].
      destruct H2; [left; destruct b; auto | right].
      apply Decidable.not_and in H2; [| red; destruct (snd timer); intuition].
      destruct H2; [left; destruct (snd timer) | right]; intuition.
    + rewrite get_clear_frame_update_neq; auto. lia.
Qed.

Definition get_insert_frame (cf : Z) : Z :=
  if (cf =? 0) then num_frames - 1 else cf - 1.

Lemma get_insert_frame_range: forall cf, 0 <= cf < num_frames -> 0 <= get_insert_frame cf < num_frames.
Proof. intros. unfold get_insert_frame. destruct (cf =? 0) eqn: ?H; lia. Qed.

Program Definition cms_insert (f : cms) (tick : bool) (is : listn Z num_rows) : cms :=
  let '(mk_cms (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let if' := get_insert_frame cf in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  let frames := upd_Znth if' frames (frame_insert (Znth if' frames) is) in
  mk_cms frames new_clear_index timer.
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

Program Definition cms_query (f : cms) (tick : bool) (is : listn Z num_rows) : cms * Z :=
  let '(mk_cms (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  (mk_cms frames new_clear_index timer,
    Zsum (upd_Znth cf (map (fun f => frame_query f is) frames) 0)).
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

Program Definition cms_clear (f : cms) (tick : bool) : cms :=
  let '(mk_cms (exist _ frames H) clear_index timer) := f in
  let new_clear_index := update_clear_index clear_index in
  let timer := update_timer timer tick in
  let cf := get_clear_frame timer in
  let frames := upd_Znth cf frames (frame_clear (Znth cf frames) (Zrepeat clear_index num_rows)) in
  mk_cms frames new_clear_index timer.
Next Obligation.
  list_solve.
Qed.
Next Obligation.
  list_solve.
Qed.

End ConCountMinSketch.

Arguments row : clear implicits.
Arguments frame : clear implicits.
Arguments cms : clear implicits.
Arguments timer_wf : clear implicits.
Arguments clear_index_wf : clear implicits.
Arguments get_clear_frame : clear implicits.
Arguments get_insert_frame : clear implicits.
