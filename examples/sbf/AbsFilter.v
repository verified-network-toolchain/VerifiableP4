Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Basics.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.ExtPred.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section AbsFilter.

Context {header_type : Set}.
Context {Inhabitant_header_type : Inhabitant header_type}.

Context (num_rows : Z) (num_cells : Z).
Hypothesis H_num_cells : 0 < num_cells.

Section Row.

Context (hash : header_type -> Z).
Hypothesis H_hash : forall h, 0 <= hash h < num_cells.

Inductive row : Type :=
  | Clear (i : Z)
  | Normal (hs : list header_type).

Inductive row_sim : row -> ConFilter.row -> Prop :=
  | rom_sim_clear : forall i cr,
      Zlength cr = num_cells ->
      (forall j, 0 <= j < i -> Znth j cr = false) ->
      row_sim (Clear i) cr
  | rom_sim_normal : forall hs cr,
      cr = fold_left (fun l i => upd_Znth i l true) (map hash hs) (Zrepeat false num_cells) ->
      row_sim (Normal hs) cr.

Definition row_insert (r : row) (h : header_type) : option row :=
  match r with
  | Clear _ => None
  | Normal hs => Some (Normal (hs ++ [h]))
  end.

Lemma row_insert_sound : forall r cr h r',
  row_sim r cr ->
  row_insert r h = Some r' ->
  row_sim r' (ConFilter.row_insert cr (hash h)).
Proof.
  intros.
  destruct r as [? | hs]; inv H0.
  inv H. constructor.
  rewrite map_app.
  rewrite fold_left_app.
  reflexivity.
Qed.

Definition row_clear (r : row) (i : Z) : option row :=
  match r with
  | Clear j =>
      if i =? j then
        if i+1 >=? num_cells then
          Some (Normal [])
        else
          Some (Clear (i+1))
      else
        None
  | Normal _ =>
      if i =? 0 then Some (Clear 1) else None
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
  destruct r as [j | ?].
  - unfold row_clear in *.
    destruct (i =? j) eqn:H_i_j.
    + destruct (i+1 >=? num_cells) eqn:H_i1_num_cells.
      * inv H0. inv H.
        replace (ConFilter.row_clear cr i) with (Zrepeat false num_cells). 2 : {
          unfold ConFilter.row_clear; list_simplify. symmetry; apply H2; list_solve.
        }
        constructor. auto.
      * inv H0. inv H.
        unfold ConFilter.row_clear; constructor.
        { list_solve. }
        { list_simplify. apply H2; list_solve. }
    + inv H0.
  - unfold row_clear in *.
    destruct (i =? 0) eqn:H_i_0.
    + inv H0. inv H.
      assert (Zlength (fold_left (fun (l : list bool) (i0 : Z) => upd_Znth i0 l true)
            (map hash hs) (Zrepeat false num_cells)) = num_cells). {
        apply fold_left_pres.
        { list_solve. }
        { list_solve. }
      }
      unfold ConFilter.row_clear; constructor.
      { list_solve. }
      { list_solve. }
    + inv H0.
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
  rewrite <- !fold_left_rev_right.
  rewrite <- !map_rev.
  generalize (rev hs) as hs0. clear hs; intro hs.
  induction hs as [ | h' hs].
  - unfold ConFilter.row_query. simpl. specialize (H_hash h). list_solve.
  - unfold ConFilter.row_query. simpl. unfold compose.
    assert (Zlength (fold_right (fun (y : Z) (x : list bool) => upd_Znth y x true)
          (Zrepeat false num_cells) (map hash hs)) = num_cells). {
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
Hypothesis H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_cells) hashes.

Definition frame : Type := row.

Definition frame_sim (f : frame) (cf : ConFilter.frame) : Prop :=
  Forall2 (fun hash cr => row_sim hash f cr) hashes cf.

Definition frame_insert : forall (f : frame) (h : header_type), option frame :=
  row_insert.

Lemma frame_insert_sound : forall f cf h f',
  frame_sim f cf ->
  frame_insert f h = Some f' ->
  frame_sim f' (ConFilter.frame_insert cf (map (fun hash => hash h) hashes)).
Proof.
  intros.
  unfold frame_sim in *.
  assert (Zlength hashes = Zlength cf). {
    eapply Forall2_Zlength. eauto.
  }
  unfold ConFilter.frame_insert in *.
  rewrite Forall2_forall_range2.
  split; only 1 : list_solve.
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

Lemma frame_clear_sound : forall f cf i f',
  frame_sim f cf ->
  frame_clear f i = Some f' ->
  frame_sim f' (ConFilter.frame_clear cf (Zrepeat i num_rows)).
Proof.
  intros.
  unfold frame_sim in *.
  assert (Zlength hashes = Zlength cf). {
    eapply Forall2_Zlength. eauto.
  }
  unfold ConFilter.frame_clear in *.
  rewrite Forall2_forall_range2.
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
  assert (Zlength hashes = Zlength cf). {
    eapply Forall2_Zlength. eauto.
  }
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

End AbsFilter.
