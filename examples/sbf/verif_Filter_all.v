Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import ProD3.examples.sbf.verif_Filter.
Require Import ProD3.examples.sbf.verif_Filter_insert.
Require Import ProD3.examples.sbf.verif_Filter_query.
Require Import ProD3.examples.sbf.verif_Filter_clear.
Require Import ProD3.examples.sbf.LightFilter.
Require Import ProD3.examples.sbf.LightRepr.

Definition hashes := common.hashes.

Lemma H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.
Proof.
  repeat apply Forall_cons.
  4 : apply Forall_nil.
  all : intros; apply Z.mod_pos_bound; apply H_num_slots.
Qed.

Notation filter := (@filter header_type).
Notation filter_repr := (@filter_repr num_frames num_rows num_slots frame_time
  H_num_slots H_num_rows _ hashes H_Zlength_hashes tick_time index_w panes rows).
Notation filter_insert := (@filter_insert header_type num_frames num_slots
  frame_time tick_time).
Notation filter_query := (@filter_query header_type num_frames frame_time hashes).
Notation filter_clear := (@filter_clear header_type num_frames num_slots
  frame_time tick_time).


Definition Filter_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : filter),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 INSERT; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [filter_repr p f])))
      POST
        (ARG_RET [P4Bit_ 8] ValBaseNull
        (MEM []
        (EXT [filter_repr p (filter_insert f (tstamp, h))]))).

Lemma Filter_insert_body :
  func_sound ge Filter_fd nil Filter_insert_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_Filter_insert.Filter_insert_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold filter_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_Filter_insert.Filter_insert_body.
  { entailer. }
  { entailer.
    lazymatch goal with
    | |- ext_implies [verif_Filter.filter_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold filter_sim in *.
    destruct f.
    2 : { auto. }
    unfold LightFilter.filter_insert.
    destruct (AbsFilter.filter_insert num_frames num_slots frame_time tick_time f (tstamp, h)) eqn:?H.
    2 : { auto. }
    eapply AbsFilter.filter_insert_sound with (f' := f0) in H.
    6 : apply H0.
    - replace (AbsFilter.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_Filter.hashes (header_to_val h)) in H. 2 : {
        apply subset_eq_compat. auto.
      }
      apply H.
    - apply H_hashes.
    - apply eq_refl.
    - apply eq_refl.
    - eexists frame_tick_tocks. apply eq_refl.
  }
Qed.

Definition P4Bit_option w ov :=
  match ov with
  | Some v => P4Bit w v
  | None => P4Bit_ w
  end.

Definition Filter_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : filter),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 QUERY; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [filter_repr p f])))
      POST
        (ARG_RET [P4Bit_option 8 (option_map Z.b2z (filter_query (filter_clear f tstamp) (tstamp, h)))] ValBaseNull
        (MEM []
        (EXT [filter_repr p (filter_clear f tstamp)]))).

Lemma fst_query_eq_clear : forall (cf : ConFilter.filter num_frames num_rows num_slots) tick is,
  fst (ConFilter.filter_query H_num_frames H_num_rows H_num_slots frame_tick_tocks cf tick is)
    = (ConFilter.filter_clear H_num_frames H_num_rows H_num_slots frame_tick_tocks cf tick).
Proof.
  intros.
  destruct cf. destruct fil_frames as [fil_frames H_fil_frames].
  simpl. f_equal.
  apply subset_eq_compat.
  f_equal. f_equal.
  apply subset_eq_compat.
  f_equal.
Qed.

Lemma filter_sim_weak_filter_inv : forall f cf,
  filter_sim (num_frames := num_frames) (frame_time := frame_time) H_num_slots H_num_rows hashes tick_time (Some f) cf ->
  weak_filter_inv num_frames frame_time (Some f).
Proof.
  intros.
  unfold filter_sim, weak_filter_inv in *.
  destruct f.
  inv H. inv H7.
  split.
  - change (AbsFilter.frame_tick_tocks frame_time tick_time) with frame_tick_tocks in *.
    remember (fst (fil_timer cf) mod frame_tick_tocks * 2 + Z.b2z (snd (fil_timer cf))) as n.
    assert (0 <= n < frame_tick_tocks * 2). {
      subst n; clear.
      pose proof (Z.mod_pos_bound (fst (fil_timer cf)) frame_tick_tocks eq_refl).
      lia.
    }
    clear -H0 H1.
    simpl in H0.
    assert (0 <= n * tick_time <= frame_time - tick_time). {
      change 0 with (0 * tick_time).
      change (frame_time - tick_time) with ((frame_tick_tocks * 2 - 1) * tick_time).
      nia.
    }
    lia.
  - clear -H4 H10.
    destruct (fil_frames cf).
    simpl in H4.
    remember (ConFilter.get_clear_frame (AbsFilter.frame_tick_tocks frame_time tick_time) (fil_timer cf)) as c.
    assert (0 <= c < num_frames). {
      subst c; apply get_clear_frame_range; auto.
      apply eq_refl.
    }
    apply Forall2_Zlength in H4.
    unfold AbsFilter.frame in *.
    list_solve.
Qed.

Lemma Filter_query_body :
  func_sound ge Filter_fd nil Filter_query_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_Filter_query.Filter_query_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold filter_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_Filter_query.Filter_query_body.
  { entailer. }
  { entailer.
    { destruct f.
      2 : { repeat constructor. }
      destruct (filter_query (filter_clear _ tstamp) (tstamp, h)) as [res | ] eqn:?H.
      2 : repeat constructor.
      eapply abs_query_pattern_ok in H0.
      { destruct H0.
        eapply AbsFilter.filter_query_sound in H.
        6 : apply H0.
        - replace (AbsFilter.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
                (snd (tstamp, h))) with (verif_Filter.hashes (header_to_val h)) in H. 2 : {
            apply subset_eq_compat. auto.
          }
          replace (ConFilter.filter_query _ _ _ _ _ _ _)
            with (verif_Filter_query.filter_query cf (Z.odd (tstamp / 2097152))
              (verif_Filter.hashes (header_to_val h))) in H by reflexivity.
          destruct (verif_Filter_query.filter_query _ _ _).
          destruct H; subst.
          apply sval_refine_refl.
        - apply H_hashes.
        - apply eq_refl.
        - apply eq_refl.
        - eexists frame_tick_tocks. apply eq_refl.
      }
      - apply H_num_rows.
      - apply H_num_frames.
      - apply H_Zlength_hashes.
      - apply eq_refl.
      - apply eq_refl.
      - eexists frame_tick_tocks. apply eq_refl.
      - eapply filter_sim_weak_filter_inv; eauto.
    }
    rewrite fst_query_eq_clear.
    lazymatch goal with
    | |- ext_implies [verif_Filter.filter_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold filter_sim in *.
    unfold LightFilter.filter_clear.
    destruct f.
    2 : { auto. }
    unfold LightFilter.filter_clear.
    destruct (AbsFilter.filter_clear num_frames num_slots frame_time tick_time f tstamp) eqn:?H.
    2 : { auto. }
    eapply AbsFilter.filter_clear_sound with (f' := f0) in H.
    6 : apply H0.
    - replace (AbsFilter.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_Filter.hashes (header_to_val h)) in H. 2 : {
        apply subset_eq_compat. auto.
      }
      unfold verif_Filter_clear.filter_clear.
      apply H.
    - apply H_Zlength_hashes.
    - apply eq_refl.
    - apply eq_refl.
    - eexists frame_tick_tocks. apply eq_refl.
  }
Qed.

Definition Filter_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : filter),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 CLEAR; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [filter_repr p f])))
      POST
        (ARG_RET [P4Bit_ 8] ValBaseNull
        (MEM []
        (EXT [filter_repr p (filter_clear f tstamp)]))).

Lemma Filter_clear_body :
  func_sound ge Filter_fd nil Filter_clear_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_Filter_clear.Filter_clear_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold filter_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_Filter_clear.Filter_clear_body.
  { entailer. }
  { entailer.
    lazymatch goal with
    | |- ext_implies [verif_Filter.filter_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold filter_sim in *.
    unfold LightFilter.filter_clear.
    destruct f.
    2 : { auto. }
    unfold LightFilter.filter_clear.
    destruct (AbsFilter.filter_clear num_frames num_slots frame_time tick_time f tstamp) eqn:?H.
    2 : { auto. }
    eapply AbsFilter.filter_clear_sound with (f' := f0) in H.
    6 : apply H0.
    - replace (AbsFilter.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_Filter.hashes (header_to_val h)) in H. 2 : {
        apply subset_eq_compat. auto.
      }
      unfold verif_Filter_clear.filter_clear.
      apply H.
    - apply H_Zlength_hashes.
    - apply eq_refl.
    - apply eq_refl.
    - eexists frame_tick_tocks. apply eq_refl.
  }
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Filter_insert_body) : func_specs.
