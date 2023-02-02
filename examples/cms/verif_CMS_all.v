Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import ProD3.examples.cms.verif_CMS_1.
Require Import ProD3.examples.cms.verif_CMS_insert.
Require Import ProD3.examples.cms.verif_CMS_query.
Require Import ProD3.examples.cms.verif_CMS_clear.
Require Import ProD3.examples.cms.LightModel.
Require Import ProD3.examples.cms.LightRepr.

Definition hashes := common.hashes.

Lemma H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.
Proof.
  repeat apply Forall_cons.
  6 : apply Forall_nil.
  all : intros; apply Z.mod_pos_bound; apply H_num_slots.
Qed.

Notation cms := (@cms header_type).
Notation cms_repr := (@cms_repr num_frames num_rows num_slots frame_time
  H_num_slots H_num_rows _ hashes H_Zlength_hashes tick_time index_w panes rows).
Notation cms_insert := (@cms_insert header_type num_frames num_slots
  frame_time tick_time).
Notation cms_query := (@cms_query header_type num_frames frame_time hashes).
Notation cms_clear := (@cms_clear header_type num_frames num_slots
  frame_time tick_time).

Definition CMS_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : cms),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 INSERT; P4Bit 48 tstamp; P4Bit_ value_w]
        (MEM []
        (EXT [cms_repr p f])))
      POST
        (ARG_RET [P4Bit_ value_w] ValBaseNull
        (MEM []
        (EXT [cms_repr p (cms_insert f (tstamp, h))]))).

Lemma CMS_insert_body :
  func_sound ge CMS_fd nil CMS_insert_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_CMS_insert.CMS_insert_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold cms_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_CMS_insert.CMS_insert_body.
  { entailer. }
  { entailer.
    lazymatch goal with
    | |- ext_implies [verif_CMS_1.cms_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold cms_sim in *.
    destruct f.
    2 : { auto. }
    unfold LightModel.cms_insert.
    destruct (AbsModel.cms_insert num_frames num_slots frame_time tick_time _ (tstamp, h)) eqn:?H.
    2 : { auto. }
    eapply AbsModel.cms_insert_sound with (f' := c0) in H.
    6 : apply H0.
    - replace (AbsModel.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_CMS_1.hashes (header_to_val h)) in H. 2 : {
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

Definition CMS_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : cms),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 QUERY; P4Bit 48 tstamp; P4Bit_ value_w]
        (MEM []
        (EXT [cms_repr p f])))
      POST
        (ARG_RET [P4Bit_option value_w (option_map (fun n => Z.min n (2 ^ (Z.of_N value_w) - 1)) (cms_query (cms_clear f tstamp) (tstamp, h)))] ValBaseNull
        (MEM []
        (EXT [cms_repr p (cms_clear f tstamp)]))).

Lemma fst_query_eq_clear : forall (cf : ConModel.cms num_frames num_rows num_slots) tick is,
  fst (ConModel.cms_query H_num_frames H_num_rows H_num_slots frame_tick_tocks cf tick is)
    = (ConModel.cms_clear H_num_frames H_num_rows H_num_slots frame_tick_tocks cf tick).
Proof.
  intros.
  destruct cf. destruct cms_frames as [cms_frames H_cms_frames].
  simpl. f_equal.
  apply subset_eq_compat.
  f_equal. f_equal.
  apply subset_eq_compat.
  f_equal.
Qed.

Lemma cms_sim_weak_cms_inv : forall f cf,
  cms_sim (num_frames := num_frames) (frame_time := frame_time) H_num_slots H_num_rows hashes tick_time (Some f) cf ->
  weak_cms_inv num_frames frame_time (Some f).
Proof.
  intros.
  unfold cms_sim, weak_cms_inv in *.
  destruct f.
  inv H. inv H7.
  split.
  - change (AbsModel.frame_tick_tocks frame_time tick_time) with frame_tick_tocks in *.
    remember (fst (cms_timer cf) mod frame_tick_tocks * 2 + Z.b2z (snd (cms_timer cf))) as n.
    assert (0 <= n < frame_tick_tocks * 2). {
      subst n; clear.
      pose proof (Z.mod_pos_bound (fst (cms_timer cf)) frame_tick_tocks eq_refl).
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
    destruct (cms_frames cf).
    simpl in H4.
    remember (ConModel.get_clear_frame (AbsModel.frame_tick_tocks frame_time tick_time) (cms_timer cf)) as c.
    assert (0 <= c < num_frames). {
      subst c; apply get_clear_frame_range; auto.
      apply eq_refl.
    }
    apply Forall2_Zlength in H4.
    unfold AbsModel.frame in *.
    list_solve.
Qed.

Lemma CMS_query_body :
  func_sound ge CMS_fd nil CMS_query_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_CMS_query.CMS_query_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold cms_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_CMS_query.CMS_query_body.
  { entailer. }
  { entailer.
    { destruct f.
      2 : { repeat constructor. }
      destruct (cms_query (cms_clear _ tstamp) (tstamp, h)) as [res | ] eqn:?H.
      2 : repeat constructor.
      eapply abs_query_pattern_ok in H0.
      { destruct H0.
        eapply AbsModel.cms_query_sound in H.
        6 : apply H0.
        - replace (AbsModel.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
                (snd (tstamp, h))) with (verif_CMS_1.hashes (header_to_val h)) in H. 2 : {
            apply subset_eq_compat. auto.
          }
          replace (ConModel.cms_query _ _ _ _ _ _ _)
            with (verif_CMS_query.cms_query cf (Z.odd (tstamp / tick_time))
              (verif_CMS_1.hashes (header_to_val h))) in H by reflexivity.
          destruct (verif_CMS_query.cms_query _ _ _).
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
      - eapply cms_sim_weak_cms_inv; eauto.
    }
    rewrite fst_query_eq_clear.
    lazymatch goal with
    | |- ext_implies [verif_CMS_1.cms_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold cms_sim in *.
    unfold LightModel.cms_clear.
    destruct f.
    2 : { auto. }
    unfold LightModel.cms_clear.
    destruct (AbsModel.cms_clear num_frames num_slots frame_time tick_time _ tstamp) eqn:?H.
    2 : { auto. }
    eapply AbsModel.cms_clear_sound with (f' := c0) in H.
    6 : apply H0.
    - replace (AbsModel.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_CMS_1.hashes (header_to_val h)) in H. 2 : {
        apply subset_eq_compat. auto.
      }
      unfold verif_CMS_clear.cms_clear.
      apply H.
    - apply H_Zlength_hashes.
    - apply eq_refl.
    - apply eq_refl.
    - eexists frame_tick_tocks. apply eq_refl.
  }
Qed.

Definition CMS_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : header_type) (tstamp : Z) (f : cms),
      PRE
        (ARG [eval_val_to_sval (header_to_val h); P4Bit 8 CLEAR; P4Bit 48 tstamp; P4Bit_ value_w]
        (MEM []
        (EXT [cms_repr p f])))
      POST
        (ARG_RET [P4Bit_ value_w] ValBaseNull
        (MEM []
        (EXT [cms_repr p (cms_clear f tstamp)]))).

Lemma CMS_clear_body :
  func_sound ge CMS_fd nil CMS_clear_spec.
Proof.
  intros_fs_bind.
  split; only 2 : apply verif_CMS_clear.CMS_clear_body.
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold cms_repr.
  Intros cf.
  normalize_EXT.
  Intros_prop.
  eapply hoare_func_pre.
  2 : eapply hoare_func_post.
  2 : apply verif_CMS_clear.CMS_clear_body.
  { entailer. }
  { entailer.
    lazymatch goal with
    | |- ext_implies [verif_CMS_1.cms_repr _ _ _ _ ?f] _ =>
        Exists f
    end.
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold cms_sim in *.
    unfold LightModel.cms_clear.
    destruct f.
    2 : { auto. }
    unfold LightModel.cms_clear.
    destruct (AbsModel.cms_clear num_frames num_slots frame_time tick_time _ tstamp) eqn:?H.
    2 : { auto. }
    eapply AbsModel.cms_clear_sound with (f' := c0) in H.
    6 : apply H0.
    - replace (AbsModel.map_hashes num_rows H_num_rows hashes H_Zlength_hashes
            (snd (tstamp, h))) with (verif_CMS_1.hashes (header_to_val h)) in H. 2 : {
        apply subset_eq_compat. auto.
      }
      unfold verif_CMS_clear.cms_clear.
      apply H.
    - apply H_Zlength_hashes.
    - apply eq_refl.
    - apply eq_refl.
    - eexists frame_tick_tocks. apply eq_refl.
  }
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply CMS_insert_body) : func_specs.
