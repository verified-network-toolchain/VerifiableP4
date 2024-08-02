Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf_gen.p4ast.
Require Import ProD3.examples.sbf_gen.ConFilter.
Require Import ProD3.examples.sbf_gen.common.
Require Import ProD3.examples.sbf_gen.FilterRepr.
Require Import ProD3.examples.sbf_gen.verif_Win1.
Require Import ProD3.examples.sbf_gen.verif_Win2.
Require Import ProD3.examples.sbf_gen.verif_Win3.
Require Import ProD3.examples.sbf_gen.verif_Win4.
Require Import ProD3.examples.sbf_gen.verif_Filter.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_3_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_index_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_window_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_3_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_4_body) : func_specs.

Definition P4_bf2_win_md_t_query (f cf if' : Z) (new_clear_index : Sval) (is : list Sval) :=
  if f=? cf then
    P4_bf2_win_md_t (P4Bit 8 CLEAR) (Zrepeat new_clear_index 3)
  else
    P4_bf2_win_md_t (P4Bit 8 QUERY) is.

Definition tbl_set_win_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_1"; "api_1"];
               ["act_set_clear_win_1"; "api_2"];
               ["act_set_clear_win_1"; "api_3"];
               ["act_set_clear_win_1"; "api_4"];
               ["act_set_clear_win_2"; "api_1"];
               ["act_set_clear_win_2"; "api_2"];
               ["act_set_clear_win_2"; "api_3"];
               ["act_set_clear_win_2"; "api_4"];
               ["act_set_clear_win_3"; "api_1"];
               ["act_set_clear_win_3"; "api_2"];
               ["act_set_clear_win_3"; "api_3"];
               ["act_set_clear_win_3"; "api_4"];
               ["act_set_clear_win_2"; "api_1"];
               ["act_set_clear_win_4"; "api_1"];
               ["act_set_clear_win_4"; "api_2"];
               ["act_set_clear_win_4"; "api_3"];
               ["act_set_clear_win_4"; "api_4"]]) []
    WITH (timer : Z * bool) (clear_index_1 hash_index_1 hash_index_2 hash_index_3: Sval)
      (H_timer : 0 <= fst timer < frame_tick_tocks * num_frames),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 QUERY);
              (["ds_md"], ValBaseStruct
                 [("clear_window", P4Bit 16 (fst timer));
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t_);
                  ("win_2", P4_bf2_win_md_t_);
                  ("win_3", P4_bf2_win_md_t_);
                  ("win_4", P4_bf2_win_md_t_)])]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (let cf := get_clear_frame timer in
        let if' := get_insert_frame cf in
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", P4Bit 16 (fst timer));
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t_query 0 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_2", P4_bf2_win_md_t_query 1 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_3", P4_bf2_win_md_t_query 2 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_4", P4_bf2_win_md_t_query 3 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3])])]
        (EXT [])))))%arg_ret_assr.

Lemma tbl_set_win_query_body :
  func_sound ge tbl_set_win_fd nil tbl_set_win_query_spec.
Proof.
  start_function; elim_trivial_cases.
  - replace (get_clear_frame timer) with 0. 2 : {
      symmetry; eapply Z_div_squeeze'; eauto.
    }
    table_action act_set_clear_win_1_body.
    { entailer. }
    { entailer. }
  - replace (get_clear_frame timer) with 1. 2 : {
      symmetry; eapply Z_div_squeeze'; eauto.
    }
    table_action act_set_clear_win_2_body.
    { entailer. }
    { entailer. }
  - replace (get_clear_frame timer) with 2. 2 : {
      symmetry; eapply Z_div_squeeze'; eauto.
    }
    table_action act_set_clear_win_3_body.
    { entailer. }
    { entailer. }
  - replace (get_clear_frame timer) with 3. 2 : {
      symmetry; eapply Z_div_squeeze'; eauto.
    }
    table_action act_set_clear_win_4_body.
    { entailer. }
    { entailer. }
  - lia.
Qed.

Definition act_merge_wins_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_merge_wins"] ge).

Definition act_merge_wins_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH,
      PRE
        (ARG []
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["query_res"], (P4Bit 8 1))]
        (EXT []))).

Lemma act_merge_wins_body :
  func_sound ge act_merge_wins_fd nil act_merge_wins_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Qed.

Definition act_merge_default_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_merge_default"] ge).

Definition act_merge_default_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH,
      PRE
        (ARG []
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["query_res"], (P4Bit 8 0))]
        (EXT []))).

Lemma act_merge_default_body :
  func_sound ge act_merge_default_fd nil act_merge_default_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Qed.

Definition tbl_merge_wins_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_merge_wins"; "apply"] ge).

Definition P4_bf2_win_md_t_rw rw1 rw2 rw3 :=
  ValBaseStruct
    [("api", P4Bit_ 8);
     ("index_1", P4Bit_ index_w);
     ("index_2", P4Bit_ index_w);
     ("index_3", P4Bit_ index_w);
     ("rw_1", P4Bit 8 (Z.b2z rw1));
     ("rw_2", P4Bit 8 (Z.b2z rw2));
     ("rw_3", P4Bit 8 (Z.b2z rw3))].

(* Because this function doesn't modify ds_md, so we can describe it in this way.
But if it does modify ds_md, we don't have a really good way to isolate the unchanged part.
But on the other hand, the get/update system doesn't work very well, either. *)
Definition tbl_merge_wins_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH rw11 rw12 rw13 rw21 rw22 rw23 rw31 rw32 rw33 rw41 rw42 rw43,
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 QUERY);
              (["ds_md"], ValBaseStruct
                 [("clear_window", P4Bit_ 16);
                  ("clear_index_1", P4Bit_ index_w);
                  ("hash_index_1", P4Bit_ index_w);
                  ("hash_index_2", P4Bit_ index_w);
                  ("hash_index_3", P4Bit_ index_w);
                  ("win_1", P4_bf2_win_md_t_rw rw11 rw12 rw13);
                  ("win_2", P4_bf2_win_md_t_rw rw21 rw22 rw23);
                  ("win_3", P4_bf2_win_md_t_rw rw31 rw32 rw33);
                  ("win_4", P4_bf2_win_md_t_rw rw41 rw42 rw43)])]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["query_res"], (P4Bit 8 (Z.b2z (
          fold_orb (map fold_andb
            [[rw11; rw12; rw13];
             [rw21; rw22; rw23];
             [rw31; rw32; rw33];
             [rw41; rw42; rw43]])))))]
        (EXT []))))%arg_ret_assr.

Lemma b2z_one : forall b,
  Z.b2z b =? 1 = b.
Proof.
  destruct b; auto.
Qed.

Lemma tbl_merge_wins_body :
  func_sound ge tbl_merge_wins_fd nil tbl_merge_wins_spec.
Proof.
  unfold tbl_merge_wins_spec, P4_bf2_win_md_t_rw.
  start_function;
    repeat rewrite b2z_one in *;
    repeat lazymatch goal with
    | H : is_true (_ && _) |- _ =>
        apply Reflect.andE in H;
        destruct H
    end;
    repeat match goal with
    | H : is_true ?b |- _ =>
        is_var b;
        unfold is_true in H;
        subst b
    end.
  - table_action act_merge_wins_body.
    { entailer. }
    { entailer. }

#[export] Hint Rewrite Bool.orb_true_l Bool.orb_true_r Bool.orb_false_l Bool.orb_false_r : simpl_orb.

  - table_action act_merge_wins_body.
    { entailer. }
    { entailer.
      unfold map, fold_andb, fold_orb, fold_left.
      autorewrite with simpl_andb simpl_orb.
      apply sval_refine_refl.
    }
  - table_action act_merge_wins_body.
    { entailer. }
    { entailer.
      unfold map, fold_andb, fold_orb, fold_left.
      autorewrite with simpl_andb simpl_orb.
      apply sval_refine_refl.
    }
  - table_action act_merge_wins_body.
    { entailer. }
    { entailer.
      unfold map, fold_andb, fold_orb, fold_left.
      autorewrite with simpl_andb simpl_orb.
      apply sval_refine_refl.
    }
  - table_action act_merge_default_body.
    { entailer. }
    { entailer.
      unfold map, fold_andb, fold_orb, fold_left.
      autorewrite with simpl_andb simpl_orb.
      replace (rw11 && rw12 && rw13) with false by (destruct (rw11 && rw12 && rw13); auto).
      replace (rw21 && rw22 && rw23) with false by (destruct (rw21 && rw22 && rw23); auto).
      replace (rw31 && rw32 && rw33) with false by (destruct (rw31 && rw32 && rw33); auto).
      replace (rw41 && rw42 && rw43) with false by (destruct (rw41 && rw42 && rw43); auto).
      apply sval_refine_refl.
    }
  - elim_trivial_cases.
  - elim_trivial_cases.
Qed.

Definition filter_query := @filter_query num_frames num_rows num_slots H_num_frames H_num_rows H_num_slots
  frame_tick_tocks.

Definition Filter_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (key : Val) (tstamp : Z) (cf : filter num_frames num_rows num_slots),
      PRE
        (ARG [eval_val_to_sval key; P4Bit 8 QUERY; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [filter_repr p index_w panes rows cf])))
      POST
        (ARG_RET [P4Bit 8 (Z.b2z (snd (filter_query cf (Z.odd (tstamp/2097152)) (hashes key))))] ValBaseNull
        (MEM []
        (EXT [filter_repr p index_w panes rows (fst (filter_query cf (Z.odd (tstamp/2097152)) (hashes key)))]))).

Ltac destruct_listn l :=
  destruct l as [l ?H];
  destruct_list l.

Lemma Filter_query_body :
  func_sound ge Filter_fd nil Filter_query_spec.
Proof.
  start_function.
  destruct cf as [[ps ?H] ? ?].
  unfold filter_repr.
  cbn [proj1_sig] in *.
  destruct_list ps.
  normalize_EXT.
  step.
  step_call tbl_hash_index_1_body.
  { entailer. }
  Intros _.
  step_call tbl_hash_index_2_body.
  { entailer. }
  Intros _.
  step_call tbl_hash_index_3_body.
  { entailer. }
  Intros _.
  set (is := (exist _ [hash1 key; hash2 key; hash3 key] eq_refl : listn Z 3)).
  set (clear_is := (exist _ (Zrepeat fil_clear_index 3) eq_refl : listn Z 3)).
  assert (Forall (fun i : Z => 0 <= i < num_slots) (`is)). {
    repeat first [apply Forall_cons | apply Forall_nil].
    all : unfold hash1, hash2, hash3;
      apply Z.mod_pos_bound; lia.
  }
  P4assert (0 <= fil_clear_index < num_slots). {
    unfold fil_clear_index_repr.
    Intros i'.
    normalize_EXT.
    Intros_prop.
    apply ext_implies_prop_intro.
    subst.
    apply Z.mod_pos_bound.
    lia.
  }
  assert (Forall (fun i : Z => 0 <= i < num_slots) (`clear_is)). {
    repeat first [
      assumption
    | constructor
    ].
  }
  step_call tbl_clear_index_body.
  { entailer. }
  Intros _.
  step_call tbl_clear_window_body.
  { entailer. }
  Intros _.
  set (new_timer := update_timer fil_timer (Z.odd (tstamp / 2097152))).
  P4assert (0 <= fst new_timer < num_frames * frame_tick_tocks).
  { unfold timer_repr.
    normalize_EXT.
    Intros_prop.
    apply ext_implies_prop_intro.
    auto.
  }
  step_call tbl_set_win_query_body.
  { entailer. }
  { auto. }
  Intros _.
  (* unfold and fold in the post condition *)
  unfold filter_query, ConFilter.filter_query.
  (* cbn [proj1_sig fst snd]. *)
  unfold proj1_sig. unfold fst. unfold snd.
  fold new_timer.
  replace (exist (fun i : list Z => Zlength i = num_rows) (Zrepeat fil_clear_index num_rows) _) with clear_is. 2 : {
    apply subset_eq_compat. auto.
  }
  assert (0 <= get_clear_frame new_timer < num_frames). {
    unfold ConFilter.get_clear_frame.
    split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia.
  }
  destruct (get_clear_frame new_timer =? 0) eqn:?.
  { replace (get_clear_frame new_timer) with 0 by lia.
    step_call verif_Win1.Win_body _ _ clear_is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win2.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win3.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win4.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { unfold P4_bf2_win_md_t_rw.
      entailer.
      replace (P4Bit 8 0) with (P4Bit 8 (Z.b2z false)) by auto.
      repeat first [
        apply sval_refine_refl
      | constructor
      ].
    }
    Intros _.
    step.
    entailer.
    destruct_listn x.
    destruct_listn x0.
    destruct_listn x1.
    destruct_listn x2.
    apply sval_refine_refl.
  }
  destruct (get_clear_frame new_timer =? 1) eqn:?.
  { replace (get_clear_frame new_timer) with 1 by lia.
    step_call verif_Win1.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win2.Win_body _ _ clear_is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win3.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win4.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { unfold P4_bf2_win_md_t_rw.
      entailer.
      replace (P4Bit 8 0) with (P4Bit 8 (Z.b2z false)) by auto.
      repeat first [
        apply sval_refine_refl
      | constructor
      ].
    }
    Intros _.
    step.
    entailer.
    destruct_listn x.
    destruct_listn x0.
    destruct_listn x1.
    destruct_listn x2.
    apply sval_refine_refl.
  }
  destruct (get_clear_frame new_timer =? 2) eqn:?.
  { replace (get_clear_frame new_timer) with 2 by lia.
    step_call verif_Win1.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win2.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win3.Win_body _ _ clear_is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win4.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { unfold P4_bf2_win_md_t_rw.
      entailer.
      replace (P4Bit 8 0) with (P4Bit 8 (Z.b2z false)) by auto.
      repeat first [
        apply sval_refine_refl
      | constructor
      ].
    }
    Intros _.
    step.
    entailer.
    destruct_listn x.
    destruct_listn x0.
    destruct_listn x1.
    destruct_listn x2.
    apply sval_refine_refl.
  }
  destruct (get_clear_frame new_timer =? 3) eqn:?.
  { replace (get_clear_frame new_timer) with 3 by lia.
    step_call verif_Win1.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win2.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win3.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    step_call verif_Win4.Win_body _ _ clear_is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { unfold P4_bf2_win_md_t_rw.
      entailer.
      replace (P4Bit 8 0) with (P4Bit 8 (Z.b2z false)) by auto.
      repeat first [
        apply sval_refine_refl
      | constructor
      ].
    }
    Intros _.
    step.
    entailer.
    destruct_listn x.
    destruct_listn x0.
    destruct_listn x1.
    destruct_listn x2.
    apply sval_refine_refl.
  }
  lia.
(* This is slow. I can understand it but I don't know the direct reason. *)
Time Qed.
