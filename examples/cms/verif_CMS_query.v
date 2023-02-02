Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import ProD3.examples.cms.verif_Win1.
Require Import ProD3.examples.cms.verif_Win2.
Require Import ProD3.examples.cms.verif_Win3.
Require Import ProD3.examples.cms.verif_CMS_1.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_3_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_4_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_5_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_index_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_window_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_3_body) : func_specs.

Definition P4_bf2_win_md_t_query (f cf if' : Z) (new_clear_index : Sval) (is : list Sval) :=
  if f=? cf then
    P4_bf2_win_md_t (P4Bit 8 CLEAR) (Zrepeat new_clear_index 5)
  else
    P4_bf2_win_md_t (P4Bit 8 QUERY) is.

Definition tbl_set_win_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_1"; "api_1"];
               ["act_set_clear_win_1"; "api_2"];
               ["act_set_clear_win_1"; "api_3"];
               ["act_set_clear_win_2"; "api_1"];
               ["act_set_clear_win_2"; "api_2"];
               ["act_set_clear_win_2"; "api_3"];
               ["act_set_clear_win_3"; "api_1"];
               ["act_set_clear_win_3"; "api_2"];
               ["act_set_clear_win_3"; "api_3"];
               ["act_set_clear_win_4"; "api_1"];
               ["act_set_clear_win_4"; "api_2"];
               ["act_set_clear_win_4"; "api_3"];
               ["act_set_clear_win_5"; "api_1"];
               ["act_set_clear_win_5"; "api_2"];
               ["act_set_clear_win_5"; "api_3"]]) []
    WITH (timer : Z * bool) (clear_index_1 hash_index_1 hash_index_2 hash_index_3 hash_index_4 hash_index_5 : Sval)
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
                  ("hash_index_4", hash_index_4);
                  ("hash_index_5", hash_index_5);
                  ("win_1", P4_bf2_win_md_t_);
                  ("win_2", P4_bf2_win_md_t_);
                  ("win_3", P4_bf2_win_md_t_)])]
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
                  ("hash_index_4", hash_index_4);
                  ("hash_index_5", hash_index_5);
                  ("win_1", P4_bf2_win_md_t_query 0 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_2", P4_bf2_win_md_t_query 1 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_3", P4_bf2_win_md_t_query 2 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5])])]
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
  - lia.
Qed.

(* Definition act_merge_wins_fd :=
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
Qed. *)

(* Definition tbl_merge_wins_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_merge_wins"; "apply"] ge). *)

Definition tbl_merge_wins_final_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH ds_md,
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 QUERY);
              (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["query_res"], abs_plus_sat
          (get "rw_1" (get "win_1" ds_md))
          (get "rw_1" (get "win_2" ds_md)))]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_wins_final_body :
  func_sound ge tbl_merge_wins_final_fd nil tbl_merge_wins_final_spec.
Proof.
  start_function; elim_trivial_cases.
  2 : lia.
  table_action act_merge_wins_final_body.
  { entailer. }
  { reflexivity. }
  { reflexivity. }
  { entailer. }
Qed.

#[local] Instance Inhabitant_ext_pred : Inhabitant ext_pred :=
  ExtPred.prop True.

Lemma ext_implies_ext : forall a1 a2,
  Zlength a1 = Zlength a2 ->
  (forall i, 0 <= i < Zlength a1 -> ext_implies [Znth i a1] [Znth i a2]) ->
  ext_implies a1 a2.
Proof.
Admitted.

Require Import ProD3.examples.sbf.Utils.

Lemma frame_query_bound : forall p (* rows *) (cf : frame) is,
  (* Zlength rows = num_rows -> *)
  Zlength is = num_rows ->
  Forall (fun i : Z => 0 <= i < num_slots) is ->
  ext_implies [frame_repr p rows cf] [ExtPred.prop (frame_query cf is >= 0)].
Proof.
  intros.
  assert (Zlength rows = num_rows) by auto.
  unfold frame_repr, frame_query.
  rewrite ext_pred_wrap_cons.
  eapply ext_implies_trans with (map2 (fun cr i => ExtPred.prop (row_query cr i >= 0)) (proj1_sig cf) is).
  - destruct cf as [crs ?].
    cbn [proj1_sig].
    apply ext_implies_ext.
    { list_solve. }
    intros.
    list_simplify.
    do 2 rewrite Znth_map2 by list_solve.
    apply row_query_bound; list_solve.
  - (* 
      list_solve.
  generalize dependent cf.
  
  destruct cr as [cr ?H]. unfold row_query. cbn [proj1_sig].
  normalize_EXT.
  Intros_prop.
  apply ext_implies_prop_intro.
  list_solve. *)
(* Qed. *)
Admitted.

Definition cms_query := @cms_query num_frames num_rows num_slots H_num_frames H_num_rows H_num_slots
  frame_tick_tocks.

Definition Filter_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (key : Val) (tstamp : Z) (cf : cms num_frames num_rows num_slots),
      PRE
        (ARG [eval_val_to_sval key; P4Bit 8 QUERY; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [cms_repr p index_w panes rows cf])))
      POST
        (ARG_RET [P4Bit value_w (Z.min (
          snd (cms_query cf (Z.odd (tstamp/tick_time)) (hashes key)))
          (2 ^ 32 -1))] ValBaseNull
        (MEM []
        (EXT [cms_repr p index_w panes rows (fst (cms_query cf (Z.odd (tstamp/tick_time)) (hashes key)))]))).

Ltac destruct_listn l :=
  destruct l as [l ?H];
  destruct_list l.

Lemma Filter_query_body :
  func_sound ge Filter_fd nil Filter_query_spec.
Proof.
  start_function.
  destruct cf as [[ps ?H] ? ?].
  unfold cms_repr.
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
  step_call tbl_hash_index_4_body.
  { entailer. }
  Intros _.
  step_call tbl_hash_index_5_body.
  { entailer. }
  Intros _.
  set (is := (exist _ [hash1 key; hash2 key; hash3 key; hash4 key; hash5 key] eq_refl : listn Z 5)).
  set (clear_is := (exist _ (Zrepeat cms_clear_index 5) eq_refl : listn Z 5)).
  assert (Forall (fun i : Z => 0 <= i < num_slots) (`is)). {
    repeat first [apply Forall_cons | apply Forall_nil].
    all : unfold hash1, hash2, hash3;
      apply Z.mod_pos_bound; lia.
  }
  P4assert (0 <= cms_clear_index < num_slots). {
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
  set (new_timer := update_timer cms_timer (Z.odd (tstamp / tick_time))).
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
  unfold cms_query, ConModel.cms_query.
  (* cbn [proj1_sig fst snd]. *)
  unfold proj1_sig. unfold fst. unfold snd.
  fold new_timer.
  replace (exist (fun i : list Z => Zlength i = num_rows) (Zrepeat cms_clear_index num_rows) _) with clear_is. 2 : {
    apply subset_eq_compat. auto.
  }
  assert (0 <= get_clear_frame new_timer < num_frames). {
    unfold ConModel.get_clear_frame.
    split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia.
  }

Ltac pose_frame_query_bound f is :=
  P4assert (frame_query f (`is) >= 0);
  only 1 : (
    eapply ext_implies_trans;
    only 2 : (apply frame_query_bound; auto);
    entailer
  ).

  pose_frame_query_bound x is.
  pose_frame_query_bound x0 is.
  pose_frame_query_bound x1 is.

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
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_1_body.
    { entailer. }
    { reflexivity. }
    { reflexivity. }
    Intros _.
    simpl_assertion.
    step_into.
    { hoare_func_table; elim_trivial_cases.
      2 : { clear -H8; lia. }
      table_action act_merge_wins_final_body.
      { entailer. }
      { reflexivity. }
      { reflexivity. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    entailer.
    simpl_assertion.
    repeat rewrite abs_plus_sat_bit.
    repeat rewrite sat_bound_spec.
    unfold value_w.
    rewrite_strat bottomup mod_bound_small.
    2-5 : lia.
    apply sval_refine_refl'. f_equal.
    unfold Zsum, fold_left. simpl.
    change ([hash1 key; hash2 key; hash3 key; hash4 key; hash5 key])
      with (`is).
    lia.
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
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_1_body.
    { entailer. }
    { reflexivity. }
    { reflexivity. }
    Intros _.
    simpl_assertion.
    step_into.
    { hoare_func_table; elim_trivial_cases.
      2 : { clear -H8; lia. }
      table_action act_merge_wins_final_body.
      { entailer. }
      { reflexivity. }
      { reflexivity. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    entailer.
    simpl_assertion.
    repeat rewrite abs_plus_sat_bit.
    repeat rewrite sat_bound_spec.
    unfold value_w.
    rewrite_strat bottomup mod_bound_small.
    2-5 : lia.
    apply sval_refine_refl'. f_equal.
    unfold Zsum, fold_left. simpl.
    change ([hash1 key; hash2 key; hash3 key; hash4 key; hash5 key])
      with (`is).
    lia.
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
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_1_body.
    { entailer. }
    { reflexivity. }
    { reflexivity. }
    Intros _.
    simpl_assertion.
    step_into.
    { hoare_func_table; elim_trivial_cases.
      2 : { clear -H8; lia. }
      table_action act_merge_wins_final_body.
      { entailer. }
      { reflexivity. }
      { reflexivity. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    entailer.
    simpl_assertion.
    repeat rewrite abs_plus_sat_bit.
    repeat rewrite sat_bound_spec.
    unfold value_w.
    rewrite_strat bottomup mod_bound_small.
    2-5 : lia.
    apply sval_refine_refl'. f_equal.
    unfold Zsum, fold_left. simpl.
    change ([hash1 key; hash2 key; hash3 key; hash4 key; hash5 key])
      with (`is).
    lia.
  }
  lia.
(* This is slow. I can understand it but I don't know the direct reason. *)
Qed.
