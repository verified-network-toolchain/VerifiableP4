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

Definition P4_bf2_win_md_t_clear (f cf if' : Z) (new_clear_index : Sval) (is : list Sval) :=
  if f=? cf then
    P4_bf2_win_md_t (P4Bit 8 CLEAR) (Zrepeat new_clear_index 5)
  else
    P4_bf2_win_md_t (P4Bit 8 NOOP) is.

Definition tbl_set_win_clear_spec : func_spec :=
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
        (MEM [(["api"], P4Bit 8 CLEAR);
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
                  ("win_1", P4_bf2_win_md_t_clear 0 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_2", P4_bf2_win_md_t_clear 1 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_3", P4_bf2_win_md_t_clear 2 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5])])]
        (EXT [])))))%arg_ret_assr.

Lemma tbl_set_win_clear_body :
  func_sound ge tbl_set_win_fd nil tbl_set_win_clear_spec.
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

Definition cms_clear := @cms_clear num_frames num_rows num_slots H_num_frames H_num_rows H_num_slots
  frame_tick_tocks.

Definition CMS_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (key : Val) (tstamp : Z) (cf : cms num_frames num_rows num_slots),
      PRE
        (ARG [eval_val_to_sval key; P4Bit 8 CLEAR; P4Bit 48 tstamp; P4Bit_ value_w]
        (MEM []
        (EXT [cms_repr p index_w panes rows cf])))
      POST
        (ARG_RET [P4Bit_ value_w] ValBaseNull
        (MEM []
        (EXT [cms_repr p index_w panes rows (cms_clear cf (Z.odd (tstamp/tick_time)))]))).

Lemma CMS_clear_body :
  func_sound ge CMS_fd nil CMS_clear_spec.
Proof.
  Time start_function.
  destruct cf as [[ps ?H] ? ?].
  unfold cms_repr.
  cbn [proj1_sig] in *.
  destruct_list ps.
  normalize_EXT.
  Time step.
  Time step_call tbl_hash_index_1_body.
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
  Time simpl_assertion.
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
  step_call tbl_set_win_clear_body.
  { entailer. }
  { auto. }
  Intros _.
  (* unfold and fold in the post condition *)
  unfold cms_clear, ConModel.cms_clear.
  unfold proj1_sig.
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
      { clear -H5; lia. }
      table_action (@NoAction_body Info).
      { entailer. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    simpl_assertion.
    entailer.
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
      { clear -H5; lia. }
      table_action (@NoAction_body Info).
      { entailer. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    simpl_assertion.
    entailer.
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
      { clear -H5; lia. }
      table_action (@NoAction_body Info).
      { entailer. }
      { apply arg_ret_implies_refl. }
    }
    { reflexivity. }
    { reflexivity. }
    simpl_assertion.
    entailer.
  }
  lia.
Time Qed.
