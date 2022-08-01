Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import ProD3.examples.sbf.verif_Win1.
Require Import ProD3.examples.sbf.verif_Win2.
Require Import ProD3.examples.sbf.verif_Win3.
Require Import ProD3.examples.sbf.verif_Win4.
Require Import ProD3.examples.sbf.verif_Filter.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_index_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_window_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_3_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_4_body) : func_specs.

Definition P4_bf2_win_md_t_insert (f cf if' : Z) (new_clear_index : Sval) (is : list Sval) :=
  if f=? cf then
    P4_bf2_win_md_t (P4Bit 8 CLEAR) (Zrepeat new_clear_index 3)
  else if f=? if' then
    P4_bf2_win_md_t (P4Bit 8 INSERT) is
  else
    P4_bf2_win_md_t (P4Bit 8 NOOP) is.

Definition tbl_set_win_insert_spec : func_spec :=
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
        (MEM [(["api"], P4Bit 8 INSERT);
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
                  ("win_1", P4_bf2_win_md_t_insert 0 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_2", P4_bf2_win_md_t_insert 1 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_3", P4_bf2_win_md_t_insert 2 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_4", P4_bf2_win_md_t_insert 3 cf if' clear_index_1
                        [hash_index_1; hash_index_2; hash_index_3])])]
        (EXT [])))))%arg_ret_assr.

Lemma tbl_set_win_insert_body :
  func_sound ge tbl_set_win_fd nil tbl_set_win_insert_spec.
Proof.
  start_function.
  hoare_table_action_cases'.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_set_win_insert_body) : func_specs.

Definition tbl_merge_wins_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_merge_wins"; "apply"] ge).

Definition tbl_merge_wins_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH,
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 INSERT);
              (["query_res"], (P4Bit_ 8));
              (["ds_md"], ValBaseStruct
                 [("clear_window", P4Bit_ 16);
                  ("clear_index_1", P4Bit_ 18);
                  ("hash_index_1", P4Bit_ 18);
                  ("hash_index_2", P4Bit_ 18);
                  ("hash_index_3", P4Bit_ 18);
                  ("win_1", P4_bf2_win_md_t_);
                  ("win_2", P4_bf2_win_md_t_);
                  ("win_3", P4_bf2_win_md_t_);
                  ("win_4", P4_bf2_win_md_t_)])]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["query_res"], (P4Bit_ 8))]
        (EXT []))))%arg_ret_assr.

Ltac hoare_func_table ::= idtac.

Lemma Forall2_inv_cons {A} {B} : forall (P : A -> B -> Prop) a al bl,
  Forall2 P (a :: al) bl ->
  exists b bl', P a b /\ Forall2 P al bl' /\ bl = b :: bl'.
Proof.
  inversion 1; eauto.
Qed.

Lemma Forall2_inv_nil {A} {B} : forall (P : A -> B -> Prop) bl,
  Forall2 P nil bl ->
  bl = nil.
Proof.
  inversion 1; eauto.
Qed.

Lemma Forall2_inv_cons' {A} {B} : forall (P : A -> B -> Prop) a al b bl,
  Forall2 P (a :: al) (b :: bl) ->
  P a b /\ Forall2 P al bl.
Proof.
  inversion 1; eauto.
Qed.

Lemma tbl_merge_wins_body :
  func_sound ge tbl_merge_wins_fd nil tbl_merge_wins_spec.
Proof.
  start_function.

  Time hoare_func_table_nondet.
  
(* Ltac simpl1 := repeat (pinv Forall2; try simpl_sval_to_val).

Ltac simpl2 :=
  repeat lazymatch goal with
  | H : Forall2 (sval_to_val read_ndetbit) (_ :: _) _ |- _ =>
      apply Forall2_inv_cons in H;
      destruct H as [?x [?l [? [? ?]]]]; subst;
      try simpl_sval_to_val
  | H : Forall2 (sval_to_val read_ndetbit) nil _ |- _ =>
      apply Forall2_inv_nil in H;
      subst
  end.

Ltac simpl3 :=
  lazymatch goal with
  | H : Forall2 (sval_to_val read_ndetbit) ?keysvals ?keyvals |- _ =>
      eassert (Zlength keyvals = Zlength keysvals) by (apply eq_sym, (Forall2_Zlength H))(* ;
      destruct_list keyvals;
      repeat lazymatch goal with
      | H : Forall2 (sval_to_val read_ndetbit) (_ :: _) (_ :: _) |- _ =>
          apply Forall2_inv_cons' in H;
          destruct H
      | H : Forall2 (sval_to_val read_ndetbit) [] [] |- _ =>
          clear H
      end;
      repeat simpl_sval_to_val *)
  end. *)

  (* Time simpl3.
  Time assert (exists x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
    keyvals = [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11]) by
      (destruct_list keyvals; eauto 100);
    do 13 destruct H1; subst.
  repeat simpl_sval_to_val.
  eexists; split; only 1 : hoare_extern_match_list;
        apply hoare_table_action_cases'_hoare_table_action_cases;
        hoare_table_action_cases'; elim_trivial_cases.
  Time destruct_list' keyvals.

  assert (Zlength keyvals = 13) by (apply eq_sym, (Forall2_Zlength H)).
  Time assert (exists x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
    keyvals = [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11]) by
      (destruct_list keyvals; eauto 100).

  Time simpl3. *)

  (* assert (Zlength keyvals = 13) by (apply eq_sym, (Forall2_Zlength H)).
  Time assert (exists x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
    keyvals = [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11]) by
      (destruct_list keyvals; eauto 100).
  Time do 13 destruct H1. Time subst.
  Time repeat lazymatch goal with
  | H : Forall2 (sval_to_val read_ndetbit) (_ :: _) (_ :: _) |- _ =>
      apply Forall2_inv_cons' in H;
      destruct H
  end.
  Time repeat simpl_sval_to_val.
  eexists; split; only 1 : hoare_extern_match_list;
        apply hoare_table_action_cases'_hoare_table_action_cases;
        hoare_table_action_cases'; elim_trivial_cases. *)

  table_action NoAction_body.
  { entailer. }
  { entailer. }
Time Qed.

Definition filter_insert := @filter_insert num_frames num_rows num_slots ltac:(lia) ltac:(lia) ltac:(lia)
  frame_tick_tocks.

Definition Filter_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (key : Val) (tstamp : Z) (cf : filter num_frames num_rows num_slots),
      PRE
        (ARG [eval_val_to_sval key; P4Bit 8 INSERT; P4Bit 48 tstamp; P4Bit_ 8]
        (MEM []
        (EXT [filter_repr p 18 panes rows cf])))
      POST
        (ARG_RET [P4Bit_ 8] ValBaseNull
        (MEM []
        (EXT [filter_repr p 18 panes rows (filter_insert cf (Z.odd (tstamp/2097152)) (hashes key))]))).

Lemma Filter_insert_body :
  func_sound ge Filter_fd nil Filter_insert_spec.
Proof.
  Time start_function.
  destruct cf as [[ps ?H] ? ?].
  unfold filter_repr.
  cbn [proj1_sig] in *.
  destruct_list ps.
  normalize_EXT.
  Time step.
  Time step_call tbl_hash_index_1_body.
  { entailer. }
  Intros _.
  step_call tbl_hash_index_2_body.
  { entailer. }
  Time simpl_assertion.
  Intros _.
  step_call tbl_hash_index_3_body.
  { entailer. }
  Time simpl_assertion.
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
  Time simpl_assertion.
  Intros _.
  step_call tbl_clear_window_body.
  { entailer. }
  Intros _.
  set (new_timer := update_timer fil_timer (Z.odd (tstamp / 2097152))).
  (* We need assert_Prop. *)
  P4assert (0 <= fst new_timer < num_frames * frame_tick_tocks).
  { unfold timer_repr.
    normalize_EXT.
    Intros_prop.
    apply ext_implies_prop_intro.
    auto.
  }
  step_call tbl_set_win_insert_body.
  { entailer. }
  { auto. }
  Intros _.
  (* unfold and fold in the post condition *)
  unfold filter_insert, ConFilter.filter_insert.
  unfold proj1_sig.
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
    { entailer.
      repeat constructor.
    }
    Intros _.
    step.
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
    step_call verif_Win4.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { entailer.
      repeat constructor.
    }
    Intros _.
    step.
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
    step_call verif_Win4.Win_body _ _ is.
    { entailer. }
    { solve [repeat constructor]. }
    { auto. }
    simpl Z.eqb. cbn match.
    step_call tbl_merge_wins_body.
    { entailer.
      repeat constructor.
    }
    Intros _.
    step.
    entailer.
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
    { entailer.
      repeat constructor.
    }
    Intros _.
    step.
    entailer.
  }
  lia.
Time Qed.
