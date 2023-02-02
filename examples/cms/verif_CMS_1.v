Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "cm2_ds"].

Definition act_hash_index_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_hash_index_1"] ge).

Definition act_hash_index_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_1"; "t'0"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_1" (P4Bit index_w (hash1 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_1() {
        ds_md.hash_index_1 = hash_idx_1.get(ds_key)[17:0];
    }
*)

Lemma act_hash_index_1_body :
  func_sound ge act_hash_index_1_fd nil act_hash_index_1_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bitstring_slice_lower_bit with (w' := index_w) by lia.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    apply P4Bit_mod_eq.
    unfold hash1.
    rewrite Z.mod_mod by lia.
    auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_1_body) : func_specs.

Definition tbl_hash_index_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_hash_index_1"; "apply"] ge).

Definition tbl_hash_index_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_1"; "t'0"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "hash_index_1" (P4Bit index_w (hash1 key)) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_hash_index_1_body :
  func_sound ge tbl_hash_index_1_fd nil tbl_hash_index_1_spec.
Proof.
  start_function.
  table_action act_hash_index_1_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.

Definition act_hash_index_2_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_hash_index_2"] ge).

Definition act_hash_index_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_2"; "t'1"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_2" (P4Bit index_w (hash2 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_2() {
        ds_md.hash_index_2 = hash_idx_2.get(ds_key)[17:0];
    }
*)

Lemma act_hash_index_2_body :
  func_sound ge act_hash_index_2_fd nil act_hash_index_2_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bitstring_slice_lower_bit with (w' := index_w) by lia.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    apply P4Bit_mod_eq.
    unfold hash2.
    rewrite Z.mod_mod by lia.
    auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_2_body) : func_specs.

Definition tbl_hash_index_2_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_hash_index_2"; "apply"] ge).

Definition tbl_hash_index_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_2"; "t'1"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "hash_index_2" (P4Bit index_w (hash2 key)) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_hash_index_2_body :
  func_sound ge tbl_hash_index_2_fd nil tbl_hash_index_2_spec.
Proof.
  start_function.
  table_action act_hash_index_2_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_2_body) : func_specs.

Definition act_hash_index_3_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_hash_index_3"] ge).

Definition act_hash_index_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_3"; "t'2"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_3" (P4Bit index_w (hash3 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_3() {
        ds_md.hash_index_3 = hash_idx_3.get(ds_key)[17:0];
    }
*)

Lemma act_hash_index_3_body :
  func_sound ge act_hash_index_3_fd nil act_hash_index_3_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bitstring_slice_lower_bit with (w' := index_w) by lia.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    apply P4Bit_mod_eq.
    unfold hash3.
    rewrite Z.mod_mod by lia.
    auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_3_body) : func_specs.

Definition tbl_hash_index_3_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_hash_index_3"; "apply"] ge).

Definition tbl_hash_index_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_3"; "t'2"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "hash_index_3" (P4Bit index_w (hash3 key)) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_hash_index_3_body :
  func_sound ge tbl_hash_index_3_fd nil tbl_hash_index_3_spec.
Proof.
  start_function.
  table_action act_hash_index_3_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_3_body) : func_specs.

Definition act_hash_index_4_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_hash_index_4"] ge).

Definition act_hash_index_4_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_4"; "t'3"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_4" (P4Bit index_w (hash4 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_4() {
        ds_md.hash_index_4 = hash_idx_4.get(ds_key)[17:0];
    }
*)

Lemma act_hash_index_4_body :
  func_sound ge act_hash_index_4_fd nil act_hash_index_4_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bitstring_slice_lower_bit with (w' := index_w) by lia.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    apply P4Bit_mod_eq.
    unfold hash4.
    rewrite Z.mod_mod by lia.
    auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_4_body) : func_specs.

Definition tbl_hash_index_4_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_hash_index_4"; "apply"] ge).

Definition tbl_hash_index_4_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_4"; "t'3"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "hash_index_4" (P4Bit index_w (hash4 key)) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_hash_index_4_body :
  func_sound ge tbl_hash_index_4_fd nil tbl_hash_index_4_spec.
Proof.
  start_function.
  table_action act_hash_index_4_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_4_body) : func_specs.

Definition act_hash_index_5_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_hash_index_5"] ge).

Definition act_hash_index_5_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_5"; "t'4"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_5" (P4Bit index_w (hash5 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_5() {
        ds_md.hash_index_5 = hash_idx_5.get(ds_key)[17:0];
    }
*)

Lemma act_hash_index_5_body :
  func_sound ge act_hash_index_5_fd nil act_hash_index_5_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bitstring_slice_lower_bit with (w' := index_w) by lia.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    apply P4Bit_mod_eq.
    unfold hash5.
    rewrite Z.mod_mod by lia.
    auto.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_5_body) : func_specs.

Definition tbl_hash_index_5_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_hash_index_5"; "apply"] ge).

Definition tbl_hash_index_5_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_hash_index_5"; "t'4"]]) []
    WITH (key : Val) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_key"], eval_val_to_sval key); (["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "hash_index_5" (P4Bit index_w (hash5 key)) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_hash_index_5_body :
  func_sound ge tbl_hash_index_5_fd nil tbl_hash_index_5_spec.
Proof.
  start_function.
  table_action act_hash_index_5_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_5_body) : func_specs.


Definition regact_clear_index_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_clear_index"])).

Definition regact_clear_index_execute_body :=
  ltac:(build_execute_body ge regact_clear_index_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_clear_index_execute_body) : func_specs.

Definition act_clear_index_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_clear_index"] ge).

Definition act_clear_index_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_clear_index"; "t'5"]]) [p ++ ["reg_clear_index"]]
    WITH (i : Z) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [fil_clear_index_repr p index_w i])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "clear_index_1" (P4Bit index_w i) ds_md)]
        (EXT [fil_clear_index_repr p index_w (update_clear_index (num_slots := num_slots) i)]))).

Lemma act_clear_index_body :
  func_sound ge act_clear_index_fd nil act_clear_index_spec.
Proof.
  start_function.
  unfold fil_clear_index_repr.
  Intros i'.
  normalize_EXT.
  Intros_prop.
  step_call regact_clear_index_execute_body.
  { entailer. }
  { reflexivity. }
  { simpl; lia. }
  { simpl. list_solve. }
  step.
  step.
  entailer.
  { apply sval_refine_refl'.
    f_equal.
    cbn [sval_to_bits_width P4Bit].
    rewrite bitstring_slice_lower_bit with (w' := index_w). 2, 3 : lia.
    apply P4Bit_mod_eq.
    pose proof (Z.mod_pos_bound i' (2 ^ Z.of_N index_w) ltac:(lia)).
    replace (i mod 2 ^ Z.of_N index_w) with i. 2 : {
      symmetry; apply Z.mod_small; lia.
    }
    auto.
  }
  { simpl.
    Exists (i' + 1).
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold update_clear_index.
    change (Z.pow_pos 2 _) with (2 ^ Z.of_N index_w).
    assert (0 <= i < num_slots) by (subst; apply Z.mod_pos_bound; reflexivity).
    rewrite Zplus_mod, H. clear H.
    destruct (i + 1 =? num_slots) eqn:?H.
    - assert (i = num_slots - 1) by lia.
      subst; auto.
    - rewrite Z.mod_small with (a := i + 1); auto.
      lia.
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_index_body) : func_specs.

Definition tbl_clear_index_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_clear_index"; "apply"] ge).

Definition tbl_clear_index_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_clear_index"; "t'5"]]) [p ++ ["reg_clear_index"]]
    WITH (i : Z) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [fil_clear_index_repr p index_w i])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "clear_index_1" (P4Bit index_w i) ds_md)]
        (EXT [fil_clear_index_repr p index_w (update_clear_index (num_slots := num_slots) i)]))))%arg_ret_assr.

Lemma tbl_clear_index_body :
  func_sound ge tbl_clear_index_fd nil tbl_clear_index_spec.
Proof.
  start_function.
  table_action act_clear_index_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_index_body) : func_specs.

Definition regact_clear_window_signal_0_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_window_signal_0"; "apply"])).

Notation update_timer := (@update_timer num_frames frame_tick_tocks).

Definition regact_clear_window_signal_0_apply_spec : func_spec :=
  RegisterAction_apply_spec' (p ++ ["regact_clear_window_signal_0"]) (fun t => 0 <= fst t < 21102) timer_repr_val
    (fun t => update_timer t false) (fun t => P4Bit 16 (fst (update_timer t false))).

(*  RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_0 = {
        void apply(inout window_pair_t val, out window_t rv) {
            if ((val.lo != 16w0))
            {
                val.hi = (val.hi + 16w1);
                val.lo = 16w0;
            }
            rv = val.hi;
        }
    };
*)

Lemma regact_clear_window_signal_0_apply_body :
  func_sound am_ge regact_clear_window_signal_0_apply_fd nil regact_clear_window_signal_0_apply_spec.
Proof.
  start_function.
  rename old_value into t.
  change (eval_val_to_sval (timer_repr_val t)) with (timer_repr_sval t).
  unfold timer_repr_sval in *.
  step.
  step.
  step.
  (* TODO fix this bug in semantics:
    why we have ["rv"] here?
    when generating uninitialized value for out parameters, the locators in these are not properly set.
  *)
  step_if (MEM [(["apply"; "val"], timer_repr_sval (update_timer t false))]
          (EXT [])).
  { unfold timer_repr_sval in *.
    step.
    step_if.
    { step.
      step.
      step.
      step.
      destruct t as [? []]; inv H.
      simpl fst in *.
      change (P4Arith.BitArith.mod_bound 16 21101) with 21101 in H0.
      replace (P4Arith.BitArith.mod_bound 16 z) with z in H0. 2 : {
        unfold P4Arith.BitArith.mod_bound.
        rewrite Z.mod_small; auto.
        change (P4Arith.BitArith.upper_bound 16) with 65536.
        lia.
      }
      unfold update_timer.
      simpl.
      destruct (z =? 21101); inv H0.
      entailer.
    }
    { step.
      step.
      step.
      step.
      destruct t as [? []]; inv H.
      simpl fst in *.
      change (P4Arith.BitArith.mod_bound 16 21101) with 21101 in H0.
      replace (P4Arith.BitArith.mod_bound 16 z) with z in H0. 2 : {
        unfold P4Arith.BitArith.mod_bound.
        rewrite Z.mod_small; auto.
        change (P4Arith.BitArith.upper_bound 16) with 65536.
        lia.
      }
      unfold update_timer.
      simpl.
      destruct (z =? 21101); inv H0.
      entailer.
    }
  }
  { unfold timer_repr_sval in *.
    step.
    step.
    step.
    step.
    destruct t as [? []]; inv H.
    entailer.
  }
  step.
  step.
  entailer.
Qed.

Definition regact_clear_window_signal_0_execute_body :=
  ltac:(build_execute_body ge regact_clear_window_signal_0_apply_body).

Definition regact_clear_window_signal_1_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_window_signal_1"; "apply"])).

Definition regact_clear_window_signal_1_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear_window_signal_1"]) timer_repr_val
    (fun t => update_timer t true) (fun t => P4Bit 16 (fst (update_timer t true))).

Lemma regact_clear_window_signal_1_apply_body :
  func_sound am_ge regact_clear_window_signal_1_apply_fd nil regact_clear_window_signal_1_apply_spec.
Proof.
  start_function.
  rename old_value into t.
  change (eval_val_to_sval (timer_repr_val t)) with (timer_repr_sval t).
  unfold timer_repr_sval in *.
  step.
  step_if (MEM [(["apply"; "val"], timer_repr_sval (update_timer t true))]
          (EXT [])).
  { step.
    step.
    step.
    destruct t as [? []]; inv H.
    entailer.
  }
  { step.
    destruct t as [? []]; inv H.
    entailer.
  }
  step.
  step.
  entailer.
Qed.

Definition regact_clear_window_signal_1_execute_body :=
  ltac:(build_execute_body ge regact_clear_window_signal_1_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_clear_window_signal_0_execute_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_clear_window_signal_1_execute_body) : func_specs.

Definition act_clear_window_signal_0_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_clear_window_signal_0"] ge).

Notation timer_repr := (@timer_repr num_frames frame_tick_tocks).

Definition act_clear_window_signal_0_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [timer_repr p t])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "clear_window" (P4Bit 16 (fst (update_timer t false))) ds_md)]
        (EXT [timer_repr p (update_timer t false)]))).

(*  action act_clear_window_signal_0() {
        ds_md.clear_window = regact_clear_window_signal_0.execute(1w0);
    }
*)

Lemma act_clear_window_signal_0_body :
  func_sound ge act_clear_window_signal_0_fd nil act_clear_window_signal_0_spec.
Proof.
  start_function.
  unfold timer_repr.
  normalize_EXT.
  Intros_prop.
  step_call regact_clear_window_signal_0_execute_body.
  { entailer. }
  { auto. }
  { lia. }
  { reflexivity. }
  { auto. }
  step.
  entailer.
  simpl ext_exclude.
  apply ext_implies_prop_intro.
  apply update_timer_wf; auto; lia.
Qed.

Definition act_clear_window_signal_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_clear_window_signal_1"] ge).

Definition act_clear_window_signal_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [timer_repr p t])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "clear_window" (P4Bit 16 (fst (update_timer t true))) ds_md)]
        (EXT [timer_repr p (update_timer t true)]))).

(*  action act_clear_window_signal_1() {
        ds_md.clear_window = regact_clear_window_signal_1.execute(1w0);
    }
*)

Lemma act_clear_window_signal_1_body :
  func_sound ge act_clear_window_signal_1_fd nil act_clear_window_signal_1_spec.
Proof.
  start_function.
  unfold timer_repr.
  normalize_EXT.
  Intros_prop.
  step_call regact_clear_window_signal_1_execute_body.
  { entailer. }
  { auto. }
  { lia. }
  { reflexivity. }
  step.
  entailer.
  apply ext_implies_prop_intro.
  apply update_timer_wf; auto; lia.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_0_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_1_body) : func_specs.

Definition tbl_clear_window_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_clear_window"; "apply"] ge).

Definition tbl_clear_window_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval) (tstamp : Z),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md); (["ingress_mac_tstamp"], P4Bit 48 tstamp)]
        (EXT [timer_repr p t])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"], update "clear_window" (P4Bit 16 (fst (update_timer t (Z.odd (tstamp / tick_time))))) ds_md)]
        (EXT [timer_repr p (update_timer t (Z.odd (tstamp / tick_time)))]))))%arg_ret_assr.

Lemma tbl_clear_window_body :
  func_sound ge tbl_clear_window_fd nil tbl_clear_window_spec.
Proof.
  start_function; elim_trivial_cases.
  { repeat rewrite Z.div_div in H by lia.
    simpl in H.
    fold tick_time in H.
    destruct (Z.odd (tstamp / tick_time)); try solve [inv H].
    table_action act_clear_window_signal_0_body.
    { entailer. }
    { entailer. }
  }
  { repeat rewrite Z.div_div in H by lia.
    simpl in H.
    fold tick_time in H.
    destruct (Z.odd (tstamp / tick_time)); try solve [inv H].
    table_action act_clear_window_signal_1_body.
    { entailer. }
    { entailer. }
  }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_window_body) : func_specs.

Definition act_set_clear_win_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_set_clear_win_1"] ge).

Definition P4_bf2_win_md_t_ :=
  ValBaseStruct
    [("api", P4Bit_ 8);
     ("index_1", P4Bit_ index_w);
     ("index_2", P4Bit_ index_w);
     ("index_3", P4Bit_ index_w);
     ("index_4", P4Bit_ index_w);
     ("index_5", P4Bit_ index_w);
     ("rw_1", P4Bit_ 32);
     ("rw_2", P4Bit_ 32);
     ("rw_3", P4Bit_ 32);
     ("rw_4", P4Bit_ 32);
     ("rw_5", P4Bit_ 32)
    ].

Definition P4_bf2_win_md_t (op : Sval) (is : list Sval) :=
  ValBaseStruct
    [("api", op);
     ("index_1", Znth 0 is);
     ("index_2", Znth 1 is);
     ("index_3", Znth 2 is);
     ("index_4", Znth 3 is);
     ("index_5", Znth 4 is);
     ("rw_1", P4Bit_ 32);
     ("rw_2", P4Bit_ 32);
     ("rw_3", P4Bit_ 32);
     ("rw_4", P4Bit_ 32);
     ("rw_5", P4Bit_ 32)
    ].

Definition act_set_clear_win_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_1"; "api_1"];
               ["act_set_clear_win_1"; "api_2"];
               ["act_set_clear_win_1"; "api_3"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3 hash_index_4 hash_index_5 : Sval) (api_1 api_2 api_3 : Sval),
      PRE
        (ARG [api_1; api_2; api_3]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("hash_index_4", hash_index_4);
                  ("hash_index_5", hash_index_5);
                  ("win_1", P4_bf2_win_md_t api_1 [clear_index_1; clear_index_1; clear_index_1; clear_index_1; clear_index_1]);
                  ("win_2", P4_bf2_win_md_t api_2 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_3", P4_bf2_win_md_t api_3 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5])])]
        (EXT []))).

Lemma act_set_clear_win_1_body :
  func_sound ge act_set_clear_win_1_fd nil act_set_clear_win_1_spec.
Proof.
  start_function.
  unfold P4_bf2_win_md_t_.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  entailer.
Qed.

Definition act_set_clear_win_2_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_set_clear_win_2"] ge).

Definition act_set_clear_win_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_2"; "api_1"];
               ["act_set_clear_win_2"; "api_2"];
               ["act_set_clear_win_2"; "api_3"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3 hash_index_4 hash_index_5 : Sval) (api_1 api_2 api_3 : Sval),
      PRE
        (ARG [api_1; api_2; api_3]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("hash_index_4", hash_index_4);
                  ("hash_index_5", hash_index_5);
                  ("win_1", P4_bf2_win_md_t api_1 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_2", P4_bf2_win_md_t api_2 [clear_index_1; clear_index_1; clear_index_1; clear_index_1; clear_index_1]);
                  ("win_3", P4_bf2_win_md_t api_3 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5])])]
        (EXT []))).

Lemma act_set_clear_win_2_body :
  func_sound ge act_set_clear_win_2_fd nil act_set_clear_win_2_spec.
Proof.
  start_function.
  unfold P4_bf2_win_md_t_.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  entailer.
Qed.

Definition act_set_clear_win_3_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_set_clear_win_3"] ge).

Definition act_set_clear_win_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_3"; "api_1"];
               ["act_set_clear_win_3"; "api_2"];
               ["act_set_clear_win_3"; "api_3"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3 hash_index_4 hash_index_5 : Sval) (api_1 api_2 api_3 : Sval),
      PRE
        (ARG [api_1; api_2; api_3]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("hash_index_4", hash_index_4);
                  ("hash_index_5", hash_index_5);
                  ("win_1", P4_bf2_win_md_t api_1 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_2", P4_bf2_win_md_t api_2 [hash_index_1; hash_index_2; hash_index_3; hash_index_4; hash_index_5]);
                  ("win_3", P4_bf2_win_md_t api_3 [clear_index_1; clear_index_1; clear_index_1; clear_index_1; clear_index_1])])]
        (EXT []))).

Lemma act_set_clear_win_3_body :
  func_sound ge act_set_clear_win_3_fd nil act_set_clear_win_3_spec.
Proof.
  start_function.
  unfold P4_bf2_win_md_t_.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_1_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_2_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_3_body) : func_specs.

Definition act_merge_wins_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_merge_wins_1"] ge).

Definition act_merge_wins_1_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) []
    WITH (ds_md : Sval) res1 res3
      (H_get_1 : get "rw_1" (get "win_1" ds_md) = res1)
      (H_get_3 : get "rw_1" (get "win_3" ds_md) = res3),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"],
          update "win_1" (
            update "rw_1" (abs_plus_sat res1 res3) (get "win_1" ds_md)
          ) ds_md)]
        (EXT []))).

Lemma act_merge_wins_1_body :
  func_sound ge act_merge_wins_1_fd nil act_merge_wins_1_spec.
Proof.
  start_function.
  step.
  rewrite H_get_1, H_get_3.
  step.
  entailer.
Qed.

Definition tbl_merge_wins_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_merge_wins_1"; "apply"] ge).

Definition tbl_merge_wins_1_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) []
    WITH (ds_md : Sval) res1 res3
      (H_get_1 : get "rw_1" (get "win_1" ds_md) = res1)
      (H_get_3 : get "rw_1" (get "win_3" ds_md) = res3),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["ds_md"],
          update "win_1" (
            update "rw_1" (abs_plus_sat res1 res3) (get "win_1" ds_md)
          ) ds_md)]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_wins_1_body :
  func_sound ge tbl_merge_wins_1_fd nil tbl_merge_wins_1_spec.
Proof.
  start_function.
  table_action act_merge_wins_1_body.
  { entailer. }
  { eauto. }
  { eauto. }
  { entailer. }
Qed.

Definition act_merge_wins_final_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "act_merge_wins_final"] ge).

Definition act_merge_wins_final_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["query_res"]]) []
    WITH (ds_md : Sval) res1 res2
      (H_get_1 : get "rw_1" (get "win_1" ds_md) = res1)
      (H_get_2 : get "rw_1" (get "win_2" ds_md) = res2),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["query_res"], abs_plus_sat res1 res2)]
        (EXT []))).

Lemma act_merge_wins_final_body :
  func_sound ge act_merge_wins_final_fd nil act_merge_wins_final_spec.
Proof.
  start_function.
  step.
  rewrite H_get_1, H_get_2.
  step.
  entailer.
Qed.

Definition tbl_merge_wins_final_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_merge_wins_final"; "apply"] ge).

Definition tbl_set_win_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "tbl_set_win"; "apply"] ge).

Notation get_clear_frame := (get_clear_frame frame_tick_tocks).
Notation get_insert_frame := (get_insert_frame num_frames).

Lemma Z_div_squeeze_pos : forall a b lo hi res,
  0 < b ->
  lo <= a <= hi ->
  lo / b = res ->
  hi / b = res ->
  a / b = res.
Proof.
  intros.
  pose proof (Z.div_le_mono lo a b ltac:(auto) ltac:(lia)).
  pose proof (Z.div_le_mono a hi b ltac:(auto) ltac:(lia)).
  lia.
Qed.

Lemma Z_div_squeeze : forall a b lo hi res,
  lo <= a <= hi ->
  lo / b = res ->
  hi / b = res ->
  a / b = res.
Proof.
  intros.
  destruct b.
  - rewrite Zdiv_0_r in *. auto.
  - eapply Z_div_squeeze_pos; eauto; lia.
  - rewrite <- Zdiv_opp_opp in *.
    eapply Z_div_squeeze_pos with (-hi) (-lo); lia.
Qed.

Lemma Z_div_squeeze' : forall a b lo hi res,
  (lo <=? a) && (a <=? hi) ->
  lo / b = res ->
  hi / b = res ->
  a / b = res.
Proof.
  intros.
  apply Z_div_squeeze with lo hi; lia.
Qed.

Definition Filter_fd :=
  ltac:(get_fd ["Cm2CountMinSketch"; "apply"] ge).

Program Definition hashes (key : Val) : listn Z num_rows := (exist _ [hash1 key; hash2 key; hash3 key; hash4 key; hash5 key] eq_refl).

Notation cms_repr := (cms_repr (frame_tick_tocks := frame_tick_tocks)).
