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
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "bf2_ds"].

Definition act_hash_index_1_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_hash_index_1"] ge).

Definition hash1 (v : Val) :=
  hash_Z 32
    {|
      Tofino.CRCP_width := 32;
      Tofino.CRCP_coeff := P4Arith.to_lbool 32 79764919;
      Tofino.CRCP_reversed := true;
      Tofino.CRCP_msb := false;
      Tofino.CRCP_extended := false;
      Tofino.CRCP_init := P4Arith.to_lbool 32 0;
      Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
    |}
    v.

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
        (MEM [(["ds_md"], update "hash_index_1" (P4Bit 18 (hash1 key)) ds_md)]
        (EXT []))).

(*  action act_hash_index_1() {
        ds_md.hash_index_1 = hash_idx_1.get(ds_key)[17:0];
    }
*)

Lemma sval_refine_refl' : forall sv sv',
  sv = sv' ->
  sval_refine sv sv'.
Proof.
  intros; subst; apply sval_refine_refl.
Qed.

(* Need a better name. *)
Lemma bit_bitstring_slice : forall (w w' : N) v,
  (w' > 0)%N ->
  ValBaseBit (Ops.bitstring_slice (P4Arith.to_loptbool w v) (N.to_nat 0) (N.to_nat (w' - 1)))
    = P4Bit w' v.
Proof.
  intros.
Admitted.

Lemma P4Bit_trunc : forall w v v',
  v mod 2 ^ Z.of_N w = v' mod 2 ^ Z.of_N w ->
  P4Bit w v = P4Bit w v'.
Proof.
Admitted.

Lemma act_hash_index_1_body :
  func_sound ge act_hash_index_1_fd nil act_hash_index_1_spec.
Proof.
  start_function.
  step_call @Hash_get_body.
  { entailer. }
  { compute. reflexivity. }
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bit_bitstring_slice with (w' := 18%N) by lia.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_hash_index_1_body) : func_specs.

Definition tbl_hash_index_1_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_hash_index_1"; "apply"] ge).

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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_1" (P4Bit 18 (hash1 key)) ds_md)]
        (EXT []))).

Lemma tbl_hash_index_1_body :
  func_sound ge tbl_hash_index_1_fd nil tbl_hash_index_1_spec.
Proof.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_1_body) : func_specs.

Definition act_hash_index_2_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_hash_index_2"] ge).

Definition hash2 (v : Val) :=
  hash_Z 32
    {|
      Tofino.CRCP_width := 32;
      Tofino.CRCP_coeff := P4Arith.to_lbool 32 517762881;
      Tofino.CRCP_reversed := true;
      Tofino.CRCP_msb := false;
      Tofino.CRCP_extended := false;
      Tofino.CRCP_init := P4Arith.to_lbool 32 0;
      Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
    |}
    v.

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
        (MEM [(["ds_md"], update "hash_index_2" (P4Bit 18 (hash2 key)) ds_md)]
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
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bit_bitstring_slice with (w' := 18%N) by lia.
  entailer.
Qed.

Definition tbl_hash_index_2_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_hash_index_2"; "apply"] ge).

Lemma tbl_hash_index_2_body :
  func_sound ge tbl_hash_index_2_fd nil act_hash_index_2_spec.
Proof.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_2_body) : func_specs.

Definition act_hash_index_3_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_hash_index_3"] ge).

Definition hash3 (v : Val) :=
  hash_Z 32
    {|
      Tofino.CRCP_width := 32;
      Tofino.CRCP_coeff := P4Arith.to_lbool 32 2821953579;
      Tofino.CRCP_reversed := true;
      Tofino.CRCP_msb := false;
      Tofino.CRCP_extended := false;
      Tofino.CRCP_init := P4Arith.to_lbool 32 0;
      Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
    |}
    v.

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
        (MEM [(["ds_md"], update "hash_index_3" (P4Bit 18 (hash3 key)) ds_md)]
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
  step.
  step.
  simpl sval_to_bits_width.
  cbv match.
  rewrite bit_bitstring_slice with (w' := 18%N) by lia.
  entailer.
Qed.

Definition tbl_hash_index_3_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_hash_index_3"; "apply"] ge).

Lemma tbl_hash_index_3_body :
  func_sound ge tbl_hash_index_3_fd nil act_hash_index_3_spec.
Proof.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_hash_index_3_body) : func_specs.

Definition regact_clear_index_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_index"; "apply"]) ge).

Definition regact_clear_index_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear_index"]) (fun i => ValBaseBit (P4Arith.to_lbool 32 i))
    (fun i => i + 1) (fun i => P4Bit 32 i).

Lemma regact_clear_index_apply_body :
  func_sound am_ge regact_clear_index_apply_fd nil regact_clear_index_apply_spec.
Proof.
  start_function.
  step.
  step.
  step.
  step.
  entailer.
  { red.
    change (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 32 old_value)))
      with (P4Bit 32 old_value).
    rewrite abs_plus_bit.
    apply sval_refine_refl.
  }
Qed.

Definition regact_clear_index_execute_body :=
  ltac:(build_execute_body ge regact_clear_index_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_clear_index_execute_body) : func_specs.

Definition act_clear_index_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_clear_index"] ge).

Definition act_clear_index_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]; ["act_clear_index"; "t'3"]]) [p ++ ["reg_clear_index"]]
    WITH (i : Z) (ds_md : Sval),
      PRE
        (ARG []
        (MEM [(["ds_md"], ds_md)]
        (EXT [fil_clear_index_repr p 18 i])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "clear_index_1" (P4Bit 18 i) ds_md)]
        (EXT [fil_clear_index_repr p 18 (update_clear_index (num_slots := num_slots) i)]))).

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
    rewrite bit_bitstring_slice with (w' := 18%N). 2 : { lia. }
    apply P4Bit_trunc.
    pose proof (Z.mod_pos_bound i' (2 ^ Z.of_N 18) ltac:(lia)).
    replace (i mod 2 ^ Z.of_N 18) with i. 2 : {
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
    change (Z.pow_pos 2 18) with (2 ^ Z.of_N 18).
    assert (0 <= i < num_slots) by (subst; apply Z.mod_pos_bound; reflexivity).
    rewrite Zplus_mod, H. clear H.
    destruct (i + 1 =? num_slots) eqn:?H.
    - assert (i = num_slots - 1) by lia.
      subst; auto.
    - rewrite Z.mod_small with (a := i + 1); auto.
      lia.
  }
Qed.

Definition tbl_clear_index_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_clear_index"; "apply"] ge).

Lemma tbl_clear_index_body :
  func_sound ge tbl_clear_index_fd nil act_clear_index_spec.
Proof.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_clear_index_body) : func_specs.

Definition regact_clear_window_signal_0_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_window_signal_0"; "apply"]) ge).

Notation update_timer := (@update_timer num_frames frame_tick_tocks).

Definition regact_clear_window_signal_0_apply_spec : func_spec :=
  RegisterAction_apply_spec (p ++ ["regact_clear_window_signal_0"]) timer_repr_val
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
  (* TODO fix this bug in semantics:
    why we have ["rv"] here?
    when generating uninitialized value for out parameters, the locators in these are not properly set.
  *)
  step_if (MEM [(["apply"; "val"], timer_repr_sval (update_timer t false))]
           (EXT [])).
  { unfold timer_repr_sval in *.
    step.
    step.
    step.
    step.
    destruct t as [? []]; inv H.
    entailer.
  }
  { unfold timer_repr_sval in *.
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
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_window_signal_1"; "apply"]) ge).

Definition regact_clear_window_signal_1_apply_spec : func_spec :=
  RegisterAction_apply_spec' (p ++ ["regact_clear_window_signal_1"]) (fun t => 0 <= fst t <= 28136) timer_repr_val
    (fun t => update_timer t true) (fun t => P4Bit 16 (fst (update_timer t true))).

(*  RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_1 = {
        void apply(inout window_pair_t val, out window_t rv) {
            if ((val.hi == 16w28136))
            {
                val.hi = 16w0;
            }
            if ((val.lo != 16w1))
            {
                val.lo = 16w1;
            }
            rv = val.hi;
        }
    };
*)

Lemma regact_clear_window_signal_1_apply_body :
  func_sound am_ge regact_clear_window_signal_1_apply_fd nil regact_clear_window_signal_1_apply_spec.
Proof.
  start_function.
  rename old_value into t.
  change (eval_val_to_sval (timer_repr_val t)) with (timer_repr_sval t).
  unfold timer_repr_sval in *.
  step.
  step_if (MEM [(["apply"; "val"], ValBaseStruct [("hi", P4Bit 16 (if (fst t =? 28136) then 0 else fst t));
                                                  ("lo", P4Bit 16 (Z.b2z (snd t)))])]
           (EXT [])).
  { step.
    step.
    step.
    change (P4Arith.BitArith.mod_bound 16 28136) with 28136 in H.
    replace (P4Arith.BitArith.mod_bound 16 (fst t)) with (fst t) in H. 2 : {
      unfold P4Arith.BitArith.mod_bound.
      rewrite Z.mod_small; auto.
      change (P4Arith.BitArith.upper_bound 16) with 65536.
      lia.
    }
    destruct (fst t =? 28136); inv H.
    entailer.
  }
  { step.
    change (P4Arith.BitArith.mod_bound 16 28136) with 28136 in H.
    replace (P4Arith.BitArith.mod_bound 16 (fst t)) with (fst t) in H. 2 : {
      unfold P4Arith.BitArith.mod_bound.
      rewrite Z.mod_small; auto.
      change (P4Arith.BitArith.upper_bound 16) with 65536.
      lia.
    }
    destruct (fst t =? 28136); inv H.
    entailer.
  }
  step_if (MEM [(["apply"; "val"], (timer_repr_sval (update_timer t true)))]
           (EXT [])).
  { unfold timer_repr_sval in *.
    step.
    step.
    step.
    destruct t as [? []]; inv H.
    simpl.
    destruct (z =? 28136);
      entailer.
  }
  { unfold timer_repr_sval in *.
    step.
    destruct t as [? []]; inv H.
    simpl.
    destruct (z =? 28136);
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
  ltac:(get_fd ["Bf2BloomFilter"; "act_clear_window_signal_0"] ge).

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
  step.
  entailer.
  simpl ext_exclude.
  apply ext_implies_prop_intro.
  apply update_timer_wf; auto; lia.
Qed.

Definition act_clear_window_signal_1_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_clear_window_signal_1"] ge).

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
  { unfold timer_wf in H.
    destruct (snd t); lia.
  }
  step.
  entailer.
  apply ext_implies_prop_intro.
  apply update_timer_wf; auto; lia.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_0_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_1_body) : func_specs.

Definition tbl_clear_window_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_clear_window"; "apply"] ge).

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
        (MEM [(["ds_md"], update "clear_window" (P4Bit 16 (fst (update_timer t (Z.odd (tstamp / 2097152))))) ds_md)]
        (EXT [timer_repr p (update_timer t (Z.odd (tstamp / 2097152)))]))))%arg_ret_assr.

(*  table tbl_clear_window {
        key = {
            ingress_mac_tstamp : ternary;
        }
        actions = {
            act_clear_window_signal_0();
            act_clear_window_signal_1();
        }
        const entries = {
            48w0 &&& 48w2097152 : act_clear_window_signal_0();
            _ : act_clear_window_signal_1();
        }
        default_action = act_clear_window_signal_1();
        size = 2;
    }
*)

Ltac next_case' :=
  constructor; (let H := fresh in intro H).

Lemma tbl_clear_window_body :
  func_sound ge tbl_clear_window_fd nil tbl_clear_window_spec.
Proof.
  start_function.
  next_case'.
  { simpl in H.
    replace (Z.odd (tstamp / 2097152)) with false by admit.
    table_action act_clear_window_signal_0_body.
    { entailer. }
    { entailer. }
  }
  next_case'.
  { simpl in H0.
    replace (Z.odd (tstamp / 2097152)) with true by admit.
    table_action act_clear_window_signal_1_body.
    { entailer. }
    { entailer. }
  }
  (* This case should be impossible. *)
  admit.
Admitted.

Definition act_set_clear_win_1_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_set_clear_win_1"] ge).

(* Definition act_set_clear_win_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_1"; "api_1"];
               ["act_set_clear_win_1"; "api_2"];
               ["act_set_clear_win_1"; "api_3"];
               ["act_set_clear_win_1"; "api_4"]]) []
    WITH (ds_md : Sval) (api_1 api_2 api_3 api_4 : Sval),
      PRE
        (ARG [api_1; api_2; api_3; api_4]
        (MEM [(["ds_md"], ds_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [
          (["ds_md"], update "win_1" (
            update "index_1" (get "clear_index_1" ds_md)
            (update "index_2" (get "clear_index_1" ds_md)
            (update "index_3" (get "clear_index_1" ds_md) (get "win_1" ds_md))))
            ds_md)]
        (EXT []))).

Lemma act_set_clear_win_1_body :
  func_sound ge act_set_clear_win_1_fd nil act_set_clear_win_1_spec.
Proof.
  start_function.
  assert (has_field "win_1" ds_md) by admit.
  assert (has_field "win_2" ds_md) by admit.
  assert (has_field "win_3" ds_md) by admit.
  assert (has_field "win_4" ds_md) by admit.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.

Ltac rewrite_get_update_same :=
  rewrite get_update_same by (auto using has_field_update).

Ltac rewrite_get_update_diff :=
  rewrite get_update_diff; [ | auto using has_field_update | discriminate].

Ltac rewrite_update_update_same :=
  rewrite update_update_same by (auto using has_field_update).

Ltac get_update_simpl :=
  repeat first [
    rewrite_get_update_same
  | rewrite_get_update_diff
  | rewrite_update_update_same
  ].

  get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  Time step.
  Time simpl; get_update_simpl.
  (* Then we need a update_update_diff rule and guide it nicely. *)
Abort. *)

Definition P4New_bf2_win_md_t :=
  ValBaseStruct
    [("api", P4NewBit 8);
     ("index_1", P4NewBit 18);
     ("index_2", P4NewBit 18);
     ("index_3", P4NewBit 18);
     ("rw_1", P4NewBit 8);
     ("rw_2", P4NewBit 8);
     ("rw_3", P4NewBit 8)].

Definition P4_bf2_win_md_t (op : Sval) (is : list Sval) :=
  ValBaseStruct
    [("api", op);
     ("index_1", Znth 0 is);
     ("index_2", Znth 1 is);
     ("index_3", Znth 2 is);
     ("rw_1", P4NewBit 8);
     ("rw_2", P4NewBit 8);
     ("rw_3", P4NewBit 8)].

Definition act_set_clear_win_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_1"; "api_1"];
               ["act_set_clear_win_1"; "api_2"];
               ["act_set_clear_win_1"; "api_3"];
               ["act_set_clear_win_1"; "api_4"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3: Sval) (api_1 api_2 api_3 api_4 : Sval),
      PRE
        (ARG [api_1; api_2; api_3; api_4]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4New_bf2_win_md_t);
                  ("win_2", P4New_bf2_win_md_t);
                  ("win_3", P4New_bf2_win_md_t);
                  ("win_4", P4New_bf2_win_md_t)])]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t api_1 [clear_index_1; clear_index_1; clear_index_1]);
                  ("win_2", P4_bf2_win_md_t api_2 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_3", P4_bf2_win_md_t api_3 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_4", P4_bf2_win_md_t api_4 [hash_index_1; hash_index_2; hash_index_3])])]
        (EXT []))).

Lemma act_set_clear_win_1_body :
  func_sound ge act_set_clear_win_1_fd nil act_set_clear_win_1_spec.
Proof.
  start_function.
  unfold P4New_bf2_win_md_t.
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
  ltac:(get_fd ["Bf2BloomFilter"; "act_set_clear_win_2"] ge).

Definition act_set_clear_win_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_2"; "api_1"];
               ["act_set_clear_win_2"; "api_2"];
               ["act_set_clear_win_2"; "api_3"];
               ["act_set_clear_win_2"; "api_4"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3: Sval) (api_1 api_2 api_3 api_4 : Sval),
      PRE
        (ARG [api_1; api_2; api_3; api_4]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4New_bf2_win_md_t);
                  ("win_2", P4New_bf2_win_md_t);
                  ("win_3", P4New_bf2_win_md_t);
                  ("win_4", P4New_bf2_win_md_t)])]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t api_1 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_2", P4_bf2_win_md_t api_2 [clear_index_1; clear_index_1; clear_index_1]);
                  ("win_3", P4_bf2_win_md_t api_3 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_4", P4_bf2_win_md_t api_4 [hash_index_1; hash_index_2; hash_index_3])])]
        (EXT []))).

Lemma act_set_clear_win_2_body :
  func_sound ge act_set_clear_win_2_fd nil act_set_clear_win_2_spec.
Proof.
  start_function.
  unfold P4New_bf2_win_md_t.
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
  ltac:(get_fd ["Bf2BloomFilter"; "act_set_clear_win_3"] ge).

Definition act_set_clear_win_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_3"; "api_1"];
               ["act_set_clear_win_3"; "api_2"];
               ["act_set_clear_win_3"; "api_3"];
               ["act_set_clear_win_3"; "api_4"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3: Sval) (api_1 api_2 api_3 api_4 : Sval),
      PRE
        (ARG [api_1; api_2; api_3; api_4]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4New_bf2_win_md_t);
                  ("win_2", P4New_bf2_win_md_t);
                  ("win_3", P4New_bf2_win_md_t);
                  ("win_4", P4New_bf2_win_md_t)])]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t api_1 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_2", P4_bf2_win_md_t api_2 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_3", P4_bf2_win_md_t api_3 [clear_index_1; clear_index_1; clear_index_1]);
                  ("win_4", P4_bf2_win_md_t api_4 [hash_index_1; hash_index_2; hash_index_3])])]
        (EXT []))).

Lemma act_set_clear_win_3_body :
  func_sound ge act_set_clear_win_3_fd nil act_set_clear_win_3_spec.
Proof.
  start_function.
  unfold P4New_bf2_win_md_t.
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

Definition act_set_clear_win_4_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_set_clear_win_4"] ge).

Definition act_set_clear_win_4_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"];
               ["act_set_clear_win_4"; "api_1"];
               ["act_set_clear_win_4"; "api_2"];
               ["act_set_clear_win_4"; "api_3"];
               ["act_set_clear_win_4"; "api_4"]]) []
    WITH (clear_window clear_index_1 hash_index_1 hash_index_2 hash_index_3: Sval) (api_1 api_2 api_3 api_4 : Sval),
      PRE
        (ARG [api_1; api_2; api_3; api_4]
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4New_bf2_win_md_t);
                  ("win_2", P4New_bf2_win_md_t);
                  ("win_3", P4New_bf2_win_md_t);
                  ("win_4", P4New_bf2_win_md_t)])]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], ValBaseStruct
                 [("clear_window", clear_window);
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4_bf2_win_md_t api_1 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_2", P4_bf2_win_md_t api_2 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_3", P4_bf2_win_md_t api_3 [hash_index_1; hash_index_2; hash_index_3]);
                  ("win_4", P4_bf2_win_md_t api_4 [clear_index_1; clear_index_1; clear_index_1])])]
        (EXT []))).

Lemma act_set_clear_win_4_body :
  func_sound ge act_set_clear_win_4_fd nil act_set_clear_win_4_spec.
Proof.
  start_function.
  unfold P4New_bf2_win_md_t.
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
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_set_clear_win_4_body) : func_specs.

Definition tbl_set_win_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_set_win"; "apply"] ge).

Definition P4_bf2_win_md_t_insert (f cf if' : Z) (new_clear_index : Sval) (is : list Sval) :=
  if f=? cf then
    P4_bf2_win_md_t (P4Bit 8 CLEAR) [new_clear_index; new_clear_index; new_clear_index]
  else if f=? if' then
    P4_bf2_win_md_t (P4Bit 8 INSERT) is
  else
    P4_bf2_win_md_t (P4Bit 8 NOOP) is.

Notation get_clear_frame := (get_clear_frame num_frames frame_tick_tocks).
Notation get_insert_frame := (get_insert_frame num_frames).

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
      (api: Z)
      (H_timer : 0 <= fst timer <= frame_tick_tocks * num_frames)
      (H_api : 0 <= api <= 255),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 api);
              (["ds_md"], ValBaseStruct
                 [("clear_window", P4Bit 16 (fst timer));
                  ("clear_index_1", clear_index_1);
                  ("hash_index_1", hash_index_1);
                  ("hash_index_2", hash_index_2);
                  ("hash_index_3", hash_index_3);
                  ("win_1", P4New_bf2_win_md_t);
                  ("win_2", P4New_bf2_win_md_t);
                  ("win_3", P4New_bf2_win_md_t);
                  ("win_4", P4New_bf2_win_md_t)])]
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

(* We need to turn set a larger searching steps, because the number of modified local variables
  is too big. *)
Ltac solve_modifies ::=
  first
  [ solve
  [ eauto  300 with nocore modifies ]
  | idtac
  "The modifies clause cannot be solved automatically." ].

(* Ltac hoare_func_table ::=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_list_intro'; (* hoare_table_match_list *)
        [ reflexivity (* eval_exprs *)
        | (* simplify_lift_option_eval_sval_to_val; (* lift_option (.. keysvals) *)
          reflexivity *)
        | (* eapply hoare_table_entries_intros; (* hoare_table_entries *)
          repeat econstructor *)
        | (* hoare_extern_match_list *) (* hoare_extern_match_list *)
        ]
      | idtac (* hoare_table_action_cases' *)
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end. *)

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

Lemma reduce_match_range: forall w x lo hi x' lo' hi' xb lob hib,
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int lo = Some (w, lo', lob) ->
  Tofino.assert_int hi = Some (w, hi', hib) ->
  Tofino.values_match_range x lo hi = (lo' <=? x') && (x' <=? hi').
Proof.
  intros.
  unfold Tofino.values_match_range.
  rewrite H, H0, H1. rewrite N.eqb_refl. simpl.
  reflexivity.
Qed.

Lemma reduce_match_singleton: forall w x y x' y' xb yb,
  val_sim x y ->
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int y = Some (w, y', yb) ->
  Tofino.values_match_singleton x y = (x' =? y').
Proof.
  intros. revert y H H1.
  induction x;
  induction y; intros;
  simpl in H0; simpl in H1; unfold val_sim in H; try discriminate; try inv H.
  { unfold Tofino.values_match_singleton, Ops.eval_binary_op_eq.
    remember (P4Arith.BitArith.from_lbool value0) as n0_name. inv H1.
    remember (P4Arith.BitArith.from_lbool value) as n_name. inv H0.
    rewrite N.eqb_refl. trivial. }
  { unfold Tofino.values_match_singleton, Ops.eval_binary_op_eq.
    remember (P4Arith.IntArith.from_lbool value0) as z0_name. inv H1.
    remember (P4Arith.IntArith.from_lbool value) as z_name. inv H0.
    rewrite N.eqb_refl. trivial. }
  unfold Tofino.values_match_singleton in IHx |- *. simpl in IHx |- *. rewrite String.eqb_refl.
  eapply IHx; assumption.
(*   assert (Tofino.values_match_singleton
    (ValBaseSenumField typ_name0 x) (ValBaseSenumField typ_name0 y)
    = Tofino.values_match_singleton x y).
  { unfold Tofino.values_match_singleton. simpl. rewrite String.eqb_refl. trivial. }
  { rewrite H. eapply IHx; assumption. } *)
Qed.

Lemma assert_int_len : forall x w x' xb,
  Tofino.assert_int x = Some (w, x', xb) -> Z.to_N (Zlength xb) = w.
Proof.
  induction x; intros; simpl in H; try discriminate.
  - unfold P4Arith.BitArith.from_lbool in H; inv H; trivial.
  - unfold P4Arith.IntArith.from_lbool in H; inv H; trivial.
  - eapply IHx; eauto.
Qed.

(*
Lemma assert_int_div_2 : forall x w x' hd tl,
  Tofino.assert_int x = Some (w, x', hd :: tl) ->
  hd <> true \/ tl <> [] ->
  exists y,
  Tofino.assert_int y = Some ((w - 1)%N, x' / 2, tl).
Proof.
  induction x; intros; simpl in H; try discriminate.
  - exists (ValBaseBit tl). simpl. unfold P4Arith.BitArith.from_lbool in *.
    inv H. f_equal. f_equal. f_equal.
    + list_solve.
    + simpl.
      rewrite (P4Arith.BitArith.lbool_to_val_1_0 tl 2 1).
      rewrite (P4Arith.BitArith.lbool_to_val_1_0 tl 2 0).
      destruct hd; rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia.
  - exists (ValBaseInt tl). simpl. unfold P4Arith.IntArith.from_lbool in *.
    inv H. f_equal. f_equal. f_equal.
    + list_solve.
    +  simpl. rewrite (P4Arith.IntArith.lbool_to_val_1_0 tl 2 1).
      rewrite (P4Arith.IntArith.lbool_to_val_1_0 tl 2 0). simpl.
      destruct hd, tl.
      2, 4: rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; lia.
      1: destruct H0; exfalso; now apply H.
      simpl; compute; easy.
  - eapply IHx; eauto.
Qed.


Lemma z_odd_bool : forall x w x' hd tl,
   Tofino.assert_int x = Some (w, x', hd :: tl) ->
   hd = Z.odd x'.
Proof.
  induction x; intros; simpl in H; try discriminate.
  - unfold P4Arith.BitArith.from_lbool in H.
    inv H. simpl. destruct hd.
    + rewrite (P4Arith.BitArith.lbool_to_val_1_0 tl 2 1).
      replace (P4Arith.BitArith.lbool_to_val tl 1 0 * 2 + 1) with
      (1 + 2 * P4Arith.BitArith.lbool_to_val tl 1 0 ) by lia.
      now rewrite Z.odd_add_mul_2.
    + rewrite (P4Arith.BitArith.lbool_to_val_1_0 tl 2 0).
      replace (P4Arith.BitArith.lbool_to_val tl 1 0 * 2 + 0) with
      (0 + 2 * P4Arith.BitArith.lbool_to_val tl 1 0 ) by lia.
      now rewrite Z.odd_add_mul_2.
  - unfold P4Arith.IntArith.from_lbool in H.
    inv H. simpl. destruct hd, tl.
    1, 3: easy.
    + rewrite (P4Arith.IntArith.lbool_to_val_1_0 (b :: tl) 2 1).
      replace (P4Arith.IntArith.lbool_to_val (b :: tl) 1 0 * 2 + 1) with
      (1 + 2 * P4Arith.IntArith.lbool_to_val (b :: tl) 1 0 ) by lia.
      now rewrite Z.odd_add_mul_2.
    + rewrite (P4Arith.IntArith.lbool_to_val_1_0 (b :: tl) 2 0).
      replace (P4Arith.IntArith.lbool_to_val (b :: tl) 1 0 * 2 + 0) with
      (0 + 2 * P4Arith.IntArith.lbool_to_val (b :: tl) 1 0 ) by lia.
      now rewrite Z.odd_add_mul_2.
  - eapply IHx; eauto.
Qed. *)

Lemma vmm_help_eq : forall xb vb mb w x',
  Z.to_N (Zlength vb) = w ->
  Z.to_N (Zlength mb) = w ->
  P4Arith.to_lbool w x' = xb ->
  Tofino.vmm_help xb vb mb = Tofino.vmm_help_z x' vb mb.
Proof.
  intros.
  pose proof (P4Arith.Zlength_to_lbool w x').
  rewrite H1 in H2.
  revert vb mb w x' H H0 H1 H2.
  induction xb;
  destruct vb;
  destruct mb; intros;
  try (unfold Tofino.vmm_help_z; easy);
  try list_solve.
  assert (a = Z.odd x' /\ xb = P4Arith.to_lbool (w - 1) (x' / 2)).
  { unfold P4Arith.to_lbool in H1 |- *.
    rewrite <- to_lbool''_to_lbool' in H1 |- *.
    replace (N.to_nat w) with (S (N.to_nat (w - 1))) in H1.
    2 : { assert (w > 0)%N by list_solve. lia. }
    (* lia seems more powerful than I thought *)
    simpl in H1. split; congruence.
    (* injection; prove eq of uninterpreted function by a sequence of rewrite *)
  }
  destruct H3.
  destruct b0; simpl.
  - subst a.
    destruct (Bool.eqb (Z.odd x') b).
    { eapply IHxb with (w := (w - 1)%N); list_solve. }
    { auto. } (* exact eq_refl *)
  - eapply IHxb with (w := (w - 1)%N); list_solve.
Qed.

Lemma to_lbool''_to_lbool : forall (width : N) (value : Z),
  to_lbool'' (N.to_nat width) value = P4Arith.to_lbool width value.
Proof.
  intros.
  apply to_lbool''_to_lbool'.
Qed.

Lemma bit_to_from_bool : forall bl,
  P4Arith.to_lbool (fst (P4Arith.BitArith.from_lbool bl)) (snd (P4Arith.BitArith.from_lbool bl)) = bl.
Proof.
  intros.
  rewrite <- to_lbool''_to_lbool.
  induction bl; auto.
  simpl.
  replace (N.to_nat (Z.to_N (Zlength (a :: bl)))) with (S (N.to_nat (Z.to_N (Zlength bl)))) by list_solve.
  simpl to_lbool''.
  destruct a; rewrite P4Arith.BitArith.lbool_to_val_1_0.
  - f_equal.
    { replace (P4Arith.BitArith.lbool_to_val bl 1 0 * 2 + 1) with
        (1 + 2 * P4Arith.BitArith.lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    rewrite Z.div_add_l by lia.
    replace (1 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
  - f_equal.
    { replace (P4Arith.BitArith.lbool_to_val bl 1 0 * 2 + 0) with
        (0 + 2 * P4Arith.BitArith.lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    rewrite Z.div_add_l by lia.
    replace (0 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
Qed.

Lemma int_to_from_bool : forall bl,
  P4Arith.to_lbool (fst (P4Arith.IntArith.from_lbool bl)) (snd (P4Arith.IntArith.from_lbool bl)) = bl.
Proof.
  intros.
  rewrite <- to_lbool''_to_lbool.
  induction bl; auto.
  simpl.
  replace (N.to_nat (Z.to_N (Zlength (a :: bl)))) with (S (N.to_nat (Z.to_N (Zlength bl)))) by list_solve.
  simpl to_lbool''.
  destruct a; rewrite P4Arith.IntArith.lbool_to_val_1_0.
  - f_equal.
    { destruct bl as [ | b bl']; auto.
      set (bl := b :: bl') in *.
      replace (P4Arith.IntArith.lbool_to_val bl 1 0 * 2 + 1) with
        (1 + 2 * P4Arith.IntArith.lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    destruct bl as [ | b bl']; auto.
    set (bl := b :: bl') in *.
    rewrite Z.div_add_l by lia.
    replace (1 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
  - f_equal.
    { destruct bl as [ | b bl']; auto.
      set (bl := b :: bl') in *.
      replace (P4Arith.IntArith.lbool_to_val bl 1 0 * 2 + 0) with
        (0 + 2 * P4Arith.IntArith.lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    destruct bl as [ | b bl']; auto.
    set (bl := b :: bl') in *.
    rewrite Z.div_add_l by lia.
    replace (0 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
Qed.

Lemma assert_int_conv : forall w x x' xb,
  Tofino.assert_int x = Some (w, x', xb) ->
  P4Arith.to_lbool w x' = xb.
Proof.
  induction x; intros; simpl in H; try discriminate; inv H.
  - apply bit_to_from_bool.
  - apply int_to_from_bool.
  - auto.
Qed.

(* Fixpoint vmm_help_z' (v : Z) (bits1 bits2: list bool) :=
  match bits2, bits1 with
  | [], [] => true
  | false::tl2, _::tl1 => vmm_help_z' (v / 2) tl1 tl2
  | true::tl2, hd1::tl1 =>
      andb (Bool.eqb (Z.odd v) hd1) (vmm_help_z' (v / 2) tl1 tl2)
  | _, _ => Tofino.dummy_bool
  end.
Goal vmm_help_z' = Tofino.vmm_help_z.
Proof. reflexivity.
 *)

(* Lemma vmm_help_eq : forall xb vb mb x w x',
  Z.to_N (Zlength vb) = w ->
  Z.to_N (Zlength mb) = w ->
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.vmm_help xb vb mb = Tofino.vmm_help_z x' vb mb.
Proof.
  induction xb;
  destruct vb;
  destruct mb; intros;
  try (unfold Tofino.vmm_help_z; easy);
  try (apply assert_int_len in H1; list_solve).
  assert (Tofino.vmm_help xb vb mb = Tofino.vmm_help_z (x' / 2) vb mb).
  {
    destruct a, xb;
    try (
      apply assert_int_len in H1;
      assert (mb = []) by list_solve;
      assert (vb = []) by list_solve; subst mb; subst vb; simpl;
      easy).
    destruct (assert_int_div_2 _ _ _ _ _ H1). right. intros S. inv S.
    eapply IHxb.
    instantiate (1 := (w - 1)%N).
    { list_solve. }
    { list_solve. }
    { eauto. }
    destruct (assert_int_div_2 _ _ _ _ _ H1). right. intros S. inv S.
    eapply IHxb.
    instantiate (1 := (w - 1)%N).
    { list_solve. }
    { list_solve. }
    { eauto. }
  }
  destruct b0; simpl; auto.
  erewrite <- z_odd_bool; eauto.
  destruct (Bool.eqb a b) eqn: ?H; auto.
Qed. *)

(* Lemma reduce_match_mask: forall w x v m x' v' m' xb vb mb ,
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int v = Some (w, v', vb) ->
  Tofino.assert_int m = Some (w, m', mb) ->
  Tofino.values_match_mask x v m = Tofino.vmm_help_z x' vb mb.
Proof.
  intros.
  unfold Tofino.values_match_mask; rewrite H, H0, H1; rewrite N.eqb_refl; simpl.
  apply assert_int_conv in H.
  apply assert_int_len in H0, H1.
  eapply vmm_help_eq; eauto.
Qed. *)

Lemma reduce_match_mask: forall w x v m x' v' m' xb vb mb,
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int v = Some (w, v', vb) ->
  Tofino.assert_int m = Some (w, m', mb) ->
  Tofino.values_match_mask x v m = Tofino.vmm_help xb vb mb.
Proof.
  intros.
  unfold Tofino.values_match_mask; rewrite H, H0, H1; rewrite N.eqb_refl; simpl.
  auto.
Qed.

(*
  rewrite <- !Z.leb_le.
  rewrite Reflect.andE.
  tauto.
*)

Lemma tbl_set_win_insert_body :
  func_sound ge tbl_set_win_fd nil tbl_set_win_insert_spec.
Proof.
Ltac Tactics.hoare_func_table ::=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
       eapply hoare_func_table';
       [ eapply hoare_table_match_list_intro';
          [ reflexivity
          | simplify_lift_option_eval_sval_to_val; reflexivity
          | eapply hoare_table_entries_intros;
            repeat first [
              simple apply sval_to_val_eval_p4int_sval
            | econstructor
            ]
          | hoare_extern_match_list ]
       |  ]
  | _ =>
      fail
       "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end.

  start_function.

(*   econstructor. econstructor. econstructor. econstructor. econstructor. econstructor. econstructor.
  apply sval_to_val_eval_p4int_sval. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor.
 *)
(* Ltac foo := lazymatch goal with  | |- ?x = ?y =>      unify x y  end. *)

(*   repeat match goal with
  | |- context [ValSetProd ?l] =>
      let l' := eval compute in l in
      progress change l with l'
  end. *)
  simpl Tofino.extern_matches.
  (* quadratic time Time (tactic ; tactic) *)
(* quadratic time Time (tactic ; tactic) *)


(* To be expanded *)
(* test examples:
   different conditions for simpl_match_cond

Ltac foo H :=  let t := type of H in  idtac t.foo H.
    *)
Ltac solve_assert_int :=
  simpl; rewrite P4Arith.bit_from_to_bool;
  unfold P4Arith.BitArith.mod_bound;
  try rewrite Z.mod_small by (unfold P4Arith.BitArith.upper_bound; lia);
  reflexivity.

Ltac simpl_match_cond cond :=
  simpl in cond; unfold fold_andb, fold_left in cond; simpl in cond;
  repeat lazymatch goal with
  | cond : context [Tofino.values_match_range ?x ?lo ?hi] |- _ =>
      erewrite (reduce_match_range _ x lo hi) in cond;
      [ idtac
      | solve_assert_int
      | compute; reflexivity
      | compute; reflexivity
      ]
  | cond : context [Tofino.values_match_singleton ?x ?y] |- _ =>
      erewrite (reduce_match_singleton _ x y) in cond;
      [ idtac
      | repeat constructor
      | solve_assert_int
      | compute; reflexivity
      ]
  | cond : context [Tofino.values_match_mask ?x ?v ?m] |- _ =>
      erewrite (reduce_match_mask _ x v m) in cond;
      [ idtac
      | solve_assert_int
      | compute; reflexivity
      | compute; reflexivity
      ];
      cbv - [Bool.eqb Z.odd Z.div] in cond
  end.
(* cbv -[Bool.eqb Z.odd Z.div] in cond *)

Ltac hoare_table_action_cases' :=
  first [
    apply hoare_table_action_cases'_nil (* solver: contradiction*)
  | refine (@id (hoare_table_action_cases' _ _ _ _ _ _ ((_, _) :: _)) _);
    lazymatch goal with
    | |- hoare_table_action_cases' _ _ _ _ _ _ ((?cond, _) :: _)  =>
      let H_cond := fresh in
      let cond_name := fresh "cond" in
      remember cond as cond_name eqn:H_cond;
      simpl_match_cond H_cond;
      subst cond_name
    end;
    apply hoare_table_action_cases'_cons;
    [ let H := fresh in intro H
    | let H := fresh in intro H;
      hoare_table_action_cases'
    ]
  ].

  hoare_table_action_cases'.

(* constructor :
   reduction as strong as Hnf (apply/reflexivity: certain form in mind) *)

  (* admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

(* [&& entry, entry, entry, entry ] *)

  apply hoare_table_action_cases'_cons.
  simpl.

  simpl_match_cond.

  hoare_table_action_cases'.
  simpl in H.
  P4Arith.to_lbool eval_p4int_val
  unfold frame_tick_tocks, num_frames in *.
  unfold fold_andb, fold_left in H. simpl in H.
  erewrite reduce_match_range in H.
  2 : { compute. reflexivity. }
  2 : { compute. reflexivity. }
  2 : {
    simpl. rewrite P4Arith.bit_from_to_bool.
    unfold P4Arith.BitArith.mod_bound.
    rewrite Z.mod_small.
    { reflexivity. }
    { unfold P4Arith.BitArith.upper_bound. lia. }
  }




Ltac solve_modifies :=  first [    solve [eauto 100 with nocore modifies]  | idtac "The modifies clause cannot be solved automatically."  ]
.


  table_action act_set_clear_win_1_body.
  { entailer. }
  { replace (get_clear_frame timer) with 0.
    2 : {
      unfold get_clear_frame.
      destruct (fst timer =? frame_time * num_frames) eqn:?.
      unfold is_true in *; lia.
      symmetry.
      eapply Z_div_squeeze with 0 7033; auto; lia.
    }
    entailer.
  }
 *)

Admitted.


Lemma tbl_clear_window_body' :
  func_sound ge tbl_clear_window_fd nil tbl_clear_window_spec.
Proof.
  start_function.
  simpl Tofino.extern_matches.
  hoare_table_action_cases'.


(*
Simpl: more heuristics in what to unfold.
       make more decisions.
       exponential time? 70 seconds
       no evaluation order => maybe evaluation before patternmatching =>
         unnecessary branching and computation
Bool.eqb
       (Z.odd
          (tstamp_mod / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 /
           2 / 2 / 2 / 2 / 2 / 2 / 2 / 2)) false && true

Call by value: unfold Bool.eqb and && true
               more computation
H0 : (if
       if
        Z.odd
          (tstamp_mod / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2 /
           2 / 2 / 2 / 2 / 2 / 2 / 2 / 2)
       then false
       else true
      then true
      else false) = true *)


(*  next_case'.
  { simpl in H0.
    replace (Z.odd (tstamp / 2097152)) with false by admit.
    table_action act_clear_window_signal_0_body.
    { entailer. }
    { auto. }
    { entailer. }
  }
  next_case'.
  { simpl in H1.
    replace (Z.odd (tstamp / 2097152)) with true by admit.
    table_action act_clear_window_signal_1_body.
    { entailer. }
    { auto. }
    { entailer. }
  }
  This case should be impossible. *)
  admit.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_set_win_insert_body) : func_specs.

Definition Filter_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "apply"] ge).

Definition filter_insert := @filter_insert num_frames num_rows num_slots ltac:(lia) ltac:(lia) ltac:(lia)
  frame_tick_tocks.

Program Definition hashes (key : Val) : listn Z num_rows := (exist _ [hash1 key; hash2 key; hash3 key] _).

Notation filter_repr := (filter_repr (frame_tick_tocks := frame_tick_tocks)).

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

Ltac simpl_assertion ::=
  cbn [
    (* First, most basic definitions for comparison. *)
    bool_rect bool_rec Bool.bool_dec Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec sumbool_rect
    sumbool_rec string_rect string_rec string_dec EquivUtil.StringEqDec EquivDec.equiv_dec EquivDec.list_eqdec
    in_dec path_eq_dec list_eq_dec Datatypes.list_rec list_rect negb is_left id

    is_some isSome

    P4String.str

    app find find

    fst snd force map lift_option

    lift_option_kv kv_map option_map List.filter

    AList.set AList.set_some AList.get

    filter_in Semantics.is_in flat_map

    eval_write_vars fold_left eval_write_var AList.set_some combine

    Members.update Members.get

    exclude

    ext_exclude eq_rect Result.Result.forallb Result.Result.andb].

Lemma Filter_insert_body :
  func_sound ge Filter_fd nil Filter_insert_spec.
Proof.
  intros_fs_bind; split. 2 : admit.
  init_function.
  destruct cf as [[ps ?H] ? ?].
  unfold filter_repr.
  cbn [proj1_sig] in *.
  destruct_list ps.
  normalize_EXT.
  Time step.
  Time step_call tbl_hash_index_1_body.
  { entailer. }
  Time simpl_assertion.
  step_call tbl_hash_index_2_body.
  { entailer. }
  Time simpl_assertion.
  step_call tbl_hash_index_3_body.
  { entailer. }
  Time simpl_assertion.
  set (is := (exist _ [hash1 key; hash2 key; hash3 key] eq_refl : listn Z 3)).
  set (clear_is := (exist _ (Zrepeat fil_clear_index 3) eq_refl : listn Z 3)).
  assert (Forall (fun i : Z => 0 <= i < num_slots) (`is)). {
    admit. (* need hash lemma *)
  }
  P4assert (0 <= fil_clear_index < num_slots). {
    unfold fil_clear_index_repr.
    normalize_EXT.
    admit.
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
  step_call tbl_clear_window_body.
  { entailer. }
  Intros _.
  set (new_timer := update_timer fil_timer (Z.odd (tstamp / 2097152))).
  (* We need assert_Prop. *)
  P4assert (0 <= fst new_timer <= num_frames * frame_tick_tocks).
  { unfold timer_repr.
    normalize_EXT.
    Intros_prop.
    apply ext_implies_prop_intro.
    unfold timer_wf in *.
    destruct (snd new_timer); lia.
  }
  step_call tbl_set_win_insert_body.
  { entailer. }
  { auto. }
  { lia. }
  Intros _.
  assert (0 <= get_clear_frame new_timer < num_frames) by admit.
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
    admit.
    (* TODO merge result *)
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
    admit.
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
    admit.
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
    admit.
  }
  lia.
Abort.
