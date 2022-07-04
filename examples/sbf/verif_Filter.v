Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.FilterRepr.
(* Require Import ProD3.examples.sbf.verif_Win1.
Require Import ProD3.examples.sbf.verif_Win2.
Require Import ProD3.examples.sbf.verif_Win3.
Require Import ProD3.examples.sbf.verif_Win4. *)
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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_2" (P4Bit 18 (hash1 key)) ds_md)]
        (EXT []))).

Lemma tbl_hash_index_2_body :
  func_sound ge tbl_hash_index_2_fd nil tbl_hash_index_2_spec.
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
        (ARG_RET [] ValBaseNull
        (MEM [(["ds_md"], update "hash_index_3" (P4Bit 18 (hash1 key)) ds_md)]
        (EXT []))).

Lemma tbl_hash_index_3_body :
  func_sound ge tbl_hash_index_3_fd nil tbl_hash_index_3_spec.
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
    WITH (i : Z) (ds_md : Sval)
      (_ : 0 <= i < num_slots),
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
  Intros' i'.
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
    Exists' (i' + 1).
    normalize_EXT.
    entailer.
    apply ext_implies_prop_intro.
    unfold update_clear_index.
    change (Z.pow_pos 2 18) with (2 ^ Z.of_N 18).
    rewrite Zplus_mod, H0. clear H0.
    destruct (i + 1 =? num_slots) eqn:?H.
    - assert (i = num_slots - 1) by lia.
      subst; auto.
    - rewrite Z.mod_small with (a := i + 1); auto.
      unfold num_slots in *; lia.
  }
Qed.

Definition regact_clear_window_signal_0_apply_fd :=
  ltac:(get_am_fd ge am_ge (p ++ ["regact_clear_window_signal_0"; "apply"]) ge).

Definition frame_tick_tocks : Z := 7034.

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

Definition act_clear_window_signal_0_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval)
      (_ : 0 <= fst t <= 28136),
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
  step_call regact_clear_window_signal_0_execute_body.
  { entailer. }
  { auto. }
  { lia. }
  { reflexivity. }
  step.
  entailer.
Qed.

Definition act_clear_window_signal_1_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "act_clear_window_signal_1"] ge).

Definition act_clear_window_signal_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval)
      (_ : 0 <= fst t <= 28136),
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
  step_call regact_clear_window_signal_1_execute_body.
  { entailer. }
  { auto. }
  { lia. }
  { reflexivity. }
  { auto. }
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_0_body) : func_specs.
#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_clear_window_signal_1_body) : func_specs.

Definition tbl_clear_window_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "tbl_clear_window"; "apply"] ge).

Definition tbl_clear_window_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ds_md"]]) [p ++ ["reg_clear_window"]]
    WITH (t : Z * bool) (ds_md : Sval) (tstamp : Z)
      (_ : 0 <= fst t <= 28136),
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
      (H_timer : 0 <= fst timer <= frame_tick_tocks * num_frames),
      PRE
        (ARG []
        (MEM [(["api"], P4Bit 8 INSERT);
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

Ltac rep_lia := unfold is_true, frame_time, num_frames in *; lia.


Lemma sval_to_val_eval_p4int_sval : forall t: P4Int.t Info,sval_to_val read_ndetbit  (eval_p4int_sval t)  (eval_p4int_val t).
Admitted.

Lemma reduce_match_range: forall w x lo hi x' lo' hi',
  Tofino.assert_int lo = Some (w, lo') ->
  Tofino.assert_int hi = Some (w, hi') ->
  Tofino.assert_int x = Some (w, x') ->
  Tofino.values_match_range x lo hi =
  (lo' <=? x') && (x' <=? hi').
Proof.
  intros.
  unfold Tofino.values_match_range.
  rewrite H, H0, H1. rewrite N.eqb_refl. simpl.
  reflexivity.
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
               repeat first [                simple apply sval_to_val_eval_p4int_sval              | econstructor              ] 
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


Ltac hoare_table_action_cases' :=
  first [
    apply hoare_table_action_cases'_nil (* solver: contradiction*)
  | apply hoare_table_action_cases'_cons;
    [ let H := fresh in intro H; simpl in H
    | let H := fresh in intro H; simpl in H; 
      hoare_table_action_cases'
    ]
  ].


[&& entry, entry, entry, entry ]


  hoare_table_action_cases'.
  unfold frame_time, num_frames in *.
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
      unfold is_true in *; rep_lia.
      symmetry.
      eapply Z_div_squeeze with 0 7033; auto; rep_lia.
    }
    entailer.
  }


Abort.


#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_set_win_insert_body) : func_specs.

Definition Filter_fd :=
  ltac:(get_fd ["Bf2BloomFilter"; "apply"] ge).

Definition filter_insert := @filter_insert num_frames num_rows num_slots ltac:(rep_lia) ltac:(unfold num_rows; rep_lia) ltac:(unfold num_slots; rep_lia)
  frame_tick_tocks.

Program Definition hashes (key : Val) : listn Z num_rows := (exist _ [hash1 key; hash2 key; hash3 key] _).

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
  intros_fs_bind; split. 2 : admit.
  init_function.
  step.
  step_call tbl_hash_index_1_body.
  { entailer. }
  step_call tbl_hash_index_2_body.
  { entailer. }
  step_call tbl_hash_index_3_body.
  { entailer. }
Abort.