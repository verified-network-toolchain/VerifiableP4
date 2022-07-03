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

Definition Filter_fundef :=
  ltac:(get_fd ["Bf2BloomFilter"; "apply"] ge).

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
    unfold eval_p4int_sval.
    cbn [width_signed].
    change (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 32 old_value)))
      with (P4Bit 32 old_value).
    change (ValBaseBit
        (P4Arith.to_loptbool 32
           (value {| tags := NoInfo; value := 1; width_signed := Some (32%N, false) |})))
      with (P4Bit 32 1).
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

Definition num_frames : Z := 4.
Definition frame_tick_tocks : Z := 7034.

Notation update_timer := (@update_timer num_frames frame_tick_tocks).

Definition timer_repr_val (t : Z * bool) :=
  ValBaseStruct [("hi", ValBaseBit (P4Arith.to_lbool 16 (fst t)));
                 ("lo", ValBaseBit (P4Arith.to_lbool 16 (Z.b2z (snd t))))].

Definition timer_repr_sval (t : Z * bool) :=
  ValBaseStruct [("hi", P4Bit 16 (fst t));
                 ("lo", P4Bit 16 (Z.b2z (snd t)))].

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

Ltac simpl_eval_p4int_sval :=
  lazymatch goal with
  | |- context [eval_p4int_sval ?i] =>
      (* We want to make sure i does not contain (opaque) variables. *)
      let v := eval compute in (value i) in
      let ws := eval compute in (width_signed i) in
      match ws with
      | Some (?w, true) =>
          change (eval_p4int_sval i) with (P4Int w v)
      | Some (?w, false) =>
          change (eval_p4int_sval i) with (P4Bit w v)
      | None =>
          change (eval_p4int_sval i) with (ValBaseInteger v)
      end
  | H : context [eval_p4int_sval ?i] |- _ =>
      revert H;
      simpl_eval_p4int_sval;
      intro H
  end.

Lemma regact_clear_window_signal_0_apply_body :
  func_sound am_ge regact_clear_window_signal_0_apply_fd nil regact_clear_window_signal_0_apply_spec.
Proof.
  start_function.
  rename old_value into t.
  change (eval_val_to_sval (timer_repr_val t)) with (timer_repr_sval t).
  step.
  (* TODO fix this bug in semantics:
    why we have ["rv"] here?
    when generating uninitialized value for out parameters, the locators in these are not properly set.
  *)
  step_if (MEM [(["apply"; "val"], timer_repr_sval (update_timer t false))]
           (EXT [])).
  { step.
    step.
    step.
    step.
    unfold timer_repr_sval in *.
    cbn.
    (* manipulate H *)
      simpl get in H.
      simpl_eval_p4int_sval.
      rewrite abs_neq_bit in H.
      destruct (snd t) eqn:?H. 2 : inv H.
      clear H.
    entailer.
    red.
    change (ValBaseBit (map Some (rev (P4Arith.to_lbool' (Pos.to_nat 16) 1 []))))
      with (P4Bit 16 1).
    rewrite abs_plus_bit.
    apply sval_refine_refl.
  }
  { step.
    unfold timer_repr_sval in *.
    cbn.
    (* manipulate H *)
      unfold timer_repr_sval in H.
      simpl get in H.
      simpl_eval_p4int_sval.
      rewrite abs_neq_bit in H.
      destruct (snd t) eqn:?H. 1 : inv H.
      clear H.
      rewrite H0.
    entailer.
  }
  step.
  step.
  entailer.
Qed.

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

Ltac simpl_assertion :=
  cbn [
    (* First, most basic definitions for comparison. *)
    bool_rect bool_rec Bool.bool_dec Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec sumbool_rect
    sumbool_rec string_rect string_rec string_dec EquivUtil.StringEqDec EquivDec.equiv_dec EquivDec.list_eqdec

    str

    app find find

    fst snd force map lift_option

    lift_option_kv kv_map

    AList.set AList.set_some AList.get

    filter_in Semantics.is_in flat_map

    eval_write_vars fold_left eval_write_var AList.set_some combine

    update get].

Ltac step' := step; simpl_assertion.

Lemma act_set_clear_win_1_body :
  func_sound ge act_set_clear_win_1_fd nil act_set_clear_win_1_spec.
Proof.
  start_function.
  unfold P4New_bf2_win_md_t.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
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
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
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
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
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
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
  step'.
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

Definition frame_time := 7034.

Notation get_clear_frame := (get_clear_frame num_frames frame_time).
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
      (H_timer : 0 <= fst timer <= frame_time * num_frames),
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

Ltac next_case' :=
  constructor; (let H := fresh in intro H).

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

Ltac rep_lia := unfold frame_time, num_frames in *; lia.

Lemma tbl_set_win_insert_body :
  func_sound ge tbl_set_win_fd nil tbl_set_win_insert_spec.
Proof.

(* Ltac foo := let x := constr:(1 + 2) in idtac x.

Ltac foo' := let x := eval compute in [...] in idtac x.
  foo'.


  Search P4Arith.BitArith.mod_bound.
  Z.mod_small *)
(* Ltac hoare_func_table ::=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_list_intro'; (* hoare_table_match_list *)
        [ reflexivity (* eval_exprs *)
        | simplify_lift_option_eval_sval_to_val; (* lift_option (.. keysvals) *)
          reflexivity
        | eapply hoare_table_entries_intros; (* hoare_table_entries *)
          (* repeat econstructor *)
          idtac
        | hoare_extern_match_list (* hoare_extern_match_list *)
        ]
      | idtac (* hoare_table_action_cases' *)
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end. *)

  start_function.
  Time repeat match goal with
  | |- context [ValSetProd ?l] =>
      let l' := eval compute in l in
      progress (change l with l')
  end.
  Time simpl Tofino.extern_matches.
  
  
  (* econstructor.
  { econstructor.
    { econstructor.
      { repeat econstructor. }
      { repeat econstructor. }
    }
    econstructor.
  }
  { econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  repeat econstructor.
  repeat econstructor.
  repeat econstructor.

eval_sval_to_val_P4Bit

  
exec_table_entries


Inductive
exec_match (tags_t : Type) (target : Target) (ge : genv)
(read_one_bit : option bool -> bool -> Prop) : path -> Match -> ValueSet -> Prop :=
    exec_match_dont_care : forall (this : path) (tag : tags_t) (typ : P4Type),
                           exec_match ge read_one_bit this (MkMatch tag MatchDontCare typ)
                             ValSetUniversal
  | exec_match_mask : forall (expr : Syntax.Expression) (exprv : Val) 
                        (mask : Syntax.Expression) (maskv : Val) (this : path) 
                        (tag : tags_t) (typ : P4Type),
                      exec_expr_det ge read_one_bit this empty_state expr exprv ->
                      exec_expr_det ge read_one_bit this empty_state mask maskv ->
                      exec_match ge read_one_bit this (MkMatch tag (MatchMask expr mask) typ)
                        (ValSetMask exprv maskv)
  | exec_match_range : forall (lo : Syntax.Expression) (lov : Val) (hi : Syntax.Expression)
                         (hiv : Val) (this : path) (tag : tags_t) (typ : P4Type),
                       exec_expr_det ge read_one_bit this empty_state lo lov ->
                       exec_expr_det ge read_one_bit this empty_state hi hiv ->
                       exec_match ge read_one_bit this (MkMatch tag (MatchRange lo hi) typ)
                         (ValSetRange lov hiv)
  | exec_match_cast : forall (newtyp : P4Type) (expr : Syntax.Expression) 
                        (oldv : Val) (newv : ValueSet) (this : path) 
                        (tag : tags_t) (typ real_typ : P4Type),
                      exec_expr_det ge read_one_bit this empty_state expr oldv ->
                      get_real_type ge newtyp = Some real_typ ->
                      Ops.eval_cast_set real_typ oldv = Some newv ->
                      exec_match ge read_one_bit this (MkMatch tag (MatchCast newtyp expr) typ)
                        newv

Arguments exec_match {tags_t}%type_scope {target} _ _%function_scope _%list_scope _ _
Arguments exec_match_dont_care {tags_t}%type_scope {target} _ _%function_scope _%list_scope _ _
Arguments exec_match_mask {tags_t}%type_scope {target} _ _%function_scope _ _ _ _ _%list_scope _
  _ _ _
Arguments exec_match_range {tags_t}%type_scope {target} _ _%function_scope _ _ _ _ _%list_scope
  _ _ _ _
Arguments exec_match_cast {tags_t}%type_scope {target} _ _%function_scope _ _ _ _ _%list_scope _
  _ _ _ _ _ *)






  
  
  (* Print Ltac init_function. *)
  
  
  (* cbn [combine map hd].
  simpl Tofino.extern_matches.
  unfold Tofino.extern_matches. simpl.
  replace (Tofino.is_true) with (id (A := bool)). unfold id. *)
  
  repeat match goal with
  | |- context [ValSetProd ?l] =>
      let l' := eval compute in l in
      progress change l with l'
  end.
  next_case'.
  { simpl Tofino.valset_to_valsett in H.
    simpl in H.
    destruct (Tofino.values_match_singleton (ValBaseBit (P4Arith.to_lbool 8 INSERT))
             (ValBaseBit [false; true; false; false; false; false; false; false])) eqn:?H.
    2 : { inv H. }
    destruct (Tofino.values_match_range (ValBaseBit (P4Arith.to_lbool 16 (fst timer)))
            (ValBaseBit
               [false; false; false; false; false; false; false; false; false;
               false; false; false; false; false; false; false])
            (ValBaseBit
               [true; false; false; true; true; true; true; false; true; true;
               false; true; true; false; false; false])) eqn:?H.
    2 : { inv H. }
    clear H.
    unfold Tofino.values_match_range, Tofino.assert_int in H1.
    rewrite P4Arith.bit_from_to_bool in H1.
    simpl in H1.
    unfold P4Arith.BitArith.mod_bound in H1.
    rewrite Z.mod_small in H1. 2 : {
      unfold P4Arith.BitArith.upper_bound. rep_lia.
    }
    table_action act_set_clear_win_1_body.
    { entailer. }
    { replace (get_clear_frame timer) with 0. 2 : {
        unfold get_clear_frame.
        destruct (fst timer =? frame_time * num_frames) eqn:?.
        unfold frame_time, num_frames in *. lia.
        unfold frame_time in *.
        symmetry.
        eapply Z_div_squeeze with 0 7033; auto; rep_lia.
      }
      entailer.
    }
Abort.
 