Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.ConFilter.
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
    fold abs_plus.
    unfold eval_p4int_sval.
    cbn [width_signed].
    change (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool 32 old_value)))
      with (ValBaseBit (P4Arith.to_loptbool 32 old_value)).
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

Lemma in_scopes_split : forall ps1 ps2 ps3 ps4,
  forallb (fun p : path => in_scopes p ps1) ps3 ->
  forallb (fun p : path => in_scopes p ps2) ps4 ->
  forallb (fun p : path => in_scopes p (ps1 ++ ps2)) (ps3 ++ ps4).
Proof.
  intros.
  rewrite forallb_app, Reflect.andE; split.
Admitted.

Lemma in_scopes_refl : forall ps,
  forallb (fun p : path => in_scopes p ps) ps.
Proof.
Admitted.

Lemma ex_and_l : forall {A} (ep1 : A -> ext_pred) ps H ep2,
  ExtPred.equiv
    (ExtPred.and (ExtPred.ex ep1 ps H) ep2)
    (ExtPred.ex (fun x => ExtPred.and (ep1 x) ep2) (ps ++ ep_paths ep2) (fun x => in_scopes_split _ _ _ _ (H x) (in_scopes_refl _))).
Proof.
  intros. red. simpl. clear H.
  apply functional_extensionality; intros.
  apply prop_ext.
  sauto.
Qed.

Lemma ex_and_3 : forall {A} ep1 (ep2 : A -> ext_pred) ps H,
  ExtPred.equiv
    (ExtPred.and ep1 (ExtPred.ex ep2 ps H))
    (ExtPred.ex (fun x => ExtPred.and ep1 (ep2 x)) (ep_paths ep1 ++ ps) (fun x => in_scopes_split _ _ _ _ (in_scopes_refl _) (H x))).
Proof.
  intros. red. simpl. clear H.
  apply functional_extensionality; intros.
  apply prop_ext.
  sauto.
Qed.

Fixpoint replace_nth {A} (n : nat) (al : list A) (x : A) {struct n} : list A :=
  match n, al with
  | O, a :: al => x :: al
  | S n', a :: al' => a :: replace_nth n' al' x
  | _, nil => nil
  end.

Lemma extract_nth_ext_ex : forall n a_ext {A} (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  EXT a_ext =
    (fun es => exists x, EXT (replace_nth n a_ext (S x)) es).
Proof.
  intros.
  f_equal.
  clear -H0.
  generalize dependent n; induction a_ext; intros.
  + extensionality es.
    apply prop_ext.
    split; only 2 : hauto lq: on.
    intros _.
    replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H0. 2 : {
      destruct n; auto.
    }
    assert (exists x, S x es). {
      change (ExtPred.ex S ep H es).
      rewrite <- H0.
      exact I.
    }
    destruct H1 as [x ?].
    exists x. unfold replace_nth; destruct n; sauto q: on.
  + destruct n.
    * simpl in H0. rewrite H0.
      clear.
      extensionality es.
      apply prop_ext.
      simpl.
      sauto.
    * specialize (IHa_ext _ H0).
      change (EXT (a :: a_ext)) with (fun es => a es /\ EXT a_ext es).
      rewrite IHa_ext.
      clear.
      extensionality es.
      apply prop_ext.
      simpl. fcrush.
Qed.

Lemma extract_nth_ext_ex' : forall n a_mem a_ext {A} (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  MEM a_mem (EXT a_ext) =
    (EX (x : A), MEM a_mem (EXT (replace_nth n a_ext (S x))))%assr.
Proof.
  intros.
  erewrite extract_nth_ext_ex; eauto.
  clear.
  extensionality st.
  apply prop_ext.
  sauto.
Qed.

Lemma extract_nth_ext_ex'' : forall n pre a_ext {A} (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  (exists x, ext_implies pre (replace_nth n a_ext (S x))) ->
  ext_implies pre a_ext.
Proof.
  intros.
  destruct H1.
  unfold ext_implies in *.
  change ext_denote with EXT in *.
  erewrite extract_nth_ext_ex with (a_ext := a_ext) by eauto.
  eauto.
Qed.

Ltac extract_ex_in_EXT a :=
  lazymatch a with
  | MEM _ (EXT ?a_ext) =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_ext_ex' n' _ a_ext A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Ltac Intros' x :=
  lazymatch goal with
  | |- hoare_block _ _ ?pre _ _ =>
      extract_ex_in_EXT pre;
      eapply hoare_block_pre_ex;
      intro x
  end.

Ltac extract_ex_in_EXT' a :=
  lazymatch a with
  | ?a_ext =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      apply (@extract_nth_ext_ex'' n' _ a_ext A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Ltac Exists' x:=
  lazymatch goal with
  | |- ext_implies ?pre ?post =>
      extract_ex_in_EXT' post;
      exists x
  end.

Fixpoint remove_nth {A} (n : nat) (al : list A) {struct n} : list A :=
  match n, al with
  | O, a :: al => al
  | S n', a :: al' => a :: remove_nth n' al'
  | _, nil => nil
  end.

Lemma extract_nth_ext_prop : forall n a_mem a_ext (S : Prop),
  nth n a_ext (ExtPred.prop True) = (ExtPred.prop S) ->
  MEM a_mem (EXT a_ext) =
    (fun st => S /\ MEM a_mem (EXT (remove_nth n a_ext)) st).
Proof.
  intros.
  transitivity (MEM a_mem (fun es => S /\ EXT (remove_nth n a_ext) es)).
  - f_equal.
    generalize dependent n; induction a_ext; intros.
    + extensionality es.
      apply prop_ext.
      split; only 2 : hauto lq: on.
      intros _.
      replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H. 2 : {
        destruct n; auto.
      }
      split; only 2 : sauto.
      assert (ExtPred.prop S es). {
        rewrite <- H.
        simpl. auto.
      }
      apply H0.
    + destruct n.
      * simpl in H. rewrite H.
        clear.
        reflexivity.
      * specialize (IHa_ext _ H).
        change (EXT (a :: a_ext)) with (fun es => a es /\ EXT a_ext es).
        rewrite IHa_ext.
        clear.
        extensionality es.
        apply prop_ext.
        simpl. fcrush.
  - clear.
    extensionality st.
    apply prop_ext.
    destruct st.
    sauto.
Qed.

Ltac extract_prop_in_EXT a :=
  lazymatch a with
  | MEM _ (EXT ?a_ext) =>
    lazymatch a_ext with context [(ExtPred.prop ?S) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_ext_prop n' _ a_ext S eq_refl);
      unfold remove_nth at 1
    end
  end.

Lemma hoare_block_pre_prop : forall p (P : Prop) pre block post,
  (P -> hoare_block ge p pre block post) ->
  hoare_block ge p (fun st : state => P /\ pre st) block post.
Proof.
  unfold hoare_block.
  intros.
  hauto lq: on.
Qed.

Ltac Intros_prop :=
  lazymatch goal with
  | |- hoare_block _ _ ?pre _ _ =>
      extract_prop_in_EXT pre;
      eapply hoare_block_pre_prop;
      intros ?H
  end.

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

Lemma ext_implies_prop_intro : forall pre (P : Prop),
  P ->
  ext_implies pre [ExtPred.prop P].
Proof.
  intros.
  sauto.
Qed.

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

Definition num_frames := 4.
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
  start_function.
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
        destruct (fst timer =? frame_time * num_frames) eqn:?. 1 : rep_lia.
        symmetry.
        eapply Z_div_squeeze with 0 7033; auto; rep_lia.
      }
      entailer.
    }
Abort.
