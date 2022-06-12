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

Definition act_set_clear_win_1_spec : func_spec :=
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
Abort.

Definition P4Type_bf2_win_md_t :=
  TypStruct
    [({| P4String.tags := NoInfo; str := "api" |}, TypBit 8);
     ({| P4String.tags := NoInfo; str := "index_1" |}, TypBit 18);
     ({| P4String.tags := NoInfo; str := "index_2" |}, TypBit 18);
     ({| P4String.tags := NoInfo; str := "index_3" |}, TypBit 18);
     ({| P4String.tags := NoInfo; str := "rw_1" |}, TypBit 8);
     ({| P4String.tags := NoInfo; str := "rw_2" |}, TypBit 8);
     ({| P4String.tags := NoInfo; str := "rw_3" |}, TypBit 8)].

Definition P4New_bf2_win_md_t := Eval compute in
  force dummy_val (uninit_sval_of_typ None P4Type_bf2_win_md_t).

Definition P4_bf2_win_md_t (op : Sval) (is : list Sval) :=
  ValBaseStruct
    [("api", op);
     ("index_1", Znth 0 is);
     ("index_2", Znth 1 is);
     ("index_3", Znth 2 is);
     ("rw_1", P4NewBit 8);
     ("rw_2", P4NewBit 8);
     ("rw_3", P4NewBit 8)].

Definition act_set_clear_win_1_spec2 : func_spec :=
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

Lemma act_set_clear_win_1_body2 :
  func_sound ge act_set_clear_win_1_fd nil act_set_clear_win_1_spec2.
Proof.
  start_function.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  Time step.
  simpl.
  entailer.
Qed.






