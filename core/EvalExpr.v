Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Syntax.P4String.
Require Import Poulet4.Utils.P4Arith.
Require Import Poulet4.Utils.Utils.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Members.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Hoare.
Require Import Coq.ZArith.BinInt.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Local Open Scope string_scope.

Lemma lift_option_map_some: forall {A: Type} (al: list A),
    lift_option (map Some al) = Some al.
Proof. intros. induction al; simpl; [|rewrite IHal]; easy. Qed.

Definition val_sim {A B : Type} (v : @ValueBase A) (v' : @ValueBase B) : Prop :=
  exec_val (fun _ _ => True) v v'.

Lemma Forall2_to_lbool: forall w v1 v2, Forall2 (fun _ _ => True) (to_lbool w v1) (to_lbool w v2).
Proof.
  intros. apply Forall2_True. rewrite <- !ZtoNat_Zlength. rewrite !Zlength_to_lbool. auto.
Qed.

Lemma val_sim_sym: forall {A B: Type} (v1: @ValueBase A) (v2: @ValueBase B),
    val_sim v1 v2 -> val_sim v2 v1.
Proof.
  intros; eapply exec_val_sym; eauto.
Qed.

Lemma val_sim_trans:
  forall {A B C} (v1: @ValueBase A) (v2: @ValueBase B) (v3: @ValueBase C),
    val_sim v1 v2 -> val_sim v2 v3 -> val_sim v1 v3.
Proof. intros. eapply exec_val_trans; eauto. repeat intro; auto. Qed.

Lemma val_sim_on_top: forall {A B: Type} (c: A -> B -> Prop) v1 v2,
    exec_val c v1 v2 -> val_sim v1 v2.
Proof. intros. eapply exec_val_impl; eauto. Qed.

Section EvalExpr.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (string).
Notation path := (list ident).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation Expression := (@Expression tags_t).

Context `{@Target tags_t Expression}.

(* Shorthands for Svals. *)

Definition P4Bit (w : N) (v : Z) : Sval :=
  ValBaseBit (to_loptbool w v).

(* Deprecated *)
Definition P4NewBit (w : N) : Sval :=
  ValBaseBit (Zrepeat None (Z.of_N w)).

Definition P4Bit_ (w : N) : Sval :=
  ValBaseBit (Zrepeat None (Z.of_N w)).

Definition P4Int (w : N) (v : Z) : Sval :=
  ValBaseInt (to_loptbool w v).

Definition P4Int_ (w : N) : Sval :=
  ValBaseInt (Zrepeat None (Z.of_N w)).

Definition build_abs_unary_op (actual_unary_op : Val -> option Val) : Sval -> Sval :=
  fun sv =>
    match eval_sval_to_val sv with
    | Some v =>
        eval_val_to_sval (force ValBaseNull (actual_unary_op v))
    | _ =>
        let v := force_sval_to_val sv in
        val_to_liberal_sval (force ValBaseNull (actual_unary_op v))
    end.

(* "Not" under abstract interpretation. *)
Definition abs_not : Sval -> Sval :=
  build_abs_unary_op (Ops.eval_unary_op Not).

Definition build_abs_binary_op (actual_binany_op : Val -> Val -> option Val) : Sval -> Sval -> Sval :=
  fun sv1 sv2 =>
    match eval_sval_to_val sv1, eval_sval_to_val sv2 with
    | Some v1, Some v2 =>
        eval_val_to_sval (force ValBaseNull (actual_binany_op v1 v2))
    | _, _ =>
        let v1 := force_sval_to_val sv1 in
        let v2 := force_sval_to_val sv2 in
        val_to_liberal_sval (force ValBaseNull (actual_binany_op v1 v2))
    end.

(* Plus under abstract interpretation. *)
Definition abs_plus : Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op Plus).

Definition abs_minus : Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op Minus).

Definition abs_mul : Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op Mul).

Definition abs_bitand : Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op BitAnd).

Definition abs_eq: Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op Eq).

Definition abs_neq: Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.eval_binary_op NotEq).

Lemma abs_bin_op_bit: forall op w i1 i2,
    ~ In op [Shl; Shr; Eq; NotEq; PlusPlus] ->
    build_abs_binary_op (Ops.eval_binary_op op)
                        (P4Bit w i1)
                        (P4Bit w i2)
    = eval_val_to_sval
        (force ValBaseNull
               (Ops.eval_binary_op_bit op w (BitArith.mod_bound w i1)
                                       (BitArith.mod_bound w i2))).
Proof.
  intros. unfold P4Bit, to_loptbool.
  unfold build_abs_binary_op. unfold eval_sval_to_val.
  rewrite !lift_option_map_some.
  unfold Ops.eval_binary_op.
  destruct op; try rewrite !bit_from_to_bool;
    try rewrite BinNat.N.eqb_refl; auto; exfalso; apply H0.
  - now left.
  - right. now left.
  - do 2 right. now left.
  - do 3 right. now left.
  - do 4 right. now left.
Qed.

Lemma abs_plus_bit : forall w i1 i2,
  abs_plus
    (P4Bit w i1)
    (P4Bit w i2)
  = ValBaseBit (to_loptbool w (i1 + i2)).
Proof.
  intros. unfold abs_plus. rewrite abs_bin_op_bit.
  - simpl. rewrite BitArith.plus_mod_mod.
    now rewrite to_lbool_bit_plus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_minus_bit : forall w i1 i2,
  abs_minus
    (P4Bit w i1)
    (P4Bit w i2)
  = (P4Bit w (i1 - i2)).
Proof.
  intros. unfold abs_minus. rewrite abs_bin_op_bit.
  - simpl. rewrite BitArith.minus_mod_mod.
    now rewrite to_lbool_bit_minus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_mul_bit : forall w i1 i2,
  abs_mul
    (P4Bit w i1)
    (P4Bit w i2)
  = (P4Bit w (i1 * i2)).
Proof.
  intros. unfold abs_mul. rewrite abs_bin_op_bit.
  - simpl. rewrite BitArith.mult_mod_mod.
    now rewrite to_lbool_bit_mult.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_eq_bit : forall w i1 i2,
  abs_eq
    (P4Bit w i1) (P4Bit w i2)
  = ValBaseBool
      (Some (BitArith.mod_bound w i1 =? BitArith.mod_bound w i2)%Z).
Proof.
  intros. unfold abs_eq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, P4Bit, to_loptbool.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op. simpl.
  rewrite !Zlength_to_lbool. rewrite BinNat.N.eqb_refl. simpl.
  now rewrite !bit_to_lbool_back.
Qed.

Lemma abs_neq_bit : forall w i1 i2,
  abs_neq
    (P4Bit w i1) (P4Bit w i2)
  = ValBaseBool
      (Some (~~ (BitArith.mod_bound w i1 =? BitArith.mod_bound w i2)%Z)).
Proof.
  intros. unfold abs_neq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, P4Bit, to_loptbool.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op. simpl.
  rewrite !Zlength_to_lbool. rewrite BinNat.N.eqb_refl. simpl.
  now rewrite !bit_to_lbool_back.
Qed.

Lemma abs_bin_op_int: forall op w i1 i2,
    ~ In op [Eq; NotEq; PlusPlus] ->
    build_abs_binary_op (Ops.eval_binary_op op)
                        (ValBaseInt (to_loptbool w i1))
                        (ValBaseInt (to_loptbool w i2))
    = eval_val_to_sval
        (force ValBaseNull
               (Ops.eval_binary_op_int
                  op w (if BinNat.N.eqb w N0
                        then 0%Z
                        else IntArith.mod_bound (pos_of_N w) i1)
                  (if BinNat.N.eqb w N0
                   then 0%Z
                   else IntArith.mod_bound (pos_of_N w) i2))).
Proof.
  intros. unfold to_loptbool, build_abs_binary_op, eval_sval_to_val.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op.
  destruct op; try rewrite !int_from_to_bool;
    try rewrite BinNat.N.eqb_refl; auto; exfalso; apply H0.
  - now left.
  - right. now left.
  - do 2 right. now left.
Qed.

Lemma abs_plus_int : forall w i1 i2,
  abs_plus
    (ValBaseInt (to_loptbool w i1))
    (ValBaseInt (to_loptbool w i2))
  = (ValBaseInt (to_loptbool w (i1 + i2))).
Proof.
  intros. unfold abs_plus. rewrite abs_bin_op_int.
  - simpl. destruct (BinNat.N.eqb w N0) eqn:?H.
    + rewrite BinNat.N.eqb_eq in H0. subst w. simpl.
      unfold to_loptbool. now simpl.
    + rewrite IntArith.plus_mod_mod. now rewrite to_lbool_int_plus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3.
Qed.

Lemma abs_minus_int : forall w i1 i2,
  abs_minus
    (ValBaseInt (to_loptbool w i1))
    (ValBaseInt (to_loptbool w i2))
  = (ValBaseInt (to_loptbool w (i1 - i2))).
Proof.
  intros. unfold abs_minus. rewrite abs_bin_op_int.
  - simpl. destruct (BinNat.N.eqb w N0) eqn:?H.
    + rewrite BinNat.N.eqb_eq in H0. subst w. simpl.
      unfold to_loptbool. now simpl.
    + rewrite IntArith.minus_mod_mod. now rewrite to_lbool_int_minus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3.
Qed.

Lemma abs_mul_int : forall w i1 i2,
  abs_mul
    (ValBaseInt (to_loptbool w i1))
    (ValBaseInt (to_loptbool w i2))
  = (ValBaseInt (to_loptbool w (i1 * i2))).
Proof.
  intros. unfold abs_mul. rewrite abs_bin_op_int.
  - simpl. destruct (BinNat.N.eqb w N0) eqn:?H.
    + rewrite BinNat.N.eqb_eq in H0. subst w. simpl.
      unfold to_loptbool. now simpl.
    + rewrite IntArith.mult_mod_mod. now rewrite to_lbool_int_mult.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3.
Qed.

Lemma abs_eq_int : forall w i1 i2,
  abs_eq
    (ValBaseInt (to_loptbool w i1)) (ValBaseInt (to_loptbool w i2))
  = ValBaseBool
      (Some (if (BinNat.N.eqb w N0) then true else
              (IntArith.mod_bound (pos_of_N w) i1 =?
                 IntArith.mod_bound (pos_of_N w) i2)%Z)).
Proof.
  intros. unfold abs_eq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, to_loptbool.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op. simpl.
  rewrite !Zlength_to_lbool. rewrite BinNat.N.eqb_refl. simpl.
  rewrite !int_to_lbool_back. destruct (BinNat.N.eqb w N0); auto.
Qed.

Lemma abs_neq_int : forall w i1 i2,
  abs_neq
    (ValBaseInt (to_loptbool w i1)) (ValBaseInt (to_loptbool w i2))
  = ValBaseBool
      (Some (if (BinNat.N.eqb w N0) then false else
              ~~ (IntArith.mod_bound (pos_of_N w) i1 =?
                    IntArith.mod_bound (pos_of_N w) i2)%Z)).
Proof.
  intros. unfold abs_neq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, to_loptbool.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op. simpl.
  rewrite !Zlength_to_lbool. rewrite BinNat.N.eqb_refl. simpl.
  rewrite !int_to_lbool_back. destruct (BinNat.N.eqb w N0); auto.
Qed.

Definition eval_read_var (a : mem_assertion) (p : path) : option Sval :=
  AList.get a p.

Definition eval_read_vars (a : mem_assertion) (ps : list path) : list (option Sval) :=
  map (eval_read_var a) ps.

Lemma eval_read_var_sound : forall a_mem a_ext p sv,
  eval_read_var a_mem p = Some sv ->
  hoare_read_var (MEM a_mem (EXT a_ext)) p sv.
Proof.
  unfold hoare_read_var; intros.
  destruct st as [m es].
  eapply mem_denote_get in H0. 2 : apply H1.
  hauto lq: on.
Qed.

Lemma eval_read_vars_sound' : forall a_mem a_ext ps svs,
  eval_read_vars a_mem ps = map Some svs ->
  hoare_read_vars' (MEM a_mem (EXT a_ext)) ps svs.
Proof.
  induction ps; intros.
  - destruct svs. 2 : inv H0.
    constructor.
  - destruct svs. 1 : inv H0.
    inv H0.
    constructor.
    + apply eval_read_var_sound; auto.
    + apply IHps. auto.
Qed.

Lemma eval_read_vars_sound : forall a_mem a_ext ps svs,
  eval_read_vars a_mem ps = map Some svs ->
  hoare_read_vars (MEM a_mem (EXT a_ext)) ps svs.
Proof.
  intros. apply hoare_read_vars_intro, eval_read_vars_sound'; auto.
Qed.

Lemma opbin_eq_dec: forall x y: OpBin, {x = y} + {x <> y}.
Proof. intros. destruct x, y; try (now left); right; intro S; inversion S. Defined.

Fixpoint eval_expr (ge : genv) (p : path) (a : mem_assertion) (expr : Expression) : option Sval :=
  match expr with
  | MkExpression _ expr _ dir =>
      match expr with
      | ExpInt i => Some (eval_p4int_sval i)
      | ExpName _ loc =>
          if is_directional dir then
            match loc with
            | LInstance p => eval_read_var a p
            | _ => None
            end
          else
            option_map eval_val_to_sval (loc_to_val_const ge p loc)
      | ExpBitStringAccess bits lo hi =>
          match eval_expr ge p a bits with
          | Some bitssv =>
              Some
                match sval_to_bits_width bitssv with
                | Some (bitsbl, wn) =>
                    let lonat := BinNat.N.to_nat lo in
                    let hinat := BinNat.N.to_nat hi in
                    (* if (andb (Nat.leb lonat hinat) (Nat.ltb hinat wn)) then *)
                      ValBaseBit (Ops.bitstring_slice bitsbl lonat hinat)
                    (* else ValBaseNull *)
                | None => ValBaseNull
                end
          | None => None
          end
      | ExpUnaryOp op arg =>
          match eval_expr ge p a arg with
          | Some argv =>
              match op with
              | Not =>
                  Some (abs_not argv)
              | _ =>
                  Some (build_abs_unary_op (Ops.eval_unary_op op) argv)
              end
          | None => None
          end
      | ExpBinaryOp op larg rarg =>
          if (in_dec opbin_eq_dec op [Shl; Shr]) then
            None
          else
            match eval_expr ge p a larg, eval_expr ge p a rarg with
            | Some largv, Some rargv =>
                match op with
                | Plus =>
                    Some (abs_plus largv rargv)
                | Minus =>
                    Some (abs_minus largv rargv)
                | Mul =>
                    Some (abs_mul largv rargv)
                | Eq =>
                    Some (abs_eq largv rargv)
                | NotEq =>
                    Some (abs_neq largv rargv)
                | BitAnd =>
                    Some (abs_bitand largv rargv)
                | _ =>
                    Some (build_abs_binary_op (Ops.eval_binary_op op) largv rargv)
                end
            | _, _ => None
            end
      | ExpCast newtyp arg =>
          match eval_expr ge p a arg, get_real_type ge newtyp with
          | Some argv, Some real_typ => Some (build_abs_unary_op (Ops.eval_cast real_typ) argv)
          | _, _ => None
          end
      | ExpList exprs =>
          (option_map ValBaseTuple) (lift_option (map (eval_expr ge p a) exprs))
      | ExpTypeMember tname member =>
          match IdentMap.get (str tname) (ge_typ ge) with
          (* enum *)
          | Some (TypEnum ename None members) =>
              Some (ValBaseEnumField (str ename) (str member))
          (* senum *)
          | Some (TypEnum ename (Some etyp) members) =>
              let fields := force nil (IdentMap.get (str ename) (ge_senum ge)) in
              match AList.get fields (str member) with
              | Some seum => Some (ValBaseSenumField (str ename) seum)
              | None => None
              end
          | _ => None
          end
      | ExpExpressionMember expr name =>
          match eval_expr ge p a expr with
          | Some sv =>
              Some (get (P4String.str name) sv)
          | None => None
          end
      | _ => None
      end
  end.

Lemma get_sound : forall sv f sv',
  get_member sv f sv' ->
  get f sv = sv'.
Proof.
  intros.
  inv H0.
  - unfold get. rewrite H1. auto.
  - unfold get. rewrite H1. auto.
  - unfold get. rewrite H1. auto.
  - reflexivity.
  - unfold get.
    destruct (BinNat.N.eqb next N0);
      inv H1; reflexivity.
Qed.

Ltac destruct_match H :=
  match goal with
  | H: context [match ?A with | _ => _ end] |- _ => destruct A eqn:?H
  end.

Lemma eval_expr_member_sound : forall ge p a tags expr typ dir name sv,
  hoare_expr ge p a expr sv ->
  hoare_expr ge p a (MkExpression tags (ExpExpressionMember expr name) typ dir) (get (P4String.str name) sv).
Proof.
  unfold hoare_expr.
  intros.
  inv H2.
  assert (sval_refine sv sv0) by (eapply H0; eauto).
  apply get_sound in H12.
  rewrite <- H12.
  apply sval_refine_get; auto.
Qed.

Lemma fields_get_sval_refine:
  forall (name : P4String) (kvs : AList.AList ident Sval eq)
         (sv' : Sval) (fields : AList.AList ident Sval eq),
    AList.get fields (str name) = Some sv' ->
    AList.all_values (exec_val bit_refine) kvs fields ->
    sval_refine (force ValBaseNull (AList.get kvs (str name))) sv'.
Proof.
  intros. red in H1. revert sv' H0. induction H1; intros.
  - unfold AList.get in H0. simpl in H0. inversion H0.
  - destruct y as [ky vy]. destruct x as [kx vx]. destruct H0. cbn [fst snd] in *.
    destruct (EquivUtil.StringEqDec (str name) ky).
    + rewrite AList.get_eq_cons in H2; auto. inv H2. rewrite AList.get_eq_cons; auto.
    + rewrite AList.get_neq_cons in H2; auto. subst. rewrite AList.get_neq_cons; auto.
Qed.

Lemma sval_to_val_Some_case1:
  forall (n : list (option bool)) (lb' l : list bool),
    lift_option n = Some l -> Forall2 read_ndetbit n lb' -> l = lb'.
Proof.
  intros n lb' l H2 H3. revert l H2. induction H3; intros; simpl in H2.
  1: now inversion H2. inv H0. 1: inv H2. destruct_match H2; inv H2.
  specialize (IHForall2 l1 eq_refl). now inv IHForall2.
Qed.

Lemma sval_to_val_Some_case2:
  forall svals_to_avals : AList.StringAList Sval -> option (AList.StringAList Val),
    svals_to_avals =
      (fun sl => lift_option_kv (kv_map eval_sval_to_val sl)) ->
    forall vs : list (ident * Sval),
      Forall
        (fun '(_, v) =>
           forall oldv : Val,
             sval_to_val read_ndetbit v oldv ->
             forall v0 : Val, eval_sval_to_val v = Some v0 -> v0 = oldv) vs ->
      forall (kvs' : AList.AList ident Val eq) (s : AList.StringAList Val),
        svals_to_avals vs = Some s ->
        AList.all_values (exec_val read_ndetbit) vs kvs' -> s = kvs'.
Proof.
  intros svals_to_avals Havals vs H0 kvs' s H1 H4.
  revert kvs' s H1 H4. induction H0; intros.
  - rewrite Havals in H1. inv H1. inv H4. auto.
  - rewrite Havals in H2. simpl in H2. rewrite <- (equal_f Havals) in H2. destruct x. simpl in H2. destruct_match H2. 2 : inv H2.
    inversion H4. subst x l0 kvs'. clear H4. destruct y. simpl in *. destruct H7.
    subst s0. destruct_match H2; inversion H2. subst s. clear H2.
    specialize (H0 v1 H5 v0 eq_refl). subst v0.
    specialize (IHForall l' s0 eq_refl H9). now subst s0.
Qed.

Lemma sval_to_val_Some_case3:
  forall eval_sval_to_vals : list Sval -> option (list Val),
    eval_sval_to_vals =
      (fun sl => lift_option (map eval_sval_to_val sl)) ->
    forall vs : list Sval,
      Forall
        (fun v : Sval =>
           forall oldv : Val,
             sval_to_val read_ndetbit v oldv ->
             forall v0 : Val, eval_sval_to_val v = Some v0 -> v0 = oldv) vs ->
      forall lv' l : list Val,
        eval_sval_to_vals vs = Some l ->
        Forall2 (exec_val read_ndetbit) vs lv' -> l = lv'.
Proof.
  intros eval_sval_to_vals Hvals vs H0 lv' l H1 H4.
  revert lv' l H1 H4. induction H0; intros.
  - rewrite Hvals in H1. inv H1. inv H4. auto.
  - rewrite Hvals in H2. simpl in H2. rewrite <- (equal_f Hvals) in H2. destruct_match H2. 2: inv H2.
    inversion H4. subst x0 l1 lv'. clear H4. specialize (H0 _ H7 v eq_refl).
    subst v. destruct_match H2; inversion H2. subst l0. clear H2.
    specialize (IHForall l' l1 eq_refl H9). now subst.
Qed.

Lemma sval_to_val_Some:
  forall (v : Sval) (oldv : Val),
    sval_to_val read_ndetbit v oldv ->
    forall v0 : Val, eval_sval_to_val v = Some v0 -> v0 = oldv.
Proof.
  remember (
    fun (sl : list Sval) =>
      lift_option (map eval_sval_to_val sl)
  ) as eval_sval_to_vals. rename Heqeval_sval_to_vals into Hvals.
  remember (
    fun (sl : AList.StringAList Sval) =>
      lift_option_kv (kv_map eval_sval_to_val sl)
  ) as svals_to_avals. rename Heqsvals_to_avals into Havals.
  intro. induction v using custom_ValueBase_ind;
    intros; simpl in H1; try (inv H1; now inv H0).
  2-4: destruct_match H1; inv H1; inv H0; f_equal;
  eapply sval_to_val_Some_case1; eauto.
  - destruct_match b; inv H1. inv H0. inv H2. auto.
  - inversion H1. subst lv oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- (equal_f Hvals) in H1. eapply sval_to_val_Some_case3; eauto.
  - inversion H1. subst kvs oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- (equal_f Havals) in H1. eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst kvs b0 oldv. clear H1. simpl in H2. destruct_match b.
    2: inv H2. subst b. destruct_match H2; inversion H2. subst v0. clear H2.
    inversion H5. subst b b0. clear H5. f_equal. rewrite <- (equal_f Havals) in H1.
    eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst kvs oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. rewrite <- (equal_f Havals) in H1.
    f_equal. eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst lv next oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- (equal_f Hvals) in H1. eapply sval_to_val_Some_case3; eauto.
  - destruct_match H1; inversion H1. subst v0. clear H1. inversion H0. subst t v0 oldv.
    clear H0. f_equal. specialize (IHv _ H5 v1 eq_refl). now subst v1.
Qed.

Section eval_sval_to_val_sval_to_val.
  Lemma lift_option_strict_read_ndetbit : forall sbs bs,
    lift_option sbs = Some bs ->
    Forall2 strict_read_ndetbit sbs bs.
  Proof.
    induction sbs; intros; inv H0.
    - constructor.
    - destruct_match H2. 2 : inv H2.
      destruct_match H2; inv H2.
      constructor.
      + constructor.
      + auto.
  Qed.

  Hint Resolve lift_option_strict_read_ndetbit : core.

  Lemma exec_val_impl_case1 : forall svs vs,
    Forall
       (fun sv : Sval =>
        forall v : Val, eval_sval_to_val sv = Some v -> sval_to_val strict_read_ndetbit sv v) svs ->
    lift_option (map eval_sval_to_val svs) = Some vs ->
    Forall2 (exec_val strict_read_ndetbit) svs vs.
  Proof.
    intros.
    generalize dependent vs.
    induction svs; intros; inv H1.
    - constructor.
    - inv H0.
      destruct_match H3; inv H3.
      destruct_match H2; inv H2.
      constructor.
      + eapply H4; auto.
      + auto.
  Qed.

  Lemma exec_val_impl_case2 : forall (svs : list (ident * ValueBase)) vs,
    Forall
       (fun '(_, sv) =>
        forall v : Val, eval_sval_to_val sv = Some v -> sval_to_val strict_read_ndetbit sv v) svs ->
    lift_option_kv (kv_map eval_sval_to_val svs) = Some vs ->
    AList.all_values (exec_val strict_read_ndetbit) svs vs.
  Proof.
    induction svs; intros; inv H1.
    - constructor.
    - inv H0.
      destruct_match H3; inv H3.
      destruct_match H2; inv H2.
      destruct_match H3; inv H3.
      constructor.
      + split; auto.
        apply H4; auto.
      + apply IHsvs; auto.
  Qed.

  Lemma eval_sval_to_val_sval_to_val : forall sv v,
    eval_sval_to_val sv = Some v ->
    sval_to_val strict_read_ndetbit sv v.
  Proof.
    intros sv v; revert v.
      induction sv using custom_ValueBase_ind; intros * H_eval;
      inv H_eval;
      try constructor; eauto.
    - destruct_match H_eval; inv H1. constructor. constructor.
    - destruct_match H_eval; inv H1. constructor; auto.
    - destruct_match H_eval; inv H1. constructor; auto.
    - destruct_match H_eval; inv H1. constructor; auto.
    - destruct_match H_eval; inv H2. constructor.
      eapply exec_val_impl_case1; auto.
    - destruct_match H_eval; inv H2. constructor.
      eapply exec_val_impl_case2; auto.
    - destruct_match H_eval; inv H2.
      destruct_match H4; inv H4.
      constructor; only 1 : constructor.
      eapply exec_val_impl_case2; auto.
    - destruct_match H2; inv H2. constructor.
      eapply exec_val_impl_case2; auto.
    - destruct_match H2; inv H2. constructor.
      eapply exec_val_impl_case1; auto.
    - destruct_match H1; inv H1. constructor.
      apply IHsv; auto.
  Qed.
End eval_sval_to_val_sval_to_val.

Lemma eval_val_to_sval_val_sim: forall v, val_sim v (eval_val_to_sval v).
Proof. intros. apply (val_sim_on_top read_detbit). now rewrite val_to_sval_iff. Qed.

Lemma sval_refine_liberal:
  forall v1 v2, val_sim v1 v2 -> sval_refine (val_to_liberal_sval v1) v2.
Proof.
  remember (fun (sl : list Val) =>
              map val_to_liberal_sval sl
           ) as to_vals. rename Heqto_vals into Hvals.
  remember (fun (sl : AList.StringAList Val) =>
              kv_map val_to_liberal_sval sl
           ) as to_avals. rename Heqto_avals into Havals.
  induction v1 using custom_ValueBase_ind; intros;
    try (inv H0; simpl; now constructor).
  - inv H0. simpl. constructor. constructor.
  - inv H0. simpl. constructor. induction H2; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inv H0. simpl. constructor. induction H2; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inv H0. simpl. constructor. induction H4; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inversion H1. subst lv v2. clear H1. simpl. constructor. rewrite <- (equal_f Hvals).
    revert H0 lv' H3. induction vs; intros; inversion H3; subst lv'; clear H3;
      rewrite Hvals; constructor; inversion H0; subst x0 l0; clear H0. 1: now apply H7.
    rewrite <- (equal_f Hvals). subst x l. apply IHvs; auto.
  - inversion H1. subst kvs v2. clear H1. simpl. constructor. rewrite <- (equal_f Havals).
    revert kvs' H3. induction H0; intros; inversion H3; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H5. split; auto. apply H0. auto.
    + rewrite <- (equal_f Havals). apply IHForall. auto.
  - inversion H1. subst kvs b0 v2. clear H1 H4. simpl. constructor.
    1: unfold bool_to_none; constructor. rewrite <- (equal_f Havals). revert kvs' H6.
    induction H0; intros; inversion H6; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H4; split; auto. apply H0. auto.
    + rewrite <- (equal_f Havals). apply IHForall; auto.
  - inversion H1. subst kvs v2. clear H1. simpl. constructor. rewrite <- (equal_f Havals).
    revert kvs' H3. induction H0; intros; inversion H3; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H5. split; auto. apply H0. auto.
    + rewrite <- (equal_f Havals). apply IHForall. auto.
  - inversion H1. subst lv next v2. clear H1. simpl. constructor. rewrite <- (equal_f Hvals).
    revert H0 lv' H5. induction vs; intros; inversion H5; subst lv'; clear H5;
      rewrite Hvals; constructor; inversion H0; subst x0 l0; clear H0. 1: now apply H7.
    rewrite <- (equal_f Hvals). subst x l. apply IHvs; auto.
  - inversion H0. subst typ_name v v2. clear H0. simpl. constructor. apply IHv1. auto.
Qed.

Lemma sval_refine_liberal_eval:
  forall v : Val, sval_refine (val_to_liberal_sval v) (eval_val_to_sval v).
Proof. intros. apply sval_refine_liberal. apply eval_val_to_sval_val_sim. Qed.

Lemma sval_refine_map_bool_to_none: forall l1 l2,
    length l1 = length l2 -> Forall2 bit_refine (map bool_to_none l1) l2.
Proof.
  intros. rewrite map_bool_to_none. revert l2 H0. induction l1; intros.
  - destruct l2. 2: simpl in H0; inversion H0. simpl. constructor.
  - destruct l2. 1: simpl in H0; inversion H0. simpl. constructor.
    + constructor.
    + simpl in H0. inversion H0. now apply IHl1.
Qed.

Lemma force_sval_to_val_val_sim: forall v, val_sim v (force_sval_to_val v).
Proof.
  remember (fix sval_to_vals (sl : list Sval) : list Val :=
              match sl with
              | [] => []
              | s :: rest => force_sval_to_val s :: sval_to_vals rest
              end) as to_vals. rename Heqto_vals into Hvals.
  remember (fun (sl : AList.StringAList Sval) =>
              kv_map force_sval_to_val sl
           ) as to_avals. rename Heqto_avals into Havals.
  induction v using custom_ValueBase_ind; simpl; try (now constructor).
  - destruct b; now constructor.
  - constructor. apply Forall2_True. now rewrite map_length.
  - constructor. apply Forall2_True. now rewrite map_length.
  - constructor. apply Forall2_True. now rewrite map_length.
  - constructor. rewrite <- (equal_f Hvals). induction vs; rewrite Hvals. 1: constructor.
    rewrite <- Hvals. inversion H0. subst x l. clear H0. constructor; auto.
  - constructor. rewrite <- (equal_f Havals). induction vs; rewrite Havals. 1: constructor.
    simpl; rewrite <- (equal_f Havals). inversion H0. subst x l. clear H0. destruct a.
    constructor; auto. apply IHvs. auto.
  - constructor; auto. rewrite <- (equal_f Havals). induction vs; rewrite Havals. 1: constructor.
    simpl; rewrite <- (equal_f Havals). destruct a. inversion H0. subst x l. clear H0.
    constructor; auto. apply IHvs; auto.
  - constructor. rewrite <- (equal_f Havals). induction vs; rewrite Havals. 1: constructor.
    simpl; rewrite <- (equal_f Havals). inversion H0. subst x l. clear H0. destruct a.
    constructor; auto. apply IHvs. auto.
  - constructor. rewrite <- (equal_f Hvals). induction vs; rewrite Hvals. 1: constructor.
    rewrite <- Hvals. inversion H0. subst x l. clear H0. constructor; auto.
Qed.

Ltac solve_ex_sim :=
  match goal with
  | |- exists A, Some ?B = Some A /\ val_sim _ _ => exists B; split; auto; constructor
  end.

Definition cast_type_ind (P: P4Type -> Prop) :=
  my_P4Type_ind _ P (fun _ => True) (fun _ => True) (fun _ => True).

Lemma eval_cast_val_sim: forall (typ: P4Type) v1 newv1 v2,
    Ops.eval_cast typ v1 = Some newv1 ->
    val_sim v1 v2 ->
    exists newv2, Ops.eval_cast typ v2 = Some newv2 /\ val_sim newv1 newv2.
Proof.
  induction typ using my_P4Type_ind with
    (Q := fun _ => True) (R := fun _ => True) (S := fun _ => True); intros; try simpl in H0; try (now inv H0); auto.
  - destruct v1; simpl in H0; inv H0. inv H1. destruct value. inv H3.
    destruct value. 2: destruct b; inv H3. inv H2. inv H6. simpl. exists (ValBaseBool y).
    destruct y; split; auto; destruct b; inv H3; constructor; auto.
  - destruct v1; simpl in H0; inv H0; inv H1; simpl.
    + solve_ex_sim. apply Forall2_refl. intros; auto.
    + destruct_match H3; inv H3. pose proof (Forall2_Zlength H2). rewrite H1 in H0.
      rewrite H0. solve_ex_sim. apply Forall2_to_lbool.
    + solve_ex_sim. apply Forall2_to_lbool.
    + destruct_match H3; inv H3. destruct_match H2; inv H2. inv H5. pose proof (Forall2_Zlength H2).
      rewrite H1 in H0. rewrite H0. solve_ex_sim. auto.
  - destruct v1; simpl in H0; inv H0; inv H1; simpl.
    + destruct_match H3; inv H3. solve_ex_sim. constructor; auto.
    + solve_ex_sim. apply Forall2_to_lbool.
    + solve_ex_sim. apply Forall2_to_lbool.
    + destruct_match H3; inv H3. pose proof (Forall2_Zlength H2). rewrite H1 in H0.
      rewrite H0. solve_ex_sim. apply Forall2_to_lbool.
    + destruct_match H3; inv H3. destruct_match H2; inv H2. inv H5. pose proof (Forall2_Zlength H2).
      rewrite H1 in H0. rewrite H0. solve_ex_sim. auto.
  - remember (fix values_of_val_tuple (l1 : list P4Type) (l0 : list Val) {struct l1} :
               option (list Val) :=
                match l1 with
                | [] => match l0 with
                        | [] => Some []
                        | _ :: _ => None
                        end
                | t :: l1' =>
                    match l0 with
                    | [] => None
                    | oldv :: l2' =>
                        match Ops.eval_cast t oldv with
                        | Some newv => match values_of_val_tuple l1' l2' with
                                       | Some l3 => Some (newv :: l3)
                                       | None => None
                                       end
                        | None => None
                        end
                    end
                end) as cast_tuple. rename Heqcast_tuple into Htlp. simpl in H1.
    rewrite <- Htlp in H1. destruct_match H1; inversion H1. subst newv1. clear H1.
    destruct_match H3; inversion H3. subst v1. clear H5. inversion H2. subst lv v2. clear H2.
    simpl. rewrite <- Htlp. revert ts H0 l l0 H3 lv' H4. induction ts; intros.
    + rewrite Htlp in *. destruct_match H3; inversion H3. subst l0. subst l. clear H3.
      inversion H4. subst lv'. solve_ex_sim. constructor.
    + inversion H0. subst x l1. clear H0. specialize (IHts H6). clear H6.
      rewrite Htlp, <- Htlp in H3. destruct l0. 1: inv H3. destruct_match H3. 2: inv H3.
      destruct_match H3; inversion H3. subst l. clear H3. inversion H4. subst x l lv'. clear H4.
      specialize (IHts _ _ H1 _ H8). specialize (H5 _ _ _ H0 H6). clear H0 H1 H6 H8.
      destruct H5 as [newy [? ?]]. destruct IHts as [newl' [? ?]]. rewrite Htlp, <- Htlp.
      destruct_match H2; inversion H2; subst newl'. clear H2. rewrite H0.
      solve_ex_sim. constructor; auto. inversion H3. subst lv lv'. auto.
  - remember (fix fields_of_val_tuple (l1 : AList tags_t P4Type) (l0 : list Val) {struct l1} :
               option (Ops.Fields Val) :=
                 match l1 with
                 | [] => match l0 with
                         | [] => Some []
                         | _ :: _ => None
                         end
                 | (k, t) :: l1' =>
                     match l0 with
                     | [] => None
                     | oldv :: l2' =>
                         match Ops.eval_cast t oldv with
                         | Some newv => match fields_of_val_tuple l1' l2' with
                                        | Some l3 => Some ((str k, newv) :: l3)
                                        | None => None
                                        end
                         | None => None
                         end
                     end
                 end) as of_tuple. rename Heqof_tuple into Htlp.
    remember (fix fields_of_val_record
                  (l1 : AList tags_t P4Type) (l0 : Ops.Fields Val) {struct l1} :
                    option (Ops.Fields Val) :=
                  match l1 with
                  | [] => Some []
                  | (k, t) :: l1' =>
                      match AList.get l0 (str k) with
                      | Some oldv =>
                          match Ops.eval_cast t oldv with
                          | Some newv =>
                              match
                                fields_of_val_record l1'
                                  (AListUtil.remove_first (str k) l0)
                              with
                              | Some l3 => Some ((str k, newv) :: l3)
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  end) as of_record. rename Heqof_record into Hrcd.
    simpl in H1. rewrite <- Htlp, <- Hrcd in H1. destruct_match H1; inversion H1. subst newv1.
    clear H1. destruct v1; inversion H3; clear H4.
    + destruct_match H3. 1: inv H3. inversion H2. subst lv v2. clear H2. simpl.
      rewrite <- Htlp. rewrite H1. clear H1. revert xts l lv' f H0 H3 H5. induction xts; intros.
      * rewrite Htlp in H3. destruct l; inversion H3; subst f; clear H3. inversion H5. subst lv'.
        rewrite Htlp. solve_ex_sim; auto. constructor.
      * rewrite Htlp, <- Htlp in H3. destruct a as [k t]. destruct l. 1: inv H3.
        destruct_match H3. 2: inv H3. destruct_match H3; inversion H3. subst f. clear H3.
        inversion H5. subst x l0 lv'. clear H5. inversion H0. subst x l0. clear H0.
        specialize (IHxts _ _ _ H7 H2 H8). simpl snd in *. specialize (H5 _ _ _ H1 H6).
        clear H1 H2 H6 H7 H8. destruct H5 as [newy [? ?]]. destruct IHxts as [? [? ?]].
        destruct_match H2; inversion H2. subst x. clear H2. inversion H3. subst kvs b kvs' b'.
        clear H3. rewrite Htlp, <- Htlp. rewrite H0. rewrite H4.
        solve_ex_sim; auto. constructor; auto.
    + destruct_match H3. 1: inv H3. destruct_match H3. 1: inv H3. inversion H2. subst kvs v2.
      clear H2. simpl. rewrite <- Hrcd.
      assert (~~ (AList.key_unique xts && AList.key_unique kvs') = false). {
        clear -H1 H6. rewrite Bool.negb_false_iff in *. apply andb_prop in H1.
        destruct H1. apply andb_true_intro. split; auto. clear -H0 H6. revert kvs' H6.
        induction fields; intros; inv H6; auto. simpl in H0. destruct a.
        destruct_match H0. 1: inv H0. destruct y. simpl in *. destruct H2. subst s0.
        specialize (IHfields H0 _ H4). erewrite all_values_get_none_is_none; eauto. }
      assert (~~ (PeanoNat.Nat.eqb (Datatypes.length xts) (Datatypes.length kvs')) = false). {
        clear -H4 H6. rewrite Bool.negb_false_iff in *. rewrite PeanoNat.Nat.eqb_eq in *.
        apply Forall2_Zlength in H6. rewrite !Zcomplements.Zlength_correct in H6.
        apply Znat.Nat2Z.inj in H6. etransitivity; eauto. } rewrite H2, H5. clear H1 H2 H4 H5.
      revert xts H0 fields f H3 kvs' H6. induction xts; intros.
      * rewrite Hrcd in H3. inversion H3. subst f. clear H3. rewrite Hrcd.
        solve_ex_sim; auto. constructor.
      * rewrite Hrcd, <- Hrcd in H3. destruct a as [k t]. do 2 (destruct_match H3; [|inv H3]).
        destruct_match H3; inversion H3. subst f. clear H3. rewrite Hrcd, <- Hrcd.
        inversion H0. subst x l. clear H0. pose proof H6 as Hallv.
        apply AListUtil.all_values_remove_first with
          (HKR := EquivUtil.StringEqDec) (key := (str k)) in H6.
        specialize (IHxts H8 _ _ H4 _ H6). clear H4 H8. simpl in *.
        eapply all_values_get_some_exists_rel in H1; eauto. destruct H1 as [v' [? ?]].
        rewrite H0. specialize (H7 _ _ _ H2 H1). destruct H7 as [v0' [? ?]]. rewrite H3.
        destruct IHxts as [? [? ?]]. destruct_match H5; inversion H5. subst x. clear H5.
        solve_ex_sim; auto.  inversion H7. subst kvs b kvs'0 b'.
        clear H7. constructor; auto.
    + destruct_match H3. 1: inv H3. destruct_match H3. 1: inv H3. inversion H2. subst kvs b v2.
      clear H2. simpl. rewrite <- Hrcd. clear H7. rename H9 into H6.
      assert (~~ (AList.key_unique xts && AList.key_unique kvs') = false). {
        clear -H1 H6. rewrite Bool.negb_false_iff in *. apply andb_prop in H1.
        destruct H1. apply andb_true_intro. split; auto. clear -H0 H6. revert kvs' H6.
        induction fields; intros; inv H6; auto. simpl in H0. destruct a.
        destruct_match H0. 1: inv H0. destruct y. simpl in *. destruct H2. subst s0.
        specialize (IHfields H0 _ H4). erewrite all_values_get_none_is_none; eauto. }
      assert (~~ (PeanoNat.Nat.eqb (Datatypes.length xts) (Datatypes.length kvs')) = false). {
        clear -H4 H6. rewrite Bool.negb_false_iff in *. rewrite PeanoNat.Nat.eqb_eq in *.
        apply Forall2_Zlength in H6. rewrite !Zcomplements.Zlength_correct in H6.
        apply Znat.Nat2Z.inj in H6. etransitivity; eauto. } rewrite H2, H5. clear H1 H2 H4 H5 b'.
      revert xts H0 fields f H3 kvs' H6. induction xts; intros.
      * rewrite Hrcd in H3. inversion H3. subst f. clear H3. rewrite Hrcd.
        solve_ex_sim; auto. constructor.
      * rewrite Hrcd, <- Hrcd in H3. destruct a as [k t]. do 2 (destruct_match H3; [|inv H3]).
        destruct_match H3; inversion H3. subst f. clear H3. rewrite Hrcd, <- Hrcd.
        inversion H0. subst x l. clear H0. pose proof H6 as Hallv.
        apply AListUtil.all_values_remove_first with
          (HKR := EquivUtil.StringEqDec) (key := (str k)) in H6.
        specialize (IHxts H8 _ _ H4 _ H6). clear H4 H8.
        simpl in *. eapply all_values_get_some_exists_rel in H1; eauto. destruct H1 as [v' [? ?]].
        rewrite H0. specialize (H7 _ _ _ H2 H1). destruct H7 as [v0' [? ?]]. rewrite H3.
        destruct IHxts as [? [? ?]]. destruct_match H5; inversion H5. subst x. clear H5.
        solve_ex_sim; auto. inversion H7. subst kvs b kvs'0 b'. clear H7.
        constructor; auto.
  - remember (fix fields_of_val_tuple (l1 : AList tags_t P4Type) (l0 : list Val) {struct l1} :
               option (Ops.Fields Val) :=
                 match l1 with
                 | [] => match l0 with
                         | [] => Some []
                         | _ :: _ => None
                         end
                 | (k, t) :: l1' =>
                     match l0 with
                     | [] => None
                     | oldv :: l2' =>
                         match Ops.eval_cast t oldv with
                         | Some newv => match fields_of_val_tuple l1' l2' with
                                        | Some l3 => Some ((str k, newv) :: l3)
                                        | None => None
                                        end
                         | None => None
                         end
                     end
                 end) as of_tuple. rename Heqof_tuple into Htlp.
    remember (fix fields_of_val_record
                  (l1 : AList tags_t P4Type) (l0 : Ops.Fields Val) {struct l1} :
                    option (Ops.Fields Val) :=
                  match l1 with
                  | [] => Some []
                  | (k, t) :: l1' =>
                      match AList.get l0 (str k) with
                      | Some oldv =>
                          match Ops.eval_cast t oldv with
                          | Some newv =>
                              match
                                fields_of_val_record l1'
                                  (AListUtil.remove_first (str k) l0)
                              with
                              | Some l3 => Some ((str k, newv) :: l3)
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  end) as of_record. rename Heqof_record into Hrcd.
    simpl in H1. rewrite <- Htlp, <- Hrcd in H1. destruct_match H1; inversion H1. subst newv1.
    clear H1. destruct v1; inversion H3; clear H4.
    + destruct_match H3. 1: inv H3. inversion H2. subst lv v2. clear H2. simpl.
      rewrite <- Htlp. rewrite H1. clear H1. revert xts l lv' f H0 H3 H5. induction xts; intros.
      * rewrite Htlp in H3. destruct l; inversion H3; subst f; clear H3. inversion H5. subst lv'.
        rewrite Htlp. solve_ex_sim; auto. constructor.
      * rewrite Htlp, <- Htlp in H3. destruct a as [k t]. destruct l. 1: inv H3.
        destruct_match H3. 2: inv H3. destruct_match H3; inversion H3. subst f. clear H3.
        inversion H5. subst x l0 lv'. clear H5. inversion H0. subst x l0. clear H0.
        specialize (IHxts _ _ _ H7 H2 H8). simpl snd in *. specialize (H5 _ _ _ H1 H6).
        clear H1 H2 H6 H7 H8. destruct H5 as [newy [? ?]]. destruct IHxts as [? [? ?]].
        destruct_match H2; inversion H2. subst x. clear H2. inversion H3. subst kvs kvs'.
        clear H3. rewrite Htlp, <- Htlp. rewrite H0. rewrite H4.
        solve_ex_sim; auto. constructor; auto.
    + destruct_match H3. 1: inv H3. destruct_match H3. 1: inv H3. inversion H2. subst kvs v2.
      clear H2. simpl. rewrite <- Hrcd.
      assert (~~ (AList.key_unique xts && AList.key_unique kvs') = false). {
        clear -H1 H6. rewrite Bool.negb_false_iff in *. apply andb_prop in H1.
        destruct H1. apply andb_true_intro. split; auto. clear -H0 H6. revert kvs' H6.
        induction fields; intros; inv H6; auto. simpl in H0. destruct a.
        destruct_match H0. 1: inv H0. destruct y. simpl in *. destruct H2. subst s0.
        specialize (IHfields H0 _ H4). erewrite all_values_get_none_is_none; eauto. }
      assert (~~ (PeanoNat.Nat.eqb (Datatypes.length xts) (Datatypes.length kvs')) = false). {
        clear -H4 H6. rewrite Bool.negb_false_iff in *. rewrite PeanoNat.Nat.eqb_eq in *.
        apply Forall2_Zlength in H6. rewrite !Zcomplements.Zlength_correct in H6.
        apply Znat.Nat2Z.inj in H6. etransitivity; eauto. } rewrite H2, H5. clear H1 H2 H4 H5.
      revert xts H0 fields f H3 kvs' H6. induction xts; intros.
      * rewrite Hrcd in H3. inversion H3. subst f. clear H3. rewrite Hrcd.
        solve_ex_sim; auto. constructor.
      * rewrite Hrcd, <- Hrcd in H3. destruct a as [k t]. do 2 (destruct_match H3; [|inv H3]).
        destruct_match H3; inversion H3. subst f. clear H3. rewrite Hrcd, <- Hrcd.
        inversion H0. subst x l. clear H0. pose proof H6 as Hallv.
        apply AListUtil.all_values_remove_first with
          (HKR := EquivUtil.StringEqDec) (key := (str k)) in H6.
        specialize (IHxts H8 _ _ H4 _ H6). clear H4 H8.
        simpl in *. eapply all_values_get_some_exists_rel in H1; eauto. destruct H1 as [v' [? ?]].
        rewrite H0. specialize (H7 _ _ _ H2 H1). destruct H7 as [v0' [? ?]]. rewrite H3.
        destruct IHxts as [? [? ?]]. destruct_match H5; inversion H5. subst x. clear H5.
        solve_ex_sim. inversion H7. subst kvs kvs'0. constructor; auto.
    + destruct_match H3. 1: inv H3. destruct_match H3. 1: inv H3. inversion H2. subst kvs b v2.
      clear H2. simpl. rewrite <- Hrcd. clear H7. rename H9 into H6.
      assert (~~ (AList.key_unique xts && AList.key_unique kvs') = false). {
        clear -H1 H6. rewrite Bool.negb_false_iff in *. apply andb_prop in H1.
        destruct H1. apply andb_true_intro. split; auto. clear -H0 H6. revert kvs' H6.
        induction fields; intros; inv H6; auto. simpl in H0. destruct a.
        destruct_match H0. 1: inv H0. destruct y. simpl in *. destruct H2. subst s0.
        specialize (IHfields H0 _ H4). erewrite all_values_get_none_is_none; eauto. }
      assert (~~ (PeanoNat.Nat.eqb (Datatypes.length xts) (Datatypes.length kvs')) = false). {
        clear -H4 H6. rewrite Bool.negb_false_iff in *. rewrite PeanoNat.Nat.eqb_eq in *.
        apply Forall2_Zlength in H6. rewrite !Zcomplements.Zlength_correct in H6.
        apply Znat.Nat2Z.inj in H6. etransitivity; eauto. } rewrite H2, H5. clear H1 H2 H4 H5 b'.
      revert xts H0 fields f H3 kvs' H6. induction xts; intros.
      * rewrite Hrcd in H3. inversion H3. subst f. clear H3. rewrite Hrcd.
        solve_ex_sim; auto. constructor.
      * rewrite Hrcd, <- Hrcd in H3. destruct a as [k t]. do 2 (destruct_match H3; [|inv H3]).
        destruct_match H3; inversion H3. subst f. clear H3. rewrite Hrcd, <- Hrcd.
        inversion H0. subst x l. clear H0. pose proof H6 as Hallv.
        apply AListUtil.all_values_remove_first with
          (HKR := EquivUtil.StringEqDec) (key := (str k)) in H6.
        specialize (IHxts H8 _ _ H4 _ H6). clear H4 H8.
        simpl in *. eapply all_values_get_some_exists_rel in H1; eauto. destruct H1 as [v' [? ?]].
        rewrite H0. specialize (H7 _ _ _ H2 H1). destruct H7 as [v0' [? ?]]. rewrite H3.
        destruct IHxts as [? [? ?]]. destruct_match H5; inversion H5. subst x. clear H5.
        solve_ex_sim. inversion H7. subst kvs kvs'0. constructor; auto.
  - simpl in *. destruct t; simpl in H1. 2: inv H1.
    destruct p; try (now inv H1); destruct v1; try (now inv H1).
    + destruct_match H1; inv H1. inv H2. simpl. pose proof (Forall2_Zlength H4). rewrite H1 in H3.
      rewrite H3. solve_ex_sim. constructor. auto.
    + destruct v1; try (now inv H1). destruct_match H1; inv H1. inv H2. inv H6. simpl.
      pose proof (Forall2_Zlength H2). rewrite H1 in H3. rewrite H3.
      solve_ex_sim. constructor. auto.
    + destruct_match H1; inv H1. inv H2. simpl. pose proof (Forall2_Zlength H4). rewrite H1 in H3.
      rewrite H3. solve_ex_sim. constructor. auto.
    + destruct v1; try (now inv H1). destruct_match H1; inv H1. inv H2. inv H6. simpl.
      pose proof (Forall2_Zlength H2). rewrite H1 in H3. rewrite H3.
      solve_ex_sim. constructor. auto.
  - simpl. apply IHtyp with v1; auto.
Qed.

Lemma Forall_from_to_lbool:
  forall (l1 l2: list bool) (w1 w2 : N) (n1 n2 z1 z2: Z),
    BitArith.from_lbool l1 = (w1, n1) ->
    Forall2 (fun _ _ : bool => True) l1 l2 ->
    BitArith.from_lbool l2 = (w2, n2) ->
    Forall2 (fun _ _ : bool => True) (to_lbool w1 z1) (to_lbool w2 z2).
Proof.
  intros. pose proof (Forall2_Zlength H1). unfold BitArith.from_lbool in H0, H2.
  rewrite H3 in H0. assert (w1 = w2) by (inv H0; inv H2; auto). subst.
  apply Forall2_to_lbool.
Qed.

Lemma eval_unary_op_val_sim: forall op v1 newv1 v2,
    Ops.eval_unary_op op v1 = Some newv1 ->
    val_sim v1 v2 ->
    exists newv2, Ops.eval_unary_op op v2 = Some newv2 /\ val_sim newv1 newv2.
Proof.
  intros. destruct op; cbn [Ops.eval_unary_op] in H0; destruct v1; try (now inv H0).
  2, 3, 5, 6: destruct (BitArith.from_lbool value) as [wv nv] eqn:?H; inv H0; inv H1;
  cbn [Ops.eval_unary_op]; destruct (BitArith.from_lbool lb') as [w n] eqn:?H;
  solve_ex_sim; eapply Forall_from_to_lbool; eauto.
  all: inv H0; inv H1; simpl; solve_ex_sim; auto.
Qed.

Lemma eval_binary_op_val_sim_plusplus: forall v1 v2 v3 v4 result,
    Ops.eval_binary_op PlusPlus v1 v2 = Some result ->
    val_sim v1 v3 -> val_sim v2 v4 ->
    exists result', Ops.eval_binary_op PlusPlus v3 v4 = Some result' /\
                 val_sim result result'.
Proof.
  simpl. intros. destruct v1; simpl in H0; try (now inv H0);
    destruct v2; inv H0; inv H1; inv H2; simpl; solve_ex_sim; apply Forall2_app; auto.
Qed.

Lemma eval_binary_op_val_sim_eq: forall v1 v2 v3 v4 result,
    Ops.eval_binary_op Eq v1 v2 = Some result ->
    val_sim v1 v3 -> val_sim v2 v4 ->
    exists result', Ops.eval_binary_op Eq v3 v4 = Some result' /\
                 val_sim result result'.
Proof.
  simpl. intros. destruct_match H0; inv H0. revert v1 v2 v3 v4 b H1 H2 H3.
  induction v1 using custom_ValueBase_ind; destruct v2; intros;
    simpl in H3; try (now inv H3).
  - inv H3. inv H1. inv H2. simpl. solve_ex_sim. auto.
  - inv H3. inv H1. inv H2. simpl. solve_ex_sim. auto.
  - destruct_match H3; inv H3. inv H1. inv H2. simpl.
    pose proof (Forall2_Zlength H3). pose proof (Forall2_Zlength H4).
    rewrite <- H1, <- H2, H0. solve_ex_sim. auto.
  - destruct_match H3; inv H3. inv H1. inv H2. simpl.
    pose proof (Forall2_Zlength H3). pose proof (Forall2_Zlength H4).
    rewrite <- H1, <- H2, H0. solve_ex_sim. auto.
  - destruct_match H3; inv H3. inv H1. inv H2. simpl. rewrite H0. solve_ex_sim. auto.
  - remember (fix eval_binary_op_eq_tuple (l1 l2 : list Val) {struct l1} : option bool :=
          match l1 with
          | [] => match l2 with
                  | [] => Some true
                  | _ :: _ => None
                  end
          | x1 :: l1' =>
              match l2 with
              | [] => None
              | x2 :: l2' =>
                  match Ops.eval_binary_op_eq x1 x2 with
                  | Some b1 =>
                      match eval_binary_op_eq_tuple l1' l2' with
                      | Some b2 => Some (b1 && b2)
                      | None => None
                      end
                  | None => None
                  end
              end
          end) as eq_tuple. rename Heqeq_tuple into Htlp.
    inversion H1. subst lv v3. clear H1. inversion H2. subst lv v4. clear H2. simpl.
    rewrite <- Htlp. revert vs l lv' lv'0 b H0 H3 H4 H5. induction vs; intros.
    + rewrite Htlp in H3. destruct l; inversion H3. subst b. clear H3.
      inversion H4. subst lv'0. inversion H5. subst lv'. rewrite Htlp.
      solve_ex_sim; auto.
    + rewrite Htlp, <- Htlp in H3. destruct l. 1: inv H3. destruct lv'0. 1: inv H4.
      destruct lv'. 1: inv H5. inversion H0. subst x l0. clear H0.
      inversion H4. subst x l0 y l'. clear H4. inversion H5. subst x l0 y l'. clear H5.
      destruct_match H3. 2: inv H3. destruct_match H3. 2: inv H3.
      specialize (H6 _ _ _ _ H4 H8 H0). rewrite Htlp, <- Htlp.
      destruct H6 as [? [? ?]]. destruct_match H2; inversion H2. subst x. clear H2.
      specialize (IHvs _ _ _ _ H7 H1 H10 H11). destruct IHvs as [? [? ?]].
      destruct_match H2; inversion H2. subst x. clear H2. solve_ex_sim; auto.
  - inv H3. inv H1. inv H2. simpl. solve_ex_sim. auto.
  - remember (fix eval_binary_op_eq_struct' (l1 l2 : Ops.Fields Val) {struct l1} :
              option bool :=
            match l1 with
            | [] => match l2 with
                    | [] => Some true
                    | _ :: _ => None
                    end
            | (k1, v1) :: l1' =>
                match l2 with
                | [] => None
                | (k2, v2) :: l2' =>
                    if ~~ (k1 =? k2)
                    then None
                    else
                     match Ops.eval_binary_op_eq v1 v2 with
                     | Some b1 =>
                         match eval_binary_op_eq_struct' l1' l2' with
                         | Some b2 => Some (b1 && b2)
                         | None => None
                         end
                     | None => None
                     end
                end
            end) as eq_struct. rename Heqeq_struct into Hst.
    destruct_match H3. 1: inv H3. inversion H1. subst kvs v3. clear H1.
    inversion H2. subst kvs v4. clear H2. simpl. rewrite <- Hst.
    rewrite Bool.negb_false_iff in H4. apply andb_prop in H4. destruct H4.
    eapply all_values_key_unique in H1; eauto.
    eapply all_values_key_unique in H2; eauto. rewrite H1, H2. simpl. clear H1 H2.
    revert vs kvs' fields kvs'0 b H0 H3 H5 H6. induction vs; intros.
    + rewrite Hst in H3. destruct fields; inversion H3. subst b. inversion H5.
      inversion H6. rewrite Hst. solve_ex_sim. auto.
    + rewrite Hst, <- Hst in H3. destruct a as [k v1]. destruct fields. 1: inv H3.
      destruct p as [k2 v2]. inversion H0. subst x l. clear H0.
      destruct_match H3. 1: inv H3. rewrite Bool.negb_false_iff in H0.
      apply eqb_eq in H0. subst k2. destruct kvs'0. 1: inv H5. destruct kvs'.
      1: inv H6. destruct p as [k2 v3]. inversion H5. subst x l y l'. clear H5.
      simpl in H8. destruct H8. subst k2. destruct p0 as [k2 v4].
      inversion H6. subst x l y l'. clear H6. simpl in H8. destruct H8. subst k2.
      destruct_match H3. 2: inv H3. destruct_match H3; inversion H3. subst b.
      specialize (H4 _ _ _ _ H2 H1 H0). specialize (IHvs _ _ _ _ H7 H5 H10 H11).
      clear H0 H1 H2 H5 H7. rewrite Hst, <- Hst. rewrite eqb_refl. simpl.
      destruct H4 as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      destruct IHvs as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      solve_ex_sim. auto.
  - remember (fix eval_binary_op_eq_struct' (l1 l2 : Ops.Fields Val) {struct l1} :
              option bool :=
            match l1 with
            | [] => match l2 with
                    | [] => Some true
                    | _ :: _ => None
                    end
            | (k1, v1) :: l1' =>
                match l2 with
                | [] => None
                | (k2, v2) :: l2' =>
                    if ~~ (k1 =? k2)
                    then None
                    else
                     match Ops.eval_binary_op_eq v1 v2 with
                     | Some b1 =>
                         match eval_binary_op_eq_struct' l1' l2' with
                         | Some b2 => Some (b1 && b2)
                         | None => None
                         end
                     | None => None
                     end
                end
            end) as eq_struct. rename Heqeq_struct into Hst.
    destruct_match H3; inversion H3. subst b0; clear H3.
    destruct_match H4. 1: inv H4. inversion H1. subst kvs b0 v3. clear H1.
    inversion H2. subst kvs b0 v4. clear H2. simpl. rewrite <- Hst.
    rewrite Bool.negb_false_iff in H3. apply andb_prop in H3. destruct H3.
    eapply all_values_key_unique in H1; eauto.
    eapply all_values_key_unique in H2; eauto. rewrite H1, H2. simpl. clear H1 H2.
    clear H6 H7. revert vs kvs' fields kvs'0 b1 H0 H4 H9 H10. induction vs; intros.
    + rewrite Hst in H4. destruct fields; inversion H4. subst b1. inversion H9.
      inversion H10. rewrite Hst. solve_ex_sim. auto.
    + rewrite Hst, <- Hst in H4. destruct a as [k v1]. destruct fields. 1: inv H4.
      destruct p as [k2 v2]. inversion H0. subst x l. clear H0.
      destruct_match H4. 1: inv H4. rewrite Bool.negb_false_iff in H0.
      apply eqb_eq in H0. subst k2. destruct kvs'0. 1: inv H10. destruct kvs'.
      1: inv H9. destruct p as [k2 v3]. inversion H10. subst x l y l'. clear H10.
      simpl in H6. destruct H6. subst k2. destruct p0 as [k2 v4].
      inversion H9. subst x l y l'. clear H9. simpl in H7. destruct H7. subst k2.
      destruct_match H4. 2: inv H4. destruct_match H4; inversion H4. subst b1.
      specialize (H3 _ _ _ _ H2 H1 H0). specialize (IHvs _ _ _ _ H5 H6 H11 H8).
      clear H0 H1 H2 H5 H6. rewrite Hst, <- Hst. rewrite eqb_refl. simpl.
      destruct H3 as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      destruct IHvs as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      destruct_match H5; inversion H5. subst b3. clear H5.
      solve_ex_sim. auto.
  - remember (fix eval_binary_op_eq_struct' (l1 l2 : Ops.Fields Val) {struct l1} :
              option bool :=
            match l1 with
            | [] => match l2 with
                    | [] => Some true
                    | _ :: _ => None
                    end
            | (k1, v1) :: l1' =>
                match l2 with
                | [] => None
                | (k2, v2) :: l2' =>
                    if ~~ (k1 =? k2)
                    then None
                    else
                     match Ops.eval_binary_op_eq v1 v2 with
                     | Some b1 =>
                         match eval_binary_op_eq_struct' l1' l2' with
                         | Some b2 => Some (b1 && b2)
                         | None => None
                         end
                     | None => None
                     end
                end
            end) as eq_struct. rename Heqeq_struct into Hst.
    destruct_match H3. 1: inv H3. inversion H1. subst kvs v3. clear H1.
    inversion H2. subst kvs v4. clear H2. simpl. rewrite <- Hst.
    rewrite Bool.negb_false_iff in H4. apply andb_prop in H4. destruct H4.
    eapply all_values_key_unique in H1; eauto.
    eapply all_values_key_unique in H2; eauto. rewrite H1, H2. simpl. clear H1 H2.
    revert vs kvs' fields kvs'0 b H0 H3 H5 H6. induction vs; intros.
    + rewrite Hst in H3. destruct fields; inversion H3. subst b. inversion H5.
      inversion H6. rewrite Hst. solve_ex_sim. auto.
    + rewrite Hst, <- Hst in H3. destruct a as [k v1]. destruct fields. 1: inv H3.
      destruct p as [k2 v2]. inversion H0. subst x l. clear H0.
      destruct_match H3. 1: inv H3. rewrite Bool.negb_false_iff in H0.
      apply eqb_eq in H0. subst k2. destruct kvs'0. 1: inv H5. destruct kvs'.
      1: inv H6. destruct p as [k2 v3]. inversion H5. subst x l y l'. clear H5.
      simpl in H8. destruct H8. subst k2. destruct p0 as [k2 v4].
      inversion H6. subst x l y l'. clear H6. simpl in H8. destruct H8. subst k2.
      destruct_match H3. 2: inv H3. destruct_match H3; inversion H3. subst b.
      specialize (H4 _ _ _ _ H2 H1 H0). specialize (IHvs _ _ _ _ H7 H5 H10 H11).
      clear H0 H1 H2 H5 H7. rewrite Hst, <- Hst. rewrite eqb_refl. simpl.
      destruct H4 as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      destruct IHvs as [? [? ?]]. destruct_match H0; inversion H0. subst x. clear H0.
      solve_ex_sim. auto.
  - remember (fix eval_binary_op_eq_tuple (l1 l2 : list Val) {struct l1} : option bool :=
          match l1 with
          | [] => match l2 with
                  | [] => Some true
                  | _ :: _ => None
                  end
          | x1 :: l1' =>
              match l2 with
              | [] => None
              | x2 :: l2' =>
                  match Ops.eval_binary_op_eq x1 x2 with
                  | Some b1 =>
                      match eval_binary_op_eq_tuple l1' l2' with
                      | Some b2 => Some (b1 && b2)
                      | None => None
                      end
                  | None => None
                  end
              end
          end) as eq_tuple. rename Heqeq_tuple into Htlp.
    inversion H1. subst lv next0 v3. clear H1. inversion H2. subst lv next0 v4.
    clear H2. simpl. rewrite <- Htlp. destruct_match H3. 1: inv H3.
    pose proof (Forall2_Zlength H7). pose proof (Forall2_Zlength H6).
    rewrite <- H2, <- H4, H1. clear H1 H2 H4.
    revert vs headers lv' lv'0 b H0 H3 H6 H7. induction vs; intros.
    + rewrite Htlp in H3. destruct headers; inversion H3. subst b. clear H3.
      inversion H6. inversion H7. rewrite Htlp. solve_ex_sim; auto.
    + rewrite Htlp, <- Htlp in H3. destruct headers. 1: inv H3.
      destruct lv'0. 1: inv H6. destruct lv'. 1: inv H7. inversion H0. subst x l.
      clear H0. inversion H6. subst x l y l'. clear H6. inversion H7. subst x l y l'.
      clear H7. destruct_match H3. 2: inv H3. destruct_match H3. 2: inv H3.
      specialize (H4 _ _ _ _ H6 H8 H0). rewrite Htlp, <- Htlp.
      destruct H4 as [? [? ?]]. destruct_match H2; inversion H2. subst x. clear H2.
      specialize (IHvs _ _ _ _ H5 H1 H10 H11). destruct IHvs as [? [? ?]].
      destruct_match H2; inversion H2. subst x. clear H2. solve_ex_sim; auto.
  - destruct_match H3; inv H3. inv H1. inv H2. simpl. rewrite H0. solve_ex_sim. auto.
  - destruct (t =? typ_name) eqn:?H. 2: inv H3. apply eqb_eq in H0. subst typ_name.
    inv H1. inv H2. simpl. rewrite eqb_refl. eapply IHv1; eauto.
Qed.

Lemma bin_op_eq_neq: forall v1 v2 b,
    Ops.eval_binary_op Eq v1 v2 = Some (ValBaseBool b) <->
    Ops.eval_binary_op NotEq v1 v2 = Some (ValBaseBool (~~ b)).
Proof.
  simpl. intros. split; intros; destruct_match H0; inv H0; auto.
  rewrite <- (Bool.negb_involutive b0), <- (Bool.negb_involutive b), H3; auto.
Qed.

Lemma eval_binary_op_val_sim_noteq: forall v1 v2 v3 v4 result,
    Ops.eval_binary_op NotEq v1 v2 = Some result ->
    val_sim v1 v3 -> val_sim v2 v4 ->
    exists result', Ops.eval_binary_op NotEq v3 v4 = Some result' /\
                 val_sim result result'.
Proof.
  intros. assert (exists b, result = ValBaseBool (~~ b)). {
    simpl in H0. destruct_match H0; inv H0. exists b; auto. } destruct H3. subst.
  rewrite <- bin_op_eq_neq in H0.
  destruct (eval_binary_op_val_sim_eq _ _ _ _ _ H0 H1 H2) as [r [? ?]].
  assert (exists b, r = ValBaseBool b). {
    simpl in H3. destruct_match H3; inv H3. exists b; auto. } destruct H5. subst.
  rewrite bin_op_eq_neq in H3. rewrite H3. solve_ex_sim. auto.
Qed.

Definition eval_bin_op op v1 v2 :=
  match v1, v2 with
  | ValBaseBit bits1, ValBaseBit bits2 =>
      let (w1, n1) := BitArith.from_lbool bits1 in
      let (w2, n2) := BitArith.from_lbool bits2 in
      if (BinNat.N.eqb w1 w2) then Ops.eval_binary_op_bit op w1 n1 n2
      else None
  | ValBaseInt bits1, ValBaseInt bits2 =>
      let (w1, n1) := IntArith.from_lbool bits1 in
      let (w2, n2) := IntArith.from_lbool bits2 in
      if (BinNat.N.eqb w1 w2) then Ops.eval_binary_op_int op w1 n1 n2
      else None
  | ValBaseInteger n1, ValBaseInteger n2 =>
        Ops.eval_binary_op_integer op n1 n2
  | ValBaseBool b1, ValBaseBool b2 =>
        Ops.eval_binary_op_bool op b1 b2
  | _, _ => None
  end.

Lemma bin_op_small: forall op v1 v2,
    ~ In op [PlusPlus; Shl; Shr; Eq; NotEq] ->
    Ops.eval_binary_op op v1 v2 = eval_bin_op op v1 v2.
Proof.
  intros. destruct op; simpl; auto; exfalso; apply H0.
  - right. now left.
  - do 2 right. now left.
  - do 3 right. now left.
  - do 4 right. now left.
  - now left.
Qed.

Lemma eval_binary_op_val_sim: forall op v1 v2 v3 v4 result,
    ~ In op [Shl; Shr] ->
    Ops.eval_binary_op op v1 v2 = Some result ->
    val_sim v1 v3 -> val_sim v2 v4 ->
    exists result', Ops.eval_binary_op op v3 v4 = Some result' /\
                 val_sim result result'.
Proof.
  intros. destruct (in_dec opbin_eq_dec op [PlusPlus; Shl; Shr; Eq; NotEq]).
  - destruct i as [? | [? | [? | [? | [? | ? ]]]]]; subst.
    + eapply eval_binary_op_val_sim_plusplus; eauto.
    + exfalso. apply H0. now left.
    + exfalso. apply H0. right. now left.
    + eapply eval_binary_op_val_sim_eq; eauto.
    + eapply eval_binary_op_val_sim_noteq; eauto.
    + inv H4.
  - rewrite bin_op_small in *; auto. clear H0 n.
    destruct v1, v2; simpl in H1; try (now inv H1).
    + destruct op; simpl in H1; inv H1; inv H2; inv H3; simpl; solve_ex_sim; auto.
    + destruct op; simpl in H1; inv H1; inv H2; inv H3; simpl; try solve_ex_sim; auto.
      all: destruct_match H4; inv H4; solve_ex_sim.
    + destruct_match H1. 2: inv H1. inv H2. inv H3. simpl.
      pose proof (Forall2_Zlength H4). pose proof (Forall2_Zlength H5).
      rewrite <- H2, <- H3, H0.
      destruct op; simpl in H1; inv H1; simpl; try solve_ex_sim; auto;
        try apply Forall2_to_lbool. admit. admit.
    + destruct_match H1. 2: inv H1. inv H2. inv H3. simpl.
      pose proof (Forall2_Zlength H4). pose proof (Forall2_Zlength H5).
      rewrite <- H2, <- H3, H0.
      destruct op; simpl in H1; inv H1; simpl; try solve_ex_sim; auto;
        try apply Forall2_to_lbool.
Admitted.

Lemma sval_refine_liberal_binary:
  forall (op : OpBin) (v v0 : Sval) (largv rargv v1 : Val),
    ~ In op [Shl; Shr] ->
    Ops.eval_binary_op op largv rargv = Some v1 ->
    sval_to_val read_ndetbit v largv ->
    sval_to_val read_ndetbit v0 rargv ->
    sval_refine
      (val_to_liberal_sval
         (force ValBaseNull
                (Ops.eval_binary_op op (force_sval_to_val v) (force_sval_to_val v0))))
      (eval_val_to_sval v1).
Proof.
  intros.
  assert (val_sim largv (force_sval_to_val v)). {
        apply val_sim_on_top in H2. apply val_sim_sym in H2.
        eapply val_sim_trans; eauto. apply force_sval_to_val_val_sim. }
  assert (val_sim rargv (force_sval_to_val v0)). {
        apply val_sim_on_top in H3. apply val_sim_sym in H3.
        eapply val_sim_trans; eauto. apply force_sval_to_val_val_sim. }
  destruct (eval_binary_op_val_sim _ _ _ _ _ _ H0 H1 H4 H5) as [v1' [? ?]].
  rewrite H6. simpl. apply sval_refine_liberal. apply val_sim_sym in H7.
  eapply val_sim_trans; eauto. apply eval_val_to_sval_val_sim.
Qed.

Opaque in_dec.

Lemma eval_expr_sound' : forall ge p a expr sv,
  eval_expr ge p a expr = Some sv ->
  forall st, (mem_denote a) (fst st) ->
  forall sv', exec_expr ge read_ndetbit p st expr sv' ->
              sval_refine sv sv'.
Proof.
  intros ge p a expr. revert ge p a.
  induction expr using expr_ind; intros; simpl in H0; try now inversion H0.
  - inversion H0. subst. inversion H2. subst. apply sval_refine_refl.
  - destruct_match H0.
    + destruct l. 1: inversion H0. inversion H2; subst.
      * simpl in H13. unfold eval_read_var in H0. destruct st. simpl in *.
        eapply mem_denote_get in H1; eauto. red in H1. rewrite H13 in H1. auto.
      * rewrite H3 in H12; inversion H12.
    + inversion H2; subst. 1: rewrite H3 in H12; inversion H12.
      unfold loc_to_sval_const in H13. rewrite H0 in H13. inversion H13.
      apply sval_refine_refl.
  - destruct_match H0; [|inv H0].
    inv H2.
    specialize (IHexpr _ _ _ _ ltac:(eassumption) _ ltac:(eassumption) _ ltac:(eassumption)).
    destruct_match H0; [|inv H0].
    2 : {
      inv IHexpr; inv H2; inv H14.
    }
    destruct p0 as [bitsbl' wn'].
    inv H0.
    constructor. apply Ops.Forall2_bitstring_slice.
    inv IHexpr; simpl in H2; inv H2; simpl in H14; inv H14; auto.
  - inversion H3. subst. simpl in H1. red.
    destruct (lift_option (map (eval_expr ge p a) vs)) eqn:?H; simpl in H1;
      inversion H1; subst; clear H1. constructor. clear H3.
    revert l H4 vs0 H11. induction vs; intros.
    + simpl in H4. inversion H4. inversion H11. constructor.
    + destruct vs0. 1: inversion H11. destruct l.
      * simpl in H4. destruct_match H4. 2: inversion H4.
        destruct_match H4; inversion H4.
      * simpl in H4. destruct_match H4. 2: inversion H4.
        destruct_match H4; inversion H4. subst. clear H4. inv H0. inv H11.
        constructor. 2: now apply IHvs. eapply H6; eauto.
  - destruct_match H0; inv H0.
    assert (Some (build_abs_unary_op (Ops.eval_unary_op op) v) = Some sv). {
      destruct op; auto.
    }
    clear H5; inv H0.
    inv H2. eapply IHexpr in H11; eauto.
    assert (sval_to_val read_ndetbit v argv). {
      eapply exec_val_trans; eauto. clear. repeat intro. inv H; auto. constructor. }
    clear H11 H12. rewrite val_to_sval_iff in H14. subst sv'.
    unfold build_abs_unary_op. destruct (eval_sval_to_val v) eqn:?H.
    + eapply sval_to_val_Some in H2; eauto. subst v1. rewrite H13. simpl.
      apply sval_refine_refl.
    + assert (val_sim argv (force_sval_to_val v)). {
        apply val_sim_on_top in H0. apply val_sim_sym in H0.
        eapply val_sim_trans; eauto. apply force_sval_to_val_val_sim. }
      destruct (eval_unary_op_val_sim _ _ _ _ H13 H4) as [newv' [? ?]].
      rewrite H5. simpl. apply sval_refine_liberal. apply val_sim_sym in H6.
      eapply val_sim_trans; eauto. apply eval_val_to_sval_val_sim.
  - destruct (in_dec opbin_eq_dec op [Shl; Shr]).
    1: inv H0. destruct_match H0. 2: inv H0.
    destruct_match H0; inv H0.
    assert (Some (build_abs_binary_op (Ops.eval_binary_op op) v v0) = Some sv). {
      destruct op; auto.
    }
    clear H6; inv H0.
    inv H2. simpl in *. eapply IHexpr1 in H12; eauto.
    eapply IHexpr2 in H14; eauto.
    assert (sval_to_val read_ndetbit v largv). {
      eapply exec_val_trans; eauto. clear. repeat intro. inv H; auto. constructor. }
    assert (sval_to_val read_ndetbit v0 rargv). {
      eapply exec_val_trans; eauto. clear. repeat intro. inv H; auto. constructor. }
    clear H15 H16 H12 H14. rewrite val_to_sval_iff in H18. subst sv'.
    unfold build_abs_binary_op. destruct (eval_sval_to_val v) eqn:?H.
    + destruct (eval_sval_to_val v0) eqn:?H.
      * eapply sval_to_val_Some in H5, H6; eauto. subst. rewrite H17. simpl.
        apply sval_refine_refl.
      * eapply sval_refine_liberal_binary; eauto.
    + eapply sval_refine_liberal_binary; eauto.
  - destruct_match H0. 2: inversion H0. destruct_match H0; inv H0. inv H2.
    rewrite H4 in H14. inv H14. red in H16. red in H13. eapply IHexpr in H11; eauto.
    red in H11. assert (sval_to_val read_ndetbit v oldv). {
      eapply exec_val_trans; eauto. clear. repeat intro. inv H; auto. constructor. }
    clear H11 H13. unfold build_abs_unary_op. rewrite val_to_sval_iff in H16.
    subst sv'. destruct (eval_sval_to_val v) eqn:?H.
    + eapply sval_to_val_Some in H2; eauto. subst v0. rewrite H15. simpl.
      apply sval_refine_refl.
    + assert (val_sim oldv (force_sval_to_val v)). {
        apply val_sim_on_top in H0. apply val_sim_sym in H0.
        eapply val_sim_trans; eauto. apply force_sval_to_val_val_sim. }
      destruct (eval_cast_val_sim _ _ _ _ H15 H5) as [newv' [? ?]].
      rewrite H6. simpl. apply sval_refine_liberal. apply val_sim_sym in H7.
      eapply val_sim_trans; eauto. apply eval_val_to_sval_val_sim.
  - destruct_match H0. 2: inversion H0. destruct_match H0; inversion H0. clear H6.
    destruct_match H0.
    + destruct_match H0; inv H0. inv H2; rewrite H3 in H12; inv H12.
      rewrite H13 in H6. simpl in H6. rewrite H6 in H14. inv H14. constructor.
      apply exec_val_refl. apply bit_refine_refl.
    + inv H0. inv H2; rewrite H3 in H11; inv H11. constructor.
  - destruct_match H0; inv H0.
    inv H2.
    eapply IHexpr in H11; eauto.
    apply get_sound in H12.
    rewrite <- H12.
    apply sval_refine_get; auto.
Qed.

Transparent in_dec.

Lemma eval_expr_sound : forall ge p a_mem a_ext expr sv,
  eval_expr ge p a_mem expr = Some sv ->
  hoare_expr ge p (MEM a_mem (EXT a_ext)) expr sv.
Proof.
  unfold hoare_expr; intros.
  eapply eval_expr_sound'; eauto.
  destruct st; destruct H1; eauto.
Qed.

Hint Resolve eval_expr_sound : hoare.

Definition eval_exprs (ge : genv) (p : path) (a : mem_assertion) (exprs : list Expression) : option (list Sval) :=
  lift_option (map (eval_expr ge p a) exprs).

Lemma hoare_exprs_det_cons' : forall ge (p : path) (pre : assertion) (expr : Expression) (exprs : list Expression)
    (sv : Sval) (svs : list Sval),
  hoare_expr_det' ge p pre expr sv ->
  hoare_exprs_det' ge p pre exprs svs ->
  hoare_exprs_det' ge p pre (expr :: exprs) (sv :: svs).
Proof.
  unfold hoare_expr_det', hoare_exprs_det'; intros.
  inv H3. inv H4. inv H5.
  constructor; eauto.
  - eapply H0; eauto.
    econstructor; eauto.
  - eapply H1; eauto.
    econstructor; eauto.
Qed.

Lemma eval_exprs_sound' : forall ge p a_mem a_ext exprs svs,
  eval_exprs ge p a_mem exprs = Some svs ->
  hoare_exprs_det' ge p (MEM a_mem (EXT a_ext)) exprs svs.
Proof.
  induction exprs; intros.
  - inv H0.
    unfold hoare_exprs_det'; intros.
    inv H1. inv H2. inv H3.
    constructor.
  - inv H0.
    apply lift_option_inv in H2.
    destruct svs; inv H2.
    apply hoare_exprs_det_cons'.
    + eapply hoare_expr_det'_intro; eauto.
      eapply eval_expr_sound; eauto.
    + eapply IHexprs.
      unfold eval_exprs.
      rewrite H3.
      apply lift_option_map_some.
Qed.

Lemma hoare_exprs_det_cons : forall ge (p : path) (pre : assertion) (expr : Expression) (exprs : list Expression)
    (sv : Sval) (svs : list Sval),
  hoare_expr_det ge p pre expr sv ->
  hoare_exprs_det ge p pre exprs svs ->
  hoare_exprs_det ge p pre (expr :: exprs) (sv :: svs).
Proof.
  unfold hoare_expr_det, hoare_exprs_det; intros.
  inv H3. inv H5. inv H6. inv H4.
  constructor; eauto.
  - eapply H0; eauto.
    econstructor; eauto.
  - eapply H1; eauto.
    econstructor; eauto.
Qed.

Lemma eval_exprs_sound : forall ge p a_mem a_ext exprs svs,
  eval_exprs ge p a_mem exprs = Some svs ->
  hoare_exprs_det ge p (MEM a_mem (EXT a_ext)) exprs svs.
Proof.
  induction exprs; intros.
  - inv H0.
    unfold hoare_exprs_det; intros.
    inv H1. inv H3. inv H4. inv H2.
    constructor.
  - inv H0.
    apply lift_option_inv in H2.
    destruct svs; inv H2.
    apply hoare_exprs_det_cons.
    + eapply hoare_expr_det_intro; eauto.
      eapply eval_expr_sound; eauto.
    + eapply IHexprs.
      unfold eval_exprs.
      rewrite H3.
      apply lift_option_map_some.
Qed.

Definition dummy_name := BareName (P4String.Build_t tags_t default "").
Global Opaque dummy_name.

(* Evaluate lvalue expressions. *)
Fixpoint eval_lexpr (ge : genv) (p : path) (a : mem_assertion) (expr : Expression) : option Lval :=
  match expr with
  | MkExpression _ (ExpName _ loc) _ _ =>
      Some (ValLeftName loc)
  | MkExpression _ (ExpExpressionMember expr member) _ _ =>
      match eval_lexpr ge p a expr with
      | Some lv =>
          if (String.eqb (P4String.str member) "next") then
            None
          else
            Some (ValLeftMember lv (P4String.str member))
      | None => None
      end
  | _ => None
  end.

Lemma eval_lexpr_sound : forall ge p a_mem a_ext expr lv,
  eval_lexpr ge p a_mem expr = Some lv ->
  hoare_lexpr ge p (MEM a_mem (EXT a_ext)) expr lv.
Proof.
  unfold hoare_lexpr; intros.
  generalize dependent lv.
  induction H2; intros; try solve [inv H0].
  - inv H0. simpl; auto.
  - simpl in H3. rewrite H0 in H3.
    destruct (eval_lexpr ge this a_mem expr) as [lv_base |]. 2 : inv H3.
    specialize (IHexec_lexpr ltac:(auto) _ ltac:(eauto)).
    inv H3.
    sfirstorder.
  - simpl in H5. rewrite H0 in H5. destruct (eval_lexpr ge this a_mem expr); inv H5.
  - inv H5.
  - inv H5.
Qed.

Definition eval_write_var (a : mem_assertion) (p : path) (sv : Sval) : mem_assertion :=
  AList.set_some a p sv.

Lemma mem_assertion_set_disjoint : forall a_mem p sv m,
  ~In p (map fst a_mem) ->
  mem_denote a_mem m ->
  mem_denote a_mem (PathMap.set p sv m).
Proof.
  intros.
  induction a_mem.
  - auto.
  - split.
    + destruct a; unfold mem_satisfies_unit.
      rewrite PathMap.get_set_diff. 2 : { simpl in H0. tauto. }
      apply (proj1 H1).
    + apply IHa_mem.
      * simpl in H0; tauto.
      * destruct H1. auto.
Qed.

Lemma eval_write_var_sound : forall a_mem a_ext p sv a_mem',
  NoDup (map fst a_mem) ->
  eval_write_var a_mem p sv = a_mem' ->
  hoare_write_var (MEM a_mem (EXT a_ext)) p sv (MEM a_mem' (EXT a_ext)).
Proof.
  unfold hoare_write_var; intros.
  destruct st as [m es]; destruct st' as [m' es'].
  inv H4. destruct H2.
  split; auto.
  induction a_mem.
  - split; auto.
    unfold mem_satisfies_unit. rewrite PathMap.get_set_same; auto.
  - simpl. destruct H1.
    destruct a as [p' sv''].
    destruct (EquivDec.list_eqdec EquivUtil.StringEqDec p p') as [H_p | H_p].
    + red in H_p.
      split.
      * simpl. rewrite PathMap.get_set_same; auto.
      * apply mem_assertion_set_disjoint; auto.
        inv H0; auto.
    + cbv in H_p.
      split.
      * unfold mem_satisfies_unit.
        rewrite PathMap.get_set_diff; auto.
      * apply IHa_mem; auto.
        inv H0; auto.
Qed.

Definition eval_write_vars (a : mem_assertion) (ps : list path) (svs : list Sval) : mem_assertion :=
  fold_left (fun a '(p, sv) => eval_write_var a p sv) (combine ps svs) a.

Lemma eval_write_var_key_range : forall a p sv x,
  In x (map fst (eval_write_var a p sv)) ->
  x = p \/ In x (map fst a).
Proof.
  intros. induction a.
  - inv H0; auto.
  - destruct a as [p' sv'].
    simpl in H0. destruct (EquivDec.list_eqdec EquivUtil.StringEqDec p p') as [H_p | H_p].
    + red in H_p. subst.
      auto.
    + cbv in H_p.
      destruct H0.
      * simpl. auto.
      * hauto.
Qed.

Lemma eval_write_var_preserve_NoDup : forall a p sv,
  NoDup (map fst a) ->
  NoDup (map fst (eval_write_var a p sv)).
Proof.
  intros. induction a.
  - repeat constructor. auto.
  - destruct a as [p' sv'].
    simpl. destruct (EquivDec.list_eqdec EquivUtil.StringEqDec p p') as [H_p | H_p].
    + red in H_p. subst.
      apply H0.
    + cbv in H_p.
      inv H0. specialize (IHa ltac:(auto)).
      simpl. constructor.
      * intro. apply eval_write_var_key_range in H0.
        hauto.
      * auto.
Qed.

Lemma eval_write_vars_sound' : forall a_mem a_ext ps svs a_mem',
  length ps = length svs ->
  NoDup (map fst a_mem) ->
  eval_write_vars a_mem ps svs = a_mem' ->
  hoare_write_vars' (MEM a_mem (EXT a_ext)) ps svs (MEM a_mem' (EXT a_ext)).
Proof.
  intros until ps. generalize a_mem. induction ps; intros.
  - destruct svs; try solve [inv H0].
    subst; econstructor.
  - destruct svs; try solve [inv H0].
    econstructor.
    + apply eval_write_var_sound; auto.
    + apply IHps; auto.
      apply eval_write_var_preserve_NoDup; auto.
Qed.

Lemma eval_write_vars_sound : forall a_mem a_ext ps svs a_mem',
  length ps = length svs ->
  NoDup (map fst a_mem) ->
  eval_write_vars a_mem ps svs = a_mem' ->
  hoare_write_vars (MEM a_mem (EXT a_ext)) ps svs (MEM a_mem' (EXT a_ext)).
Proof.
  intros; apply hoare_write_vars_intro, eval_write_vars_sound'; auto.
Qed.

Lemma hoare_func_copy_in_intro : forall a_arg a_mem a_ext params a_mem',
  length (filter_in params) = length a_arg ->
  NoDup (map fst a_mem) ->
  eval_write_vars a_mem (filter_in params) a_arg = a_mem' ->
  hoare_func_copy_in (ARG a_arg (MEM a_mem (EXT a_ext))) params (MEM a_mem' (EXT a_ext)).
Proof.
  unfold hoare_func_copy_in. intros.
  eapply eval_write_vars_sound in H1. 2, 3 : eassumption.
  destruct H3; eauto.
Qed.

Fixpoint eval_read (a : mem_assertion) (lv : Lval) : option Sval :=
  match lv with
  | ValLeftName (LInstance p) => eval_read_var a p
  | ValLeftName (LGlobal _) => None
  | ValLeftMember lv' member => option_map (get member) (eval_read a lv')
  | ValLeftBitAccess lv' hi lo => None (* TODO *)
  | ValLeftArrayAccess lv' pos => None (* TODO *)
  end.

Lemma eval_read_sound : forall a_mem a_ext lv sv,
  eval_read a_mem lv = Some sv ->
  hoare_read (MEM a_mem (EXT a_ext)) lv sv.
Proof.
  induction lv; unfold hoare_read; intros.
  - destruct loc; only 1 : inv H0.
    inv H2.
    eapply eval_read_var_sound; eauto.
  - simpl in H0.
    destruct (eval_read a_mem lv) eqn:?. 2 : inv H0.
    inv H2. inv H0.
    apply get_sound in H8. subst.
    apply sval_refine_get.
    eapply IHlv; eauto.
  - inv H0.
  - inv H0.
Qed.

Definition option_join {A} (ooa : option (option A)) : option A :=
  match ooa with
  | Some (Some a) => Some a
  | _ => None
  end.

Fixpoint eval_write (a : mem_assertion) (lv : Lval) (sv : Sval) : option mem_assertion :=
  match lv with
  | ValLeftName (LInstance p) => Some (eval_write_var a p sv)
  | ValLeftName (LGlobal _) => None
  | ValLeftMember lv' member =>
      option_join (option_map (eval_write a lv') (option_map (update member sv) (eval_read a lv')))
  | ValLeftBitAccess lv' hi lo => None (* TODO *)
  | ValLeftArrayAccess lv' pos => None (* TODO *)
  end.

Lemma all_values_set_some_rel : forall {A} rel (kvl kvl' : AList.StringAList A) f v new_kvl v' new_kvl',
  AList.all_values rel kvl kvl' ->
  AList.set kvl f v = Some new_kvl ->
  AList.set kvl' f v' = Some new_kvl' ->
  rel v v' ->
  AList.all_values rel new_kvl new_kvl'.
Proof.
  intros * H0. revert new_kvl new_kvl'.
  induction H0; intros.
  - inv H0.
  - destruct x as [kx vx]; destruct y as [ky vy].
    destruct H0. simpl in H0. subst ky.
    simpl in H2, H3.
    destruct (EquivUtil.StringEqDec f kx).
    + inv H2; inv H3.
      constructor; auto.
    + destruct (AList.set l f v); inv H2.
      destruct (AList.set l' f v'); inv H3.
      constructor. eauto.
      eapply IHForall2; eauto.
Qed.

Lemma Some_is_some : forall {A} x (y : A),
  x = Some y ->
  is_some x.
Proof.
  intros. rewrite H0. auto.
Qed.

Lemma all_values_set_some_is_some : forall {A} rel (kvl kvl' : AList.StringAList A) f v new_kvl v',
  AList.all_values rel kvl kvl' ->
  AList.set kvl f v = Some new_kvl ->
  is_some (AList.set kvl' f v').
Proof.
  intros. apply Some_is_some in H1.
  rewrite <- AList.get_set_is_some in H1 |- *.
  erewrite all_values_get_is_some in H1; eauto.
Qed.

Lemma all_values_set_some_is_some' : forall {A} rel (kvl kvl' : AList.StringAList A) f v new_kvl' v',
  AList.all_values rel kvl kvl' ->
  AList.set kvl' f v' = Some new_kvl' ->
  is_some (AList.set kvl f v).
Proof.
  intros. apply Some_is_some in H1.
  rewrite <- AList.get_set_is_some in H1 |- *.
  erewrite all_values_get_is_some; eauto.
Qed.

Lemma all_values_set_some_rel' : forall {A} rel (kvl kvl' : AList.StringAList A) f v new_kvl' v' dummy_new_kvl,
  AList.all_values rel kvl kvl' ->
  AList.set kvl' f v' = Some new_kvl' ->
  rel v v' ->
  AList.all_values rel (force dummy_new_kvl (AList.set kvl f v)) new_kvl'.
Proof.
  intros.
  destruct (AList.set kvl f v) eqn:H_set. 2 : {
    eapply all_values_set_some_is_some' with (v := v) in H1. 2 : apply H0.
    rewrite H_set in H1. inv H1.
  }
  eapply all_values_set_some_rel; eauto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_case1 : forall bs,
  Forall2 bit_refine (map (fun _ : option bool => None) bs) bs.
Proof.
  induction bs.
  - constructor.
  - constructor; eauto.
    constructor.
Qed.

Lemma sval_refine_uninit_sval_of_sval_case2 : forall vs,
  Forall (fun sv : Sval => sval_refine (uninit_sval_of_sval None sv) sv) vs ->
  Forall2 sval_refine (map (uninit_sval_of_sval None) vs) vs.
Proof.
  induction 1.
  - constructor.
  - constructor; eauto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_case3 : forall (vs : AList.StringAList Sval),
  Forall (fun '(_, sv) => sval_refine (uninit_sval_of_sval None sv) sv) vs ->
  AList.all_values sval_refine (kv_map (uninit_sval_of_sval None) vs) vs.
Proof.
  induction 1.
  - constructor.
  - destruct x; constructor; eauto.
Qed.

Lemma sval_refine_uninit_sval_of_sval : forall sv,
  sval_refine (uninit_sval_of_sval None sv) sv.
Proof.
  induction sv using custom_ValueBase_ind; constructor; eauto.
  1, 7 : constructor.
  1, 2, 3 : apply sval_refine_uninit_sval_of_sval_case1.
  1, 5 : apply sval_refine_uninit_sval_of_sval_case2; auto.
  1, 2, 3 : apply sval_refine_uninit_sval_of_sval_case3; auto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_eq_case1 : forall bs1 bs2,
  Forall2 bit_refine bs1 bs2 ->
  (map (fun _ : option bool => @None bool) bs1) = (map (fun _ : option bool => None) bs2).
Proof.
  induction 1.
  - auto.
  - simpl; f_equal; auto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_eq_case2 : forall b vs1 vs2,
  Forall2 sval_refine vs1 vs2 ->
  Forall2 (fun sv1 sv2 : Sval => uninit_sval_of_sval b sv1 = uninit_sval_of_sval b sv2) vs1 vs2 ->
  map (uninit_sval_of_sval b) vs1 = map (uninit_sval_of_sval b) vs2.
Proof.
  induction 1; intros.
  - auto.
  - inv H2; simpl; f_equal; auto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_eq_case3 : forall b (vs1 vs2 : AList.StringAList Sval),
  AList.all_values sval_refine vs1 vs2 ->
  AList.all_values (fun sv1 sv2 : Sval => uninit_sval_of_sval b sv1 = uninit_sval_of_sval b sv2) vs1 vs2 ->
  kv_map (uninit_sval_of_sval b) vs1 = kv_map (uninit_sval_of_sval b) vs2.
Proof.
  induction 1; intros.
  - auto.
  - destruct x; destruct y; inv H2.
    destruct H6; simpl; f_equal; auto.
    f_equal; auto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_eq : forall b sv1 sv2,
  sval_refine sv1 sv2 ->
  uninit_sval_of_sval b sv1 = uninit_sval_of_sval b sv2.
Proof.
  induction 1 using custom_exec_val_ind; simpl; f_equal; auto.
  1, 2, 3 : apply sval_refine_uninit_sval_of_sval_eq_case1; auto.
  1, 5 : apply sval_refine_uninit_sval_of_sval_eq_case2; auto.
  1, 2, 3 : apply sval_refine_uninit_sval_of_sval_eq_case3; auto.
Qed.

Lemma sval_refine_uninit_sval_of_sval_trans : forall b sv1 sv2,
  sval_refine sv1 sv2 ->
  sval_refine (uninit_sval_of_sval b sv1) (uninit_sval_of_sval b sv2).
Proof.
  intros.
  hauto use: sval_refine_uninit_sval_of_sval_eq, sval_refine_refl.
Qed.

Lemma all_values_uninit_sval_of_sval_trans : forall b (kvs kvs' : AList.StringAList Sval),
  AList.all_values sval_refine kvs kvs' ->
  AList.all_values sval_refine (kv_map (uninit_sval_of_sval b) kvs)
    (kv_map (uninit_sval_of_sval b) kvs').
Proof.
  induction 1; intros.
  - constructor.
  - destruct x; destruct y; destruct H0.
    constructor; auto.
    split; auto.
    apply sval_refine_uninit_sval_of_sval_trans; auto.
Qed.

Definition osval_refine := EquivUtil.relop sval_refine.

Lemma sval_refine_havoc_header : forall update_is_valid update_is_valid' sv sv',
  (forall b b',
    bit_refine b b' ->
    bit_refine (update_is_valid b) (update_is_valid' b')) ->
  sval_refine sv sv' ->
  osval_refine (havoc_header update_is_valid sv) (havoc_header update_is_valid' sv').
Proof.
  intros * H_update_is_valid H_sval_refine.
  inv H_sval_refine; constructor.
  constructor; auto.
  apply all_values_uninit_sval_of_sval_trans; auto.
Qed.

Lemma sval_refine_kv_map_havoc_header : forall update_is_valid update_is_valid' (kvs kvs' : AList.StringAList Sval),
  (forall b b',
    bit_refine b b' ->
    bit_refine (update_is_valid b) (update_is_valid' b')) ->
  AList.all_values sval_refine kvs kvs' ->
  EquivUtil.relop (AList.all_values sval_refine)
    (lift_option_kv (kv_map (havoc_header update_is_valid) kvs))
    (lift_option_kv (kv_map (havoc_header update_is_valid') kvs')).
Proof.
  intros * H_update_is_valid H_all_values.
  induction H_all_values.
  - repeat constructor.
  - inv IHH_all_values.
    + simpl. rewrite <- H2. rewrite <- H3.
      destruct (kv_map_func (havoc_header update_is_valid) x) as [? []];
      destruct (kv_map_func (havoc_header update_is_valid') y) as [? []];
      constructor.
    + simpl. rewrite <- H1. rewrite <- H2.
      destruct x; destruct y; destruct H0.
      apply sval_refine_havoc_header with update_is_valid update_is_valid' _ _ in H4; auto.
      simpl; inv H4; constructor.
      constructor; auto.
Qed.

Lemma lift_option_kv_inv : forall {A} (xl : AList.StringAList (option A)) (al :  AList.StringAList A),
  lift_option_kv xl = Some al ->
  xl = kv_map Some al.
Proof.
  induction xl; intros.
  - inversion H0. auto.
  - destruct a as [? []].
    + simpl in H0. destruct (lift_option_kv xl).
      * inversion H0. simpl; f_equal; auto.
      * inversion H0.
    + inversion H0.
Qed.

Lemma update_sound : forall sv f f_sv sv' abs_sv abs_f_sv,
  sval_refine abs_sv sv ->
  sval_refine abs_f_sv f_sv ->
  update_member sv f f_sv sv' ->
  sval_refine (update f abs_f_sv abs_sv) sv'.
Proof.
  induction 3.
  - inv H0.
    constructor.
    eapply all_values_set_some_rel'; eauto.
  - inv H2; inv H0.
    + inv H5; simpl.
      * constructor. 1 : constructor.
        eapply all_values_set_some_rel'; eauto.
        eapply sval_refine_trans.
        --apply sval_refine_uninit_sval_of_sval.
        --auto.
      * constructor. 1 : constructor.
        eapply all_values_set_some_rel'; eauto.
    + inv H5; simpl.
      * constructor. 1 : constructor.
        eapply all_values_set_some_rel'; eauto.
        apply sval_refine_uninit_sval_of_sval_trans. auto.
      * constructor. 1 : constructor.
        eapply all_values_set_some_rel'; eauto.
        apply sval_refine_uninit_sval_of_sval_trans. auto.
    + inv H5; simpl.
      * constructor. 1 : constructor.
        eapply all_values_set_some_rel'; eauto.
        apply sval_refine_uninit_sval_of_sval_trans. auto.
  - inv H2; inv H0; inv H1; inv H6.
    2 : destruct b0.
    + (* When the abstract is_valid is None: *)
      simpl.
      destruct is_valid as [[] | ].
      * unfold update_union_member in H4.
        destruct (lift_option_kv (kv_map (havoc_header _) fields)) eqn:H0; only 2 : inv H4.
        assert (EquivUtil.relop (AList.all_values sval_refine)
          (lift_option_kv (kv_map (havoc_header (fun _ => None)) kvs))
          (lift_option_kv (kv_map (havoc_header (fun _ => Some false)) fields))). {
          apply sval_refine_kv_map_havoc_header; auto.
          constructor.
        }
        rewrite H0 in H1.
        inv H1; try discriminate.
        constructor. simpl.
        eapply all_values_set_some_rel'; eauto.
        constructor; auto.
        constructor.
      * unfold update_union_member in H4.
        destruct (lift_option_kv (kv_map (havoc_header _) fields)) eqn:H0; only 2 : inv H4.
        assert (EquivUtil.relop (AList.all_values sval_refine)
          (lift_option_kv (kv_map (havoc_header (fun _ => None)) kvs))
          (lift_option_kv (kv_map (havoc_header id) fields))). {
          apply sval_refine_kv_map_havoc_header; auto.
          constructor.
        }
        rewrite H0 in H1.
        inv H1; try discriminate.
        constructor. simpl.
        eapply all_values_set_some_rel'; eauto.
        constructor; auto.
        constructor.
      * unfold update_union_member in H4.
        destruct (lift_option_kv (kv_map (havoc_header _) fields)) eqn:H0; only 2 : inv H4.
        assert (EquivUtil.relop (AList.all_values sval_refine)
          (lift_option_kv (kv_map (havoc_header (fun _ => None)) kvs))
          (lift_option_kv (kv_map (havoc_header id) fields))). {
          apply sval_refine_kv_map_havoc_header; auto.
          constructor.
        }
        rewrite H0 in H1.
        inv H1; try discriminate.
        constructor. simpl.
        eapply all_values_set_some_rel'; eauto.
        constructor; auto.
        constructor.
    + simpl.
      unfold update_union_member in H4.
      destruct (lift_option_kv (kv_map (havoc_header _) fields)) eqn:H0; only 2 : inv H4.
      assert (EquivUtil.relop (AList.all_values sval_refine)
        (lift_option_kv (kv_map (havoc_header (fun _ => Some false)) kvs))
        (lift_option_kv (kv_map (havoc_header (fun _ => Some false)) fields))). {
        apply sval_refine_kv_map_havoc_header; auto.
        constructor.
      }
      rewrite H0 in H1.
      inv H1; try discriminate.
      constructor. simpl.
      eapply all_values_set_some_rel'; eauto.
      constructor; auto.
      constructor.
    + simpl.
      unfold update_union_member in H4.
      destruct (lift_option_kv (kv_map (havoc_header _) fields)) eqn:H0; only 2 : inv H4.
      assert (EquivUtil.relop (AList.all_values sval_refine)
        (lift_option_kv (kv_map (havoc_header id) kvs))
        (lift_option_kv (kv_map (havoc_header id) fields))). {
        apply sval_refine_kv_map_havoc_header; auto.
      }
      rewrite H0 in H1.
      inv H1; try discriminate.
      constructor. simpl.
      eapply all_values_set_some_rel'; eauto.
      constructor; auto.
      constructor.
Qed.

Lemma eval_write_sound : forall a_mem a_ext lv sv a_mem',
  NoDup (map fst a_mem) ->
  eval_write a_mem lv sv = Some a_mem' ->
  hoare_write (MEM a_mem (EXT a_ext)) lv sv (MEM a_mem' (EXT a_ext)).
Proof.
  induction lv; unfold hoare_write; intros.
  - destruct loc; only 1 : inv H1.
    inv H1. inv H4.
    eapply eval_write_var_sound; eauto.
  - simpl in H1.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H1.
    simpl in H1.
    destruct (eval_write a_mem lv (update name sv v)) eqn:H_eval_write. 2 : inv H1.
    inv H4.
    pose proof (eval_read_sound _ _ _ _ H_eval_read _ _ ltac:(eassumption) ltac:(eassumption)).
    epose proof (update_sound _ _ _ _ _ _ H4 H3 ltac:(eassumption)).
    inv H1.
    eapply IHlv; eauto.
  - inv H1.
  - inv H1.
Qed.

Hint Resolve eval_write_sound : hoare.

Lemma eval_write_preserve_NoDup : forall (a : mem_assertion) (lv : Lval) sv a',
  NoDup (map fst a) ->
  eval_write a lv sv = Some a' ->
  NoDup (map fst a').
Proof.
  induction lv; intros.
  - destruct loc; only 1 : inv H1.
    inv H1.
    auto using eval_write_var_preserve_NoDup.
  - simpl in H1.
    destruct (eval_read a lv) eqn:H_eval_read. 2 : inv H1.
    simpl in H1.
    destruct (eval_write a lv (update name sv v)) eqn:H_eval_write. 2 : inv H1.
    inv H1.
    eapply IHlv; eauto.
  - inv H1.
  - inv H1.
Qed.

Definition eval_arg (ge : genv) (p : path) (a : mem_assertion) (arg : option Expression)
    (dir : direction) : option argument :=
  match arg, dir with
  | Some arg, Typed.In =>
      match eval_expr ge p a arg with
      | Some sv => Some (Some sv, None)
      | _ => None
      end
  | Some arg, Out =>
      match eval_lexpr ge p a arg with
      | Some lv => Some (None, Some lv)
      | _ => None
      end
  | None, Out =>
      Some (None, None)
  | Some arg, InOut =>
      match eval_lexpr ge p a arg with
      | Some lv =>
          match eval_read a lv with
          | Some sv => Some (Some sv, Some lv)
          | _ => None
          end
      | _ => None
      end
  | _, _ => None
  end.

Lemma eval_arg_sound : forall ge p a_mem a_ext arg dir argval,
  eval_arg ge p a_mem arg dir = Some argval ->
  hoare_arg ge p (MEM a_mem (EXT a_ext)) arg dir argval.
Proof.
  unfold hoare_arg; intros.
  inv H2.
  - simpl in H0.
    destruct (eval_expr ge p a_mem expr) eqn:H_eval_expr. 2 : inv H0.
    inv H0.
    repeat constructor.
    eapply hoare_expr_det_intro; eauto.
    eapply eval_expr_sound; auto.
  - simpl in H0.
    inv H0.
    repeat constructor.
  - simpl in H0.
    destruct (eval_lexpr ge p a_mem expr) eqn:H_eval_lexpr. 2 : inv H0.
    inv H0.
    eapply eval_lexpr_sound in H_eval_lexpr.
    edestruct H_eval_lexpr; eauto.
    repeat constructor; eauto.
  - simpl in H0.
    destruct (eval_lexpr ge p a_mem expr) eqn:H_eval_lexpr. 2 : inv H0.
    destruct (eval_read a_mem v0) eqn:H_eval_read. 2 : inv H0.
    inv H0.
    eapply eval_lexpr_sound in H_eval_lexpr.
    edestruct H_eval_lexpr; eauto.
    eapply eval_read_sound in H_eval_read.
    repeat constructor; eauto.
    eapply sval_refine_trans. 2 : {
      eapply sval_to_val_to_sval; eauto.
    }
    subst v0.
    eapply H_eval_read; eauto.
Qed.

Definition eval_args (ge : genv) (p : path) (a : mem_assertion) (args : list (option Expression))
    (dirs : list direction) : option (list argument) :=
  lift_option (map (fun '(arg, dir) => eval_arg ge p a arg dir) (combine args dirs)).

Lemma eval_args_sound : forall ge p a_mem a_ext (args : list (option Expression)) dirs argvals,
  eval_args ge p a_mem args dirs = Some argvals ->
  hoare_args ge p (MEM a_mem (EXT a_ext)) args dirs argvals.
Proof.
  unfold hoare_args; intros.
  generalize dependent argvals.
  induction H2; intros.
  - inv H0. repeat constructor.
  - unfold eval_args in H4. simpl in H4.
    destruct (eval_arg ge p a_mem exp dir) eqn:H_eval_arg. 2 : inv H4.
    eapply eval_arg_sound in H_eval_arg.
    edestruct H_eval_arg; eauto; subst.
    simpl in H3; subst.
    change (lift_option _) with (eval_args ge p a_mem exps dirs) in H4.
    destruct (eval_args ge p a_mem exps dirs) eqn:H_eval_args. 2 : inv H4.
    edestruct IHexec_args; eauto.
    inv H4.
    repeat constructor; eauto.
Qed.

Lemma eval_sval_to_val_P4Bit : forall (w : N) (v : Z),
  eval_sval_to_val (P4Bit w v) = Some (ValBaseBit (P4Arith.to_lbool w v)).
Proof.
  intros.
  cbn.
  unfold to_loptbool.
  rewrite lift_option_map_some.
  reflexivity.
Qed.

End EvalExpr.

#[export] Hint Resolve eval_expr_sound eval_lexpr_sound eval_write_sound eval_arg_sound eval_args_sound : hoare.
#[export] Hint Rewrite abs_plus_bit abs_minus_bit abs_mul_bit abs_eq_bit abs_neq_bit
                       abs_plus_int abs_minus_int abs_mul_int abs_eq_int abs_neq_int : abs_ops.
