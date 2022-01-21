Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.P4String.
Require Import Poulet4.P4Arith.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Members.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.ExprInd.
Require Import Coq.ZArith.BinInt.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Local Open Scope string_scope.

Lemma locator_eqb_refl : forall (loc : Locator),
  locator_eqb loc loc.
Proof.
  destruct loc; simpl; auto.
Qed.

#[export] Hint Resolve locator_eqb_refl : core.

Lemma lift_option_map_some: forall {A: Type} (al: list A),
    lift_option (map Some al) = Some al.
Proof. intros. induction al; simpl; [|rewrite IHal]; easy. Qed.

Section EvalExpr.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation Expression := (@Expression tags_t).

Context `{@Target tags_t Expression}.

(* Convert Sval to Val only when all bits are known. *)
Fixpoint eval_sval_to_val (sval: Sval): option Val :=
  let fix sval_to_vals (sl: list Sval): option (list Val) :=
    match sl with
    | [] => Some []
    | s :: rest => match eval_sval_to_val s with
                   | None => None
                   | Some v => match sval_to_vals rest with
                               | Some l' => Some (v :: l')
                               | None => None
                               end
                   end
    end in
  let fix sval_to_avals (sl: AList.StringAList Sval): option (AList.StringAList Val) :=
    match sl with
    | [] => Some []
    | (k, s) :: rest => match eval_sval_to_val s with
                        | None => None
                        | Some v => match sval_to_avals rest with
                                    | None => None
                                    | Some l' => Some ((k, v) :: l')
                                    end
                        end
    end in
  match sval with
  | ValBaseNull => Some ValBaseNull
  | ValBaseBool (Some b) => Some (ValBaseBool b)
  | ValBaseBool None => None
  | ValBaseInteger z => Some (ValBaseInteger z)
  | ValBaseBit bits => match lift_option bits with
                       | Some l => Some (ValBaseBit l)
                       | None => None
                       end
  | ValBaseInt bits => match lift_option bits with
                       | Some l => Some (ValBaseInt l)
                       | None => None
                       end
  | ValBaseVarbit n bits => match lift_option bits with
                            | Some l => Some (ValBaseVarbit n l)
                            | None => None
                            end
  | ValBaseString s => Some (ValBaseString s)
  | ValBaseTuple l => match sval_to_vals l with
                      | Some l' => Some (ValBaseTuple l')
                      | None => None
                      end
  | ValBaseError err => Some (ValBaseError err)
  | ValBaseMatchKind k => Some (ValBaseMatchKind k)
  | ValBaseStruct l => match sval_to_avals l with
                       | Some l' => Some (ValBaseStruct l')
                       | None => None
                       end
  | ValBaseHeader _ None => None
  | ValBaseHeader l (Some b) => match sval_to_avals l with
                                | Some l' => Some (ValBaseHeader l' b)
                                | None => None
                                end
  | ValBaseUnion l => match sval_to_avals l with
                      | Some l' => Some (ValBaseUnion l')
                      | None => None
                      end
  | ValBaseStack l n => match sval_to_vals l with
                          | Some l' => Some (ValBaseStack l' n)
                          | None => None
                          end
  | ValBaseEnumField s1 s2 => Some (ValBaseEnumField s1 s2)
  | ValBaseSenumField s1 s => match eval_sval_to_val s with
                                 | None => None
                                 | Some v => Some (ValBaseSenumField s1 v)
                                 end
  end.

Definition opt_to_bool (op: option bool) : bool :=
  match op with
  | None => false
  | Some b => b
  end.

(* Convert Sval to Val, convert unknown bits to false. *)
Fixpoint force_sval_to_val (sval: Sval): Val :=
  let fix sval_to_vals (sl: list Sval): list Val :=
    match sl with
    | [] => []
    | s :: rest => force_sval_to_val s :: sval_to_vals rest
    end in
  let fix sval_to_avals (sl: AList.StringAList Sval): AList.StringAList Val :=
    match sl with
    | [] => []
    | (k, s) :: rest => (k, force_sval_to_val s) :: sval_to_avals rest
    end in
  match sval with
  | ValBaseNull => ValBaseNull
  | ValBaseBool (Some b) => ValBaseBool b
  | ValBaseBool None => ValBaseBool false
  | ValBaseInteger z => ValBaseInteger z
  | ValBaseBit bits => ValBaseBit (map opt_to_bool bits)
  | ValBaseInt bits => ValBaseInt (map opt_to_bool bits)
  | ValBaseVarbit n bits => ValBaseVarbit n (map opt_to_bool bits)
  | ValBaseString s => ValBaseString s
  | ValBaseTuple l => ValBaseTuple (sval_to_vals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (opt_to_bool valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l n => ValBaseStack (sval_to_vals l) n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s => ValBaseSenumField s1 (force_sval_to_val s)
  end.

Definition bool_to_none: bool -> option bool := fun _ => None.

Lemma map_bool_to_none: forall l,
    map bool_to_none l = repeat None (length l).
Proof.
  induction l; simpl; auto. unfold bool_to_none at 1. now rewrite IHl.
Qed.

(* Convert Val to Sval, but convert all bits to unknown. *)
Fixpoint val_to_liberal_sval (val: Val): Sval :=
  let fix sval_to_vals (sl: list Val): list Sval :=
    match sl with
    | [] => []
    | s :: rest => val_to_liberal_sval s :: sval_to_vals rest
    end in
  let fix sval_to_avals (sl: AList.StringAList Val): AList.StringAList Sval :=
    match sl with
    | [] => []
    | (k, s) :: rest => (k, val_to_liberal_sval s) :: sval_to_avals rest
    end in
  match val with
  | ValBaseNull => ValBaseNull
  | ValBaseBool b => ValBaseBool None
  | ValBaseInteger z => ValBaseInteger z
  | ValBaseBit bits => ValBaseBit (map bool_to_none bits)
  | ValBaseInt bits => ValBaseInt (map bool_to_none bits)
  | ValBaseVarbit n bits => ValBaseVarbit n (map bool_to_none bits)
  | ValBaseString s => ValBaseString s
  | ValBaseTuple l => ValBaseTuple (sval_to_vals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (bool_to_none valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l n => ValBaseStack (sval_to_vals l) n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s => ValBaseSenumField s1 (val_to_liberal_sval s)
  end.

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
                        (ValBaseBit (to_loptbool w i1))
                        (ValBaseBit (to_loptbool w i2))
    = eval_val_to_sval
        (force ValBaseNull
               (Ops.eval_binary_op_bit op w (BitArith.mod_bound w i1)
                                       (BitArith.mod_bound w i2))).
Proof.
  intros. unfold to_loptbool.
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
    (ValBaseBit (to_loptbool w i1))
    (ValBaseBit (to_loptbool w i2))
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
    (ValBaseBit (to_loptbool w i1))
    (ValBaseBit (to_loptbool w i2))
  = (ValBaseBit (to_loptbool w (i1 - i2))).
Proof.
  intros. unfold abs_minus. rewrite abs_bin_op_bit.
  - simpl. rewrite BitArith.minus_mod_mod.
    now rewrite to_lbool_bit_minus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_mul_bit : forall w i1 i2,
  abs_mul
    (ValBaseBit (to_loptbool w i1))
    (ValBaseBit (to_loptbool w i2))
  = (ValBaseBit (to_loptbool w (i1 * i2))).
Proof.
  intros. unfold abs_mul. rewrite abs_bin_op_bit.
  - simpl. rewrite BitArith.mult_mod_mod.
    now rewrite to_lbool_bit_mult.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_eq_bit : forall w i1 i2,
  abs_eq
    (ValBaseBit (to_loptbool w i1)) (ValBaseBit (to_loptbool w i2))
  = ValBaseBool
      (Some (BitArith.mod_bound w i1 =? BitArith.mod_bound w i2)%Z).
Proof.
  intros. unfold abs_eq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, to_loptbool.
  rewrite !lift_option_map_some. unfold Ops.eval_binary_op. simpl.
  rewrite !Zlength_to_lbool. rewrite BinNat.N.eqb_refl. simpl.
  now rewrite !bit_to_lbool_back.
Qed.

Lemma abs_neq_bit : forall w i1 i2,
  abs_neq
    (ValBaseBit (to_loptbool w i1)) (ValBaseBit (to_loptbool w i2))
  = ValBaseBool
      (Some (~~ (BitArith.mod_bound w i1 =? BitArith.mod_bound w i2)%Z)).
Proof.
  intros. unfold abs_neq. unfold build_abs_binary_op.
  unfold eval_sval_to_val, to_loptbool.
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
      | ExpUnaryOp op arg =>
          match eval_expr ge p a arg with
          | Some argv => Some (build_abs_unary_op (Ops.eval_unary_op op) argv)
          | None => None
          end
      | ExpBinaryOp op (larg, rarg) =>
          match eval_expr ge p a larg, eval_expr ge p a rarg with
          | Some largv, Some rargv => Some (build_abs_binary_op (Ops.eval_binary_op op) largv rargv)
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
      (fix sval_to_avals (sl : AList.StringAList Sval) :
        option (AList.StringAList Val) :=
         match sl with
         | [] => Some []
         | (k, s) :: rest =>
             match eval_sval_to_val s with
             | Some v =>
                 match sval_to_avals rest with
                 | Some l' => Some ((k, v) :: l')
                 | None => None
                 end
             | None => None
             end
         end) ->
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
  - rewrite Havals, <- Havals in H2. destruct x. destruct_match H2. 2: inv H2.
    inversion H4. subst x l0 kvs'. clear H4. destruct y. simpl in *. destruct H7.
    subst s0. destruct_match H2; inversion H2. subst s. clear H2.
    specialize (H0 v1 H5 v0 eq_refl). subst v0.
    specialize (IHForall l' s0 eq_refl H9). now subst s0.
Qed.

Lemma sval_to_val_Some_case3:
  forall eval_sval_to_vals : list Sval -> option (list Val),
    eval_sval_to_vals =
      (fix sval_to_vals (sl : list Sval) : option (list Val) :=
         match sl with
         | [] => Some []
         | s :: rest =>
             match eval_sval_to_val s with
             | Some v =>
                 match sval_to_vals rest with
                 | Some l' => Some (v :: l')
                 | None => None
                 end
             | None => None
             end
         end) ->
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
  - rewrite Hvals, <- Hvals in H2. destruct_match H2. 2: inv H2.
    inversion H4. subst x0 l1 lv'. clear H4. specialize (H0 _ H7 v eq_refl).
    subst v. destruct_match H2; inversion H2. subst l0. clear H2.
    specialize (IHForall l' l1 eq_refl H9). now subst.
Qed.

Lemma sval_to_val_Some:
  forall (v : Sval) (oldv : Val),
    sval_to_val read_ndetbit v oldv ->
    forall v0 : Val, eval_sval_to_val v = Some v0 -> v0 = oldv.
Proof.
  remember (fix sval_to_vals (sl : list Sval) : option (list Val) :=
              match sl with
              | [] => Some []
              | s :: rest =>
                  match eval_sval_to_val s with
                  | Some v =>
                      match sval_to_vals rest with
                      | Some l' => Some (v :: l')
                      | None => None
                      end
                  | None => None
                  end
              end) as eval_sval_to_vals. rename Heqeval_sval_to_vals into Hvals.
  remember (fix sval_to_avals (sl : AList.StringAList Sval) :
             option (AList.StringAList Val) :=
              match sl with
              | [] => Some []
              | (k, s) :: rest =>
                  match eval_sval_to_val s with
                  | Some v =>
                      match sval_to_avals rest with
                      | Some l' => Some ((k, v) :: l')
                      | None => None
                      end
                  | None => None
                  end
              end) as svals_to_avals. rename Heqsvals_to_avals into Havals.
  intro. induction v using custom_ValueBase_ind;
    intros; simpl in H1; try (inv H1; now inv H0).
  2-4: destruct_match H1; inv H1; inv H0; f_equal;
  eapply sval_to_val_Some_case1; eauto.
  - destruct_match b; inv H1. inv H0. inv H2. auto.
  - inversion H1. subst lv oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- Hvals in H1. eapply sval_to_val_Some_case3; eauto.
  - inversion H1. subst kvs oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- Havals in H1. eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst kvs b0 oldv. clear H1. simpl in H2. destruct_match b.
    2: inv H2. subst b. destruct_match H2; inversion H2. subst v0. clear H2.
    inversion H5. subst b b0. clear H5. f_equal. rewrite <- Havals in H1.
    eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst kvs oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. rewrite <- Havals in H1.
    f_equal. eapply sval_to_val_Some_case2; eauto.
  - inversion H1. subst lv next oldv. clear H1. simpl in H2.
    destruct_match H2; inversion H2. subst v0. clear H2. f_equal.
    rewrite <- Hvals in H1. eapply sval_to_val_Some_case3; eauto.
  - destruct_match H1; inversion H1. subst v0. clear H1. inversion H0. subst t v0 oldv.
    clear H0. f_equal. specialize (IHv _ H5 v1 eq_refl). now subst v1.
Qed.

Lemma sval_refine_liberal:
  forall v : Val, sval_refine (val_to_liberal_sval v) (eval_val_to_sval v).
Proof.
  induction v using custom_ValueBase_ind; simpl; constructor; auto.
  - constructor.
  - induction n; simpl; constructor; auto; unfold bool_to_none. constructor.
  - induction z; simpl; constructor; auto; unfold bool_to_none. constructor.
  - induction n; simpl; constructor; auto; unfold bool_to_none. constructor.
  - induction H0; constructor; auto.
  - induction H0; [constructor | destruct x; constructor; auto].
  - unfold bool_to_none. constructor.
  - induction H0; [constructor | destruct x; constructor; auto].
  - induction H0; [constructor | destruct x; constructor; auto].
  - induction H0; [constructor | destruct x; constructor; auto].
Qed.

Lemma sval_refine_map_bool_to_none: forall l1 l2,
    length l1 = length l2 -> Forall2 bit_refine (map bool_to_none l1) l2.
Proof.
  intros. rewrite map_bool_to_none. revert l2 H0. induction l1; intros.
  - destruct l2. 2: simpl in H0; inversion H0. simpl. constructor.
  - destruct l2. 1: simpl in H0; inversion H0. simpl. constructor.
    + constructor.
    + simpl in H0. inversion H0. now apply IHl1.
Qed.

Lemma sval_refine_liberal_cast:
  forall (v : Sval) (real_typ : P4Type) (oldv newv : Val),
    Ops.eval_cast real_typ oldv = Some newv ->
    sval_to_val read_ndetbit v oldv ->
    eval_sval_to_val v = None ->
    sval_refine
      (val_to_liberal_sval
         (force ValBaseNull (Ops.eval_cast real_typ (force_sval_to_val v))))
      (eval_val_to_sval newv).
Proof.
  induction v using custom_ValueBase_ind; simpl; intros; try (now inversion H2).
  - destruct b; inv H2. inv H1. inv H3.
    induction real_typ; simpl in H0; try (now inversion H0); simpl; auto.
    + destruct_match H0; inv H0. simpl. constructor. constructor; constructor.
    + destruct b'.
      * destruct typ; simpl in *; [destruct p|]; inversion H0.
      * rewrite H0. simpl. apply sval_refine_liberal.
  - destruct_match H2; inv H2. inv H1.
    induction real_typ; simpl in H0; try (now inversion H0); simpl; auto.
    + destruct lb'. 1: inv H0. destruct lb'. 2: destruct b; inv H0.
      inv H4. inv H7. simpl. simpl in H3. destruct x; inv H3. simpl.
      destruct b; inv H0; simpl; repeat constructor.
    + destruct_match H0; inv H0. rewrite Zlength_map, (Forall2_Zlength H4), H1. simpl.
      constructor. apply sval_refine_map_bool_to_none. rewrite map_length.
      rewrite <- !ZtoNat_Zlength, !Zlength_to_lbool. auto.
    + inv H0. constructor. apply sval_refine_map_bool_to_none. rewrite map_length.
      rewrite <- !ZtoNat_Zlength, !Zlength_to_lbool. auto.
    + destruct typ; simpl in H0. 2: inv H0. destruct p; try (now inversion H0).
      simpl. destruct_match H0; inv H0. simpl.
      rewrite Zlength_map, (Forall2_Zlength H4), H1. simpl. do 2 constructor.
      apply sval_refine_map_bool_to_none. rewrite !map_length, <- !ZtoNat_Zlength.
      now rewrite (Forall2_Zlength H4).
  - destruct_match H2; inv H2. inv H1.
    induction real_typ; simpl in H0; try (now inversion H0); simpl; auto.
    + inv H0. simpl. constructor. apply sval_refine_map_bool_to_none.
      rewrite <- !ZtoNat_Zlength, Zlength_map, !Zlength_to_lbool. auto.
    + destruct_match H0; inv H0. rewrite Zlength_map, (Forall2_Zlength H4), H1. simpl.
      constructor. apply sval_refine_map_bool_to_none. rewrite map_length.
      rewrite <- !ZtoNat_Zlength, !Zlength_to_lbool. auto.
    + destruct typ; simpl in H0. 2: inv H0. destruct p; try (now inversion H0).
      simpl. destruct_match H0; inv H0. simpl.
      rewrite Zlength_map, (Forall2_Zlength H4), H1. simpl. do 2 constructor.
      apply sval_refine_map_bool_to_none. rewrite !map_length, <- !ZtoNat_Zlength.
      now rewrite (Forall2_Zlength H4).
  - destruct_match H2; inv H2. inv H1.
    induction real_typ; simpl in H0; try (now inversion H0); simpl; auto.
    destruct typ; simpl in H0. 2: inv H0. destruct p; try (now inversion H0).
  - remember (fix sval_to_vals (sl : list Sval) : option (list Val) :=
                match sl with
                | [] => Some []
                | s :: rest =>
                    match eval_sval_to_val s with
                    | Some v =>
                        match sval_to_vals rest with
                        | Some l' => Some (v :: l')
                        | None => None
                        end
                    | None => None
                    end
                end) as to_vals. rename Heqto_vals into Hvals.
    destruct_match H3. 1: inv H3. revert oldv newv H1 H2. clear H3.
    induction vs; intros. 1: rewrite Hvals in H4; inv H4.
    rewrite Hvals, <- Hvals in H4. destruct_match H4.
    + admit.
    + inversion H0. subst x l. clear H0.
Abort.

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
  - destruct_match H0; inv H0. inversion H2; subst.
    eapply IHexpr in H11; eauto. eapply sval_to_val_to_sval in H14; eauto.
    destruct op; destruct v; unfold build_abs_unary_op; simpl. 3-48: admit.
    + simpl. red. inversion H11. subst. inversion H12. subst. simpl in H13. inv H13.
    + destruct o.
      * simpl. inv H11. inv H4. inv H12. simpl in H13. inv H13. constructor.
        inv H4. constructor.
      * simpl. inv H11. inv H12. simpl in H13. inv H13. constructor. constructor.
  - admit.
  - destruct_match H0. 2: inversion H0. destruct_match H0; inv H0. inv H2.
    rewrite H4 in H14. inv H14. red in H16. red in H13. eapply IHexpr in H11; eauto.
    red in H11. assert (sval_to_val read_ndetbit v oldv). {
      eapply exec_val_trans; eauto. clear. repeat intro. inv H; auto. constructor. }
    clear H11 H13. unfold build_abs_unary_op. rewrite val_to_sval_iff in H16.
    destruct (eval_sval_to_val v) eqn:?H.
    + eapply sval_to_val_Some in H2; eauto. subst v0. rewrite H15. simpl.
      rewrite H16. apply sval_refine_refl.
    + subst sv'. admit.
  - destruct_match H0. 2: inversion H0. destruct_match H0; inversion H0. clear H6.
    destruct_match H0.
    + destruct_match H0; inv H0. inv H2; rewrite H3 in H12; inv H12.
      rewrite H13 in H6. simpl in H6. rewrite H6 in H14. inv H14. constructor.
      apply exec_val_refl. apply bit_refine_refl.
    + inv H0. inv H2; rewrite H3 in H11; inv H11. constructor.
  - destruct_match H0; inv H0. inv H2. eapply IHexpr in H11; eauto.
    inv H12; inv H11; simpl. 1-3: eapply fields_get_sval_refine; eauto.
    + apply Forall2_Zlength in H5. rewrite H5. constructor.
      apply Forall2_refl. apply bit_refine_refl.
    + destruct_match H4.
      * unfold uninit_sval_of_typ in H4. Opaque repeat. inv H4. unfold Zrepeat.
        constructor. apply Forall2_refl, bit_refine_refl. Transparent repeat.
      * subst. constructor. apply Forall2_refl, bit_refine_refl.
 Admitted.

Lemma eval_expr_sound : forall ge p a_mem a_ext expr sv,
  eval_expr ge p a_mem expr = Some sv ->
  hoare_expr ge p (MEM a_mem (EXT a_ext)) expr sv.
Proof.
  unfold hoare_expr; intros.
  eapply eval_expr_sound'; eauto.
  destruct st; destruct H1; eauto.
Qed.

Hint Resolve eval_expr_sound : hoare.

Definition dummy_name := BareName (P4String.Build_t tags_t default "").
Global Opaque dummy_name.

(* Evaluate lvalue expressions. *)
Fixpoint eval_lexpr (ge : genv) (p : path) (a : mem_assertion) (expr : Expression) : option Lval :=
  match expr with
  | MkExpression _ (ExpName _ loc) _ _ =>
      Some (MkValueLvalue (ValLeftName dummy_name loc) dummy_type)
  | MkExpression _ (ExpExpressionMember expr member) _ _ =>
      match eval_lexpr ge p a expr with
      | Some lv =>
          if (String.eqb (P4String.str member) "next") then
            None
          else
            Some (MkValueLvalue (ValLeftMember lv (P4String.str member)) dummy_type)
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
    simpl. rewrite String.eqb_refl.
    destruct IHexec_lexpr. split. 1 : auto.
    apply Reflect.andE; split; auto.
  - simpl in H5. rewrite H0 in H5. destruct (eval_lexpr ge this a_mem expr); inv H5.
  - inv H5.
  - inv H4.
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
  let '(MkValueLvalue lv _) := lv in
  match lv with
  | ValLeftName _ (LInstance p) => eval_read_var a p
  | ValLeftName _ (LGlobal _) => None
  | ValLeftMember lv' member => option_map (get member) (eval_read a lv')
  | ValLeftBitAccess lv' hi lo => None (* TODO *)
  | ValLeftArrayAccess lv' pos => None (* TODO *)
  end.

Scheme custom_ValuePreLvalue_ind := Induction for ValuePreLvalue Sort Prop
  with custom_ValueLvalue_ind := Induction for ValueLvalue Sort Prop.

Lemma eval_read_sound : forall ge a_mem a_ext lv sv,
  eval_read a_mem lv = Some sv ->
  hoare_read ge (MEM a_mem (EXT a_ext)) lv sv
with eval_read_sound_preT : forall ge a_mem a_ext lv typ sv,
  eval_read a_mem (MkValueLvalue lv typ) = Some sv ->
  hoare_read ge (MEM a_mem (EXT a_ext)) (MkValueLvalue lv typ) sv.
Proof.
  - destruct lv; apply eval_read_sound_preT.
  - destruct lv; unfold hoare_read; intros.
    + destruct loc; only 1 : inv H0.
      inv H2.
      eapply eval_read_var_sound; eauto.
    + simpl in H0.
      destruct (eval_read a_mem expr) eqn:?. 2 : inv H0.
      inv H2. inv H0.
      apply get_sound in H9. subst.
      apply sval_refine_get.
      eapply eval_read_sound; eauto.
    + inv H0.
    + inv H0.
Qed.

Definition option_join {A} (ooa : option (option A)) : option A :=
  match ooa with
  | Some (Some a) => Some a
  | _ => None
  end.

Fixpoint eval_write (a : mem_assertion) (lv : Lval) (sv : Sval) : option mem_assertion :=
  let '(MkValueLvalue lv _) := lv in
  match lv with
  | ValLeftName _ (LInstance p) => Some (eval_write_var a p sv)
  | ValLeftName _ (LGlobal _) => None
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
    eapply all_values_set_some_is_some' with (v0 := v) in H1. 2 : apply H0.
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

Lemma eval_write_sound : forall ge a_mem a_ext lv sv a_mem',
  NoDup (map fst a_mem) ->
  eval_write a_mem lv sv = Some a_mem' ->
  hoare_write ge (MEM a_mem (EXT a_ext)) lv sv (MEM a_mem' (EXT a_ext))
with eval_write_sound_preT : forall ge a_mem a_ext lv typ sv a_mem',
  NoDup (map fst a_mem) ->
  eval_write a_mem (MkValueLvalue lv typ) sv = Some a_mem' ->
  hoare_write ge (MEM a_mem (EXT a_ext)) (MkValueLvalue lv typ) sv (MEM a_mem' (EXT a_ext)).
Proof.
  - destruct lv; apply eval_write_sound_preT.
  - destruct lv; unfold hoare_write; intros.
    + destruct loc; only 1 : inv H1.
      inv H1. inv H4.
      eapply eval_write_var_sound; eauto.
    + simpl in H1.
      destruct (eval_read a_mem expr) eqn:H_eval_read. 2 : inv H1.
      simpl in H1.
      destruct (eval_write a_mem expr (update name sv v)) eqn:H_eval_write. 2 : inv H1.
      inv H4.
      pose proof (eval_read_sound _ _ _ _ _ H_eval_read _ _ ltac:(eassumption) ltac:(eassumption)).
      epose proof (update_sound _ _ _ _ _ _ H4 H3 ltac:(eassumption)).
      inv H1.
      eapply eval_write_sound; eauto.
    + inv H1.
    + inv H1.
Qed.

Hint Resolve eval_write_sound : hoare.

Lemma eval_write_preserve_NoDup : forall (a : mem_assertion) (lv : Lval) sv a',
  NoDup (map fst a) ->
  eval_write a lv sv = Some a' ->
  NoDup (map fst a')
with eval_write_preserve_NoDup_preT : forall a lv typ sv a',
  NoDup (map fst a) ->
  eval_write a (MkValueLvalue lv typ) sv = Some a' ->
  NoDup (map fst a').
Proof.
  - destruct lv; apply eval_write_preserve_NoDup_preT.
  - destruct lv; intros.
    + destruct loc; only 1 : inv H1.
      inv H1.
      auto using eval_write_var_preserve_NoDup.
    + simpl in H1.
      destruct (eval_read a expr) eqn:H_eval_read. 2 : inv H1.
      simpl in H1.
      destruct (eval_write a expr (update name sv v)) eqn:H_eval_write. 2 : inv H1.
      inv H1.
      eapply eval_write_preserve_NoDup; eauto.
    + inv H1.
    + inv H1.
Qed.

Definition eval_arg (ge : genv) (p : path) (a : mem_assertion) (arg : option Expression)
    (dir : direction) : option (@argument tags_t) :=
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
    apply lval_eqb_eq in H2. subst v0.
    eapply H_eval_read; eauto.
Qed.

Definition eval_args (ge : genv) (p : path) (a : mem_assertion) (args : list (option Expression))
    (dirs : list direction) : option (list (@argument tags_t)) :=
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

End EvalExpr.

#[export] Hint Resolve eval_expr_sound eval_lexpr_sound eval_write_sound eval_arg_sound eval_args_sound : hoare.
