Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
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
  | ValBaseRecord l => match sval_to_avals l with
                       | Some l' => Some (ValBaseRecord l')
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
  | ValBaseStack l s n => match sval_to_vals l with
                          | Some l' => Some (ValBaseStack l' s n)
                          | None => None
                          end
  | ValBaseEnumField s1 s2 => Some (ValBaseEnumField s1 s2)
  | ValBaseSenumField s1 s2 s => match eval_sval_to_val s with
                                 | None => None
                                 | Some v => Some (ValBaseSenumField s1 s2 v)
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
  | ValBaseRecord l => ValBaseRecord (sval_to_avals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (opt_to_bool valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l s n => ValBaseStack (sval_to_vals l) s n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s2 s => ValBaseSenumField s1 s2 (force_sval_to_val s)
  end.

Definition bool_to_none: bool -> option bool := fun _ => None.

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
  | ValBaseRecord l => ValBaseRecord (sval_to_avals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (bool_to_none valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l s n => ValBaseStack (sval_to_vals l) s n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s2 s => ValBaseSenumField s1 s2 (val_to_liberal_sval s)
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

Lemma abs_bin_op_bit: forall op w i1 i2,
    ~ In op [Shl; Shr; Eq; NotEq; PlusPlus] ->
    build_abs_binary_op (Ops.eval_binary_op op)
                        (ValBaseBit (P4Arith.to_loptbool w i1))
                        (ValBaseBit (P4Arith.to_loptbool w i2))
    = eval_val_to_sval
        (force ValBaseNull
               (Ops.eval_binary_op_bit op w (P4Arith.BitArith.mod_bound w i1)
                                       (P4Arith.BitArith.mod_bound w i2))).
Proof.
  intros. unfold P4Arith.to_loptbool.
  unfold build_abs_binary_op. unfold eval_sval_to_val.
  rewrite !lift_option_map_some.
  unfold Ops.eval_binary_op.
  destruct op; try rewrite !P4Arith.bit_from_to_bool;
    try rewrite BinNat.N.eqb_refl; auto; exfalso; apply H0.
  - now left.
  - right. now left.
  - do 2 right. now left.
  - do 3 right. now left.
  - do 4 right. now left.
Qed.

Lemma abs_plus_bit : forall w i1 i2,
  abs_plus
    (ValBaseBit (P4Arith.to_loptbool w i1))
    (ValBaseBit (P4Arith.to_loptbool w i2))
  = ValBaseBit (P4Arith.to_loptbool w (i1 + i2)).
Proof.
  intros. unfold abs_plus. rewrite abs_bin_op_bit.
  - simpl. rewrite P4Arith.BitArith.plus_mod_mod.
    now rewrite P4Arith.to_lbool_bit_plus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_minus_bit : forall w i1 i2,
  abs_minus
    (ValBaseBit (P4Arith.to_loptbool w i1))
    (ValBaseBit (P4Arith.to_loptbool w i2))
  = (ValBaseBit (P4Arith.to_loptbool w (i1 - i2))).
Proof.
  intros. unfold abs_minus. rewrite abs_bin_op_bit.
  - simpl. rewrite P4Arith.BitArith.minus_mod_mod.
    now rewrite P4Arith.to_lbool_bit_minus.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_mul_bit : forall w i1 i2,
  abs_mul
    (ValBaseBit (P4Arith.to_loptbool w i1))
    (ValBaseBit (P4Arith.to_loptbool w i2))
  = (ValBaseBit (P4Arith.to_loptbool w (i1 * i2))).
Proof.
  intros. unfold abs_mul. rewrite abs_bin_op_bit.
  - simpl. rewrite P4Arith.BitArith.mult_mod_mod.
    now rewrite P4Arith.to_lbool_bit_mult.
  - intro. inversion H0; inversion H1; inversion H2; inversion H3;
      inversion H4; inversion H5.
Qed.

Lemma abs_plus_int : forall w i1 i2,
  abs_plus
    (ValBaseInt (P4Arith.to_loptbool w i1))
    (ValBaseInt (P4Arith.to_loptbool w i2))
  = (ValBaseInt (P4Arith.to_loptbool w (i1 + i2))).
Proof.
  intros. unfold abs_plus. unfold P4Arith.to_loptbool, build_abs_binary_op.
  unfold eval_sval_to_val. rewrite !lift_option_map_some.
  Opaque P4Arith.IntArith.from_lbool. simpl.
Abort.

Fixpoint eval_read_var (a : mem_assertion) (p : path) : option Sval :=
  match a with
  | (p', v) :: tl =>
      if path_eqb p p' then Some v else eval_read_var tl p
  | [] => None
  end.

Axiom path_eqb_eq : forall (p1 p2 : path), path_eqb p1 p2 -> p1 = p2.

Lemma eval_read_var_sound : forall a_mem a_ext p sv,
  eval_read_var a_mem p = Some sv ->
  hoare_read_var (MEM a_mem (EXT a_ext)) p sv.
Proof.
  unfold hoare_read_var; intros.
  induction a_mem.
  - inv H0.
  - destruct a as [p' ?]. simpl in H0.
    destruct st as [m es]; destruct H1.
    simpl in H1, H2. unfold mem_denote, mem_satisfies in H1; simpl in H1.
    destruct (path_eqb p p') eqn:H_p.
    + apply path_eqb_eq in H_p; subst.
      inv H0.
      rewrite H2 in H1. tauto.
    + apply IHa_mem; auto.
      split; tauto.
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
      | ExpExpressionMember expr name =>
          match eval_expr ge p a expr with
          | Some sv =>
              Some (get (P4String.str name) sv)
          | None => None
          end
      | _ => None
      end
  end.

Lemma get_member_sound : forall sv f sv',
  match sv with ValBaseStruct _ | ValBaseHeader _ _ => true | _ => false end ->
  get_member sv f sv' ->
  get f sv = sv'.
Proof.
  intros.
  destruct sv; try solve [inv H0]; inv H1.
  - unfold get. rewrite H3. auto.
  - unfold get. rewrite H6. auto.
Qed.

Lemma eval_expr_member_sound : forall ge p a tags expr typ dir name sv,
  match sv with ValBaseStruct _ | ValBaseHeader _ _ => true | _ => false end ->
  hoare_expr ge p a expr sv ->
  hoare_expr ge p a (MkExpression tags (ExpExpressionMember expr name) typ dir) (get (P4String.str name) sv).
Proof.
  unfold hoare_expr.
  intros.
  inv H3.
  assert (sval_refine sv sv0) by (eapply H1; eauto).
  apply get_member_sound in H13. 2 : {
    inv H3; try solve [inv H0]; auto.
  }
  rewrite <- H13.
  apply sval_refine_get; auto.
Qed.

Lemma eval_expr_sound' : forall ge p a expr sv,
  eval_expr ge p a expr = Some sv ->
  forall st, (mem_denote a) (fst st) ->
  forall sv', exec_expr ge read_ndetbit p st expr sv' ->
    sval_refine sv sv'.
Admitted.

Lemma eval_expr_sound : forall ge p a_mem a_ext expr sv,
  eval_expr ge p a_mem expr = Some sv ->
  hoare_expr ge p (MEM a_mem (EXT a_ext)) expr sv.
Proof.
  unfold hoare_expr; intros.
  eapply eval_expr_sound'; eauto.
  destruct st; destruct H1; eauto.
Qed.

Definition dummy_name := BareName (P4String.Build_t tags_t default "").
Global Opaque dummy_name.

(* Evaluate lvalue expressions. *)
Fixpoint eval_lexpr (expr : Expression) : option Lval :=
  match expr with
  | MkExpression _ (ExpName _ loc) _ _ =>
      Some (MkValueLvalue (ValLeftName dummy_name loc) dummy_type)
  | MkExpression _ (ExpExpressionMember expr member) _ _ =>
      match eval_lexpr expr with
      | Some lv =>
          if (String.eqb (P4String.str member) "next") then
            None
          else
            Some (MkValueLvalue (ValLeftMember lv (P4String.str member)) dummy_type)
      | None => None
      end
  | _ => None
  end.

Axiom locator_eqb_refl : forall (loc : Locator),
  locator_eqb loc loc.
Hint Resolve locator_eqb_refl : core.

Lemma eval_lexpr_sound : forall ge p a_mem a_ext expr lv,
  eval_lexpr expr = Some lv ->
  hoare_lexpr ge p (MEM a_mem (EXT a_ext)) expr lv.
Proof.
  unfold hoare_lexpr; intros.
  generalize dependent lv.
  induction H2; intros; try solve [inv H0].
  - inv H0. simpl; auto.
  - simpl in H3. rewrite H0 in H3.
    destruct (eval_lexpr expr) as [lv_base |]. 2 : inv H3.
    specialize (IHexec_lexpr ltac:(auto) _ ltac:(eauto)).
    inv H3.
    simpl. rewrite String.eqb_refl.
    destruct IHexec_lexpr. split. 1 : auto.
    apply Reflect.andE; split; auto.
  - simpl in H5. rewrite H0 in H5. destruct (eval_lexpr expr); inv H5.
  - inv H5.
  - inv H5.
Qed.

Definition eval_write_var (a : mem_assertion) (p : path) (sv : Sval) : mem_assertion :=
  AList.set_some a p sv.

Lemma get_set_same : forall {A} (p : path) (a : A) (m : PathMap.t A),
  PathMap.get p (PathMap.set p a m) = Some a.
Proof.
Admitted.

Lemma get_set_diff : forall {A} (p p' : path) (a : A) (m : PathMap.t A),
  p <> p' ->
  PathMap.get p (PathMap.set p' a m) = PathMap.get p m.
Proof.
Admitted.

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
      rewrite get_set_diff. 2 : { simpl in H0. tauto. }
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
    unfold mem_satisfies_unit. rewrite get_set_same; auto.
  - simpl. destruct H1.
    destruct a as [p' sv''].
    destruct (EquivDec.list_eqdec EquivUtil.StringEqDec p p') as [H_p | H_p].
    + red in H_p.
      split.
      * simpl. rewrite get_set_same; auto.
      * apply mem_assertion_set_disjoint; auto.
        inv H0; auto.
    + cbv in H_p.
      split.
      * unfold mem_satisfies_unit.
        rewrite get_set_diff; auto.
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
  unfold hoare_func_copy_in, bind_parameters. intros.
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
      inv H2. inv H8.
      * (* struct *)
        assert (get name (ValBaseStruct fields) = sv'). {
          simpl. rewrite H3. auto.
        }
        inv H0.
        apply sval_refine_get.
        eapply eval_read_sound; eauto.
      * (* header *)
        assert (get name (ValBaseHeader fields is_valid) = sv'). {
          simpl. rewrite H3. auto.
        }
        inv H0.
        apply sval_refine_get.
        eapply eval_read_sound; eauto.
      * (* union *)
        assert (get name (ValBaseUnion fields) = sv'). {
          simpl. rewrite H3. auto.
        }
        inv H0.
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

Lemma eval_write_sound : forall ge a_mem a_ext lv sv a_mem',
  eval_write a_mem lv sv = Some a_mem' ->
  hoare_write ge (MEM a_mem (EXT a_ext)) lv sv (MEM a_mem' (EXT a_ext)).
Admitted.

End EvalExpr.
