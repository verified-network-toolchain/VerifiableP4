Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import Coq.ZArith.BinInt.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section EvalExpr.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (ValueLvalue).

Notation ident := (string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation Expression := (@Expression tags_t).

Context `{@Target tags_t Expression}.

(* Convert Sval to Val only when all bits are known. *)
Axiom eval_sval_to_val : Sval -> option Val.

(* Convert Sval to Val, convert unknown bits to false. *)
Axiom force_sval_to_val : Sval -> Val.

(* Convert Val to Sval, but convert all bits to unknown. *)
Axiom val_to_liberal_sval : Val -> Sval.

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

Axiom abs_plus_bit : forall w i1 i2,
  abs_plus
    (ValBaseBit (P4Arith.to_loptbool w i1))
    (ValBaseBit (P4Arith.to_loptbool w i2))
  = (ValBaseBit (P4Arith.to_loptbool w (i1 + i2))).

Fixpoint eval_read (a : mem_assertion) (p : path) : option Sval :=
  match a with
  | (p', v) :: tl =>
      if path_eqb p p' then Some v else eval_read tl p
  | [] => None
  end.

Fixpoint eval_expr (ge : genv) (p : path) (a : mem_assertion) (expr : Expression) : option Sval :=
  match expr with
  | MkExpression _ expr _ dir =>
      match expr with
      | ExpInt i => Some (eval_p4int_sval i)
      | ExpName _ loc =>
          if is_directional dir then
            match loc with
            | LInstance p => eval_read a p
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
      (* | ExpCast newtyp arg =>
          match eval_expr_gen hook arg, get_real_type newtyp with
          | Some argv, Some real_typ => Ops.eval_cast real_typ argv
          | _, _ => None
          end *)
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
  admit.
    (* sval_refine sv sv0 ->
      sval_refine (get (P4String.str name) sv) (get (P4String.str name) sv0) *)
Admitted.

Lemma eval_expr_sound' : forall ge p a expr sv,
  eval_expr ge p a expr = Some sv ->
  forall st, (mem_denote a) (fst st) ->
  forall sv', exec_expr ge read_ndetbit p st expr sv' ->
    sval_refine sv sv'.
Admitted.

Lemma eval_expr_sound : forall ge p a expr sv,
  eval_expr ge p a expr = Some sv ->
  hoare_expr ge p (fun st => mem_denote a (fst st)) expr sv.
Proof.
  unfold hoare_expr; intros.
  eapply eval_expr_sound'; eauto.
Qed.

End EvalExpr.
