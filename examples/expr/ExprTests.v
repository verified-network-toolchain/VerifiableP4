Require Import Coq.Strings.String.
Require Import Poulet4.P4defs.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.
Import Poulet4.Semantics.
Open Scope string_scope.

Section ExprTests.

Context `{@Target Info (@Expression Info)}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (ValueLvalue).

Notation ident := (string).
Notation path := (list ident).

(* a.x + a.y *)
Definition expr1 :=
  (MkExpression NoInfo
    (ExpBinaryOp Plus
         ( (MkExpression NoInfo
                (ExpExpressionMember
                     (MkExpression NoInfo
                          (ExpName
                           (BareName
                            {| stags := NoInfo;
                               str := "a" |})
                           (LInstance ["a"]))
                          (TypTypeName
                           (BareName
                            {| stags := NoInfo;
                               str := "metadata" |}))
                          InOut)
                     {| stags := NoInfo;
                        str := "x" |})
                (TypBit 8%N) Directionless),
           (MkExpression NoInfo
                (ExpExpressionMember
                     (MkExpression NoInfo
                          (ExpName
                           (BareName
                            {| stags := NoInfo;
                               str := "a" |})
                           (LInstance ["a"]))
                          (TypTypeName
                           (BareName
                            {| stags := NoInfo;
                               str := "metadata" |}))
                          InOut)
                     {| stags := NoInfo;
                        str := "y" |})
                (TypBit 8%N) Directionless) ))
    (TypBit 8%N) Directionless).

Variable (ge : genv) (p : path).
Variable (xi yi : Z) (z : Sval).

Definition mem_pre1 : mem_assertion :=
  [(["a"], ValBaseStruct [("x", ValBaseBit (P4Arith.to_loptbool 8%N xi));
                          ("y", ValBaseBit (P4Arith.to_loptbool 8%N yi));
                          ("z", z)])].

Definition pre1 : assertion := fun '(m, es) =>
  mem_denote mem_pre1 m.

Definition mem_assertion_to_mem (a : mem_assertion) : mem :=
  fold_right (fun '(p, sv) m => PathMap.set p sv m) PathMap.empty a.

Definition st1 : state := (mem_assertion_to_mem mem_pre1, PathMap.empty).

(* We should define P4Arith.to_loptbool w x := map Some (P4Arith.to_lbool w x) *)

Lemma Forall2_strict_read_ndetbit : forall w x,
  Forall2 strict_read_ndetbit (P4Arith.to_loptbool w x) (P4Arith.to_lbool w x).
Admitted.

Hint Resolve Forall2_strict_read_ndetbit : eval_expr.

(* Lemma test1 : exists sv, hoare_expr ge p pre1 expr1 sv. *)
Lemma test1 : exists sv, exec_expr ge strict_read_ndetbit p st1 expr1 sv.
Proof.
  econstructor.
  econstructor.
  - econstructor.
    + econstructor; econstructor.
    + econstructor; econstructor.
  - econstructor.
    + econstructor; econstructor.
    + econstructor; econstructor.
  - econstructor. auto with eval_expr.
  - econstructor. auto with eval_expr.
  - econstructor.
  - (* This form is very bad. *)
    (* simpl is not helpful. *)
Admitted.

(* "test1" uses exec_expr as the evaluation scheme. For soundness, we'll need to prove a lemma
  to relate (exec_expr strict_read_ndetbit) with hoare_expr, which seems not hard to do. To
  summarize test1, we find constructing a nice exec_expr is tricky. We can construct by econstructor
  and eauto. The econstructor part can be merged into eauto by Hint Constructors. But the result
  is bad:

  val_to_sval
  (ValBaseInt
     (P4Arith.to_lbool (Z.to_N (Zlength (P4Arith.to_lbool 8 xi)))
        (P4Arith.IntArith.plus_mod ...)))

  I think it can be resolved by using lemmas instead of constructors for Ops.Ops.eval_binary_op.
      *)

(* Let's redefine P4Arith.to_loptbool as (map Some (P4Arith.to_lbool)). *)
(* Still cannot handle force get_member. *)
(* Also we want to handle get_set conversion. *)

Axiom target1 : hoare_expr ge p pre1 expr1 (ValBaseBit (P4Arith.to_loptbool 8%N (xi + yi))).

Variable (a : Sval).

Definition mem_pre2 : mem_assertion :=
  [(["a"], a)].



(* ValBaseStruct [("x", ValBaseInt (P4Arith.to_loptbool 8%N xi));
                          ("y", ValBaseInt (P4Arith.to_loptbool 8%N yi));
                          ("z", z)])]. *)

Definition pre2 : assertion := fun '(m, es) =>
  mem_denote mem_pre2 m.

Axiom get : ident -> Sval -> Sval.

Axiom target2 :
  get "x" a = ValBaseBit (P4Arith.to_loptbool 8%N xi) ->
  get "y" a = ValBaseBit (P4Arith.to_loptbool 8%N yi) ->
  hoare_expr ge p pre2 expr1 (ValBaseBit (P4Arith.to_loptbool 8%N (xi + yi))).

(* So I think we should build a function that eval to (option Sval),
  but only gives None when used variables are not found in the mem_assertion. *)

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
  build_abs_unary_op (Ops.Ops.eval_unary_op Not).

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
  build_abs_binary_op (Ops.Ops.eval_binary_op Plus).

Definition abs_minus : Sval -> Sval -> Sval :=
  build_abs_binary_op (Ops.Ops.eval_binary_op Minus).

Axiom abs_plus_bit : forall w i1 i2,
  abs_plus
    (ValBaseBit (P4Arith.to_loptbool w i1))
    (ValBaseBit (P4Arith.to_loptbool w i2))
  = (ValBaseBit (P4Arith.to_loptbool w (i1 + i2))).





