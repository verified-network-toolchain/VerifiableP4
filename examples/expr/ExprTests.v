Require Import Coq.Strings.String.
Require Import Poulet4.P4defs.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.EvalExpr.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.
Import Poulet4.Semantics.
Open Scope string_scope.

Section ExprTests.
Context `{@Target Info (@Expression Info)}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (ValueLvalue).
Notation Expression := (@Expression Info).

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

Axiom target2 :
  get "x" a = ValBaseBit (P4Arith.to_loptbool 8%N xi) ->
  get "y" a = ValBaseBit (P4Arith.to_loptbool 8%N yi) ->
  hoare_expr ge p pre2 expr1 (ValBaseBit (P4Arith.to_loptbool 8%N (xi + yi))).

(* So I think we should build a function that eval to (option Sval),
  but only gives None when used variables are not found in the mem_assertion. *)



Eval simpl in (eval_expr ge p mem_pre1 expr1).

