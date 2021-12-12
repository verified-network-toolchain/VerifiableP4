Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.EvalExpr.
Require Import Poulet4.V1Model.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.
Require Import Coq.ZArith.BinInt.

Section ConcreteHoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (String.string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Context `{@Target tags_t Expression}.

Variable ge : (@genv tags_t _).

(* shallow assertions *)
Definition assertion := state -> Prop.
Definition arg_assertion := list Sval -> state -> Prop.
Definition ret_assertion := Val -> state -> Prop.
Definition arg_ret_assertion := list Sval -> Val -> state -> Prop.

Lemma hoare_stmt_assign' : forall p a_mem a_ext tags lhs rhs typ a_mem' ret_post lv sv,
  is_call_expression rhs = false ->
  is_no_dup (map fst a_mem) ->
  eval_lexpr lhs = Some lv ->
  eval_expr ge p a_mem rhs = Some sv ->
  eval_write a_mem lv sv = Some a_mem' ->
  hoare_stmt ge p (MEM a_mem (EXT a_ext)) (MkStatement tags (StatAssignment lhs rhs) typ)
      (mk_post_assertion (MEM a_mem' (EXT a_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_assign.
  - assumption.
  - apply eval_lexpr_sound; eassumption.
  - apply hoare_expr_det_intro, eval_expr_sound; eassumption.
  - apply eval_write_sound; only 1 : apply is_no_dup_NoDup; eassumption.
Qed.

End ConcreteHoare.
