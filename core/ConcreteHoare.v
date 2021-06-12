(* Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import Hammer.Tactics.Tactics.

Section ConcreteHoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation assertion := (@assertion tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Variable ge : (@genv tags_t).
Variable inst_m : (@inst_mem tags_t).
(* Variable this : path. *)

Definition hoare_expr (pre : assertion) (expr : Expression) (v : Val) : Prop :=
  eval_expr pre expr = Some v.

Lemma hoare_expr_sound : forall p pre expr v,
  hoare_expr pre expr v ->
  Hoare.hoare_expr ge p (to_shallow_assertion p pre) expr v.
Admitted.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : @Expression tags_t) (lv : Lval) : Prop :=
  True. (* TODO *)

Lemma hoare_lexpr_sound : forall p pre expr lv,
  hoare_lexpr p pre expr lv ->
  Hoare.hoare_lexpr ge p (to_shallow_assertion p pre) expr lv.
Admitted.

Definition hoare_write (pre : assertion) (lv : Lval) (v : Val) (post : assertion) : Prop :=
  True. (* TODO *)

Lemma hoare_write_sound : forall p pre lv v post,
  hoare_write pre lv v post ->
  Hoare.hoare_write p (to_shallow_assertion p pre) lv v (to_shallow_assertion p post).
Admitted.

Inductive hoare_stmt : path -> assertion -> (@Statement tags_t) -> assertion -> Prop :=
  | hoare_stmt_assignment : forall p pre tags lhs rhs typ post lv v,
      hoare_lexpr p pre lhs lv ->
      hoare_expr pre rhs v ->
      hoare_write pre lv v post ->
      hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.

Lemma hoare_stmt_sound : forall p pre stmt post,
  hoare_stmt p pre stmt post ->
  Hoare.hoare_stmt ge inst_m p (to_shallow_assertion p pre) stmt (to_shallow_assertion p post).
Proof.
  intros * H_hoare_stmt.
  induction H_hoare_stmt.
  - repeat lazymatch goal with
    | H : hoare_lexpr _ _ _ _ |- _ => apply hoare_lexpr_sound in H
    | H : hoare_expr _ _ _ |- _ => apply hoare_expr_sound with (p := p) in H
    | H : hoare_write _ _ _ _ |- _ => eapply hoare_write_sound with (p := p) in H
    end.
    hnf. intros. inversion H4.
    + hauto unfold: Hoare.hoare_write, Hoare.hoare_expr, Hoare.hoare_lexpr.
    + admit. (* assign call rule should be ruled out, but we cnanot prove it now. *)
    + admit. (* assign call rule should be ruled out, but we cnanot prove it now. *)
    + unfold Hoare.hoare_lexpr in H0. hauto lq: on.
(* Qed. *)
Admitted.

End ConcreteHoare.
 *)