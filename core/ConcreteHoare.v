Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section ConcreteHoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation SemLval := (@ValueLvalue tags_t).
Notation Lval := (@AssertionLang.Lval tags_t).

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
  eval_expr ge pre expr = Some v.

Lemma hoare_expr_sound : forall p pre expr v,
  wellformed pre ->
  hoare_expr pre expr v ->
  Hoare.hoare_expr ge p (to_shallow_assertion p pre) expr v.
Proof.
  unfold Hoare.hoare_expr; intros.
  eapply eval_expr_sound; eassumption.
Qed.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : @Expression tags_t) (lv : Lval) : Prop :=
  eval_lexpr expr = Some lv.

Lemma hoare_lexpr_sound : forall p pre expr lv,
  hoare_lexpr p pre expr lv ->
  Hoare.hoare_lexpr ge p (to_shallow_assertion p pre) expr (lval_to_semlval lv).
Proof.
  unfold Hoare.hoare_lexpr; intros.
  eapply eval_lexpr_sound; eassumption.
Qed.

Definition hoare_write (pre : assertion) (lv : Lval) (v : Val) (post : assertion) : Prop :=
  is_writable_lval lv pre /\ eval_write pre lv v = post.

Lemma hoare_write_sound : forall p pre lv v post,
  wellformed pre ->
  hoare_write pre lv v post ->
  Hoare.hoare_write p (to_shallow_assertion p pre) (lval_to_semlval lv) v (to_shallow_assertion p post).
Proof.
  unfold Hoare.hoare_write; intros. destruct H1; subst.
  eapply eval_write_sound; try eassumption.
Qed.

Inductive hoare_stmt : path -> assertion -> (@Statement tags_t) -> assertion -> Prop :=
  | hoare_stmt_assignment : forall p pre tags lhs rhs typ post lv v,
      hoare_lexpr p pre lhs lv ->
      is_valid_field pre lv ->
      hoare_expr pre rhs v ->
      hoare_write pre lv v post ->
      hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.

Lemma hoare_stmt_sound : forall p pre stmt post,
  wellformed pre ->
  hoare_stmt p pre stmt post ->
  Hoare.hoare_stmt ge inst_m p (to_shallow_assertion p pre) stmt (to_shallow_assertion p post).
Proof.
  intros * H_wellformed H_hoare_stmt.
  induction H_hoare_stmt.
  - hnf. intros. pinv @exec_stmt.
    + repeat lazymatch goal with
      | H : hoare_lexpr _ _ _ _ |- _ => apply hoare_lexpr_sound in H
      | H : hoare_expr _ _ _ |- _ => apply hoare_expr_sound with (p := p) in H; only 2 : assumption
      | H : hoare_write _ _ _ _ |- _ => eapply hoare_write_sound with (p := p) in H; only 2 : assumption
      end.
      specialize (H0 _ _ _ H4 H15).
      specialize (H2 _ _ H4 H16); subst v0.
      eapply exec_write_congruent in H17. 3 : apply H0. 2 : { eapply state_is_valid_field_sound, is_valid_field_sound; eassumption. }
      specialize (H3 _ _ H4 H17). sfirstorder.
    + pinv @exec_call; pinv hoare_expr.
    + pinv @exec_call; pinv hoare_expr.
    + lazymatch goal with
      | H : hoare_lexpr _ _ _ _ |- _ => apply hoare_lexpr_sound in H
      end.
      unfold Hoare.hoare_lexpr in H0. hauto lq: on.
Qed.

Inductive hoare_block : path -> assertion -> (@Block tags_t) -> assertion -> Prop :=
  | hoare_block_nil : forall p pre post tags,
      implies pre post ->
      hoare_block p pre (BlockEmpty tags) post
  | hoare_block_cons : forall p pre stmt rest mid post,
      hoare_stmt p pre stmt mid ->
      wellformed mid ->
      hoare_block p mid rest post ->
      hoare_block p pre (BlockCons stmt rest) post.

Lemma hoare_block_sound : forall p pre block post,
  wellformed pre ->
  hoare_block p pre block post ->
  Hoare.hoare_block ge inst_m p (to_shallow_assertion p pre) block (to_shallow_assertion p post).
Proof.
  intros * H_wellformed H_hoare_block.
  induction H_hoare_block.
  - hnf. intros. pinv @exec_block.
    split; only 1 : constructor.
    eapply implies_sound; eassumption.
  - apply hoare_stmt_sound in H0; only 2 : assumption.
    hnf. intros. pinv @exec_block.
    + specialize (H0 _ _ _ H2 H9).
      specialize (IHH_hoare_block H1 _ _ _ (proj2 H0) H12).
      auto.
    + specialize (H0 _ _ _ H2 H9). hauto.
Qed.

End ConcreteHoare.
