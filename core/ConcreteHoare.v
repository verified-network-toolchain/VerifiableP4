Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionLangSoundness.
Require Import Poulet4.V1Model.
Require Import ProD3.core.V1ModelLang.
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
Notation arg_assertion := (@arg_assertion tags_t).
Notation ret_assertion := (@ret_assertion tags_t).
Notation mem_assertion := (@AssertionLang.assertion tags_t).
Notation ext_assertion := (@ext_assertion tags_t).

Notation state := (@state tags_t V1Model).

Variable ge : (@genv tags_t).
Variable inst_m : (@inst_mem tags_t).

Section WithThisPath.

Variable this : path.

Definition assertion : Type := mem_assertion * ext_assertion.

Record post_assertion := mk_post_assertion {
  post_continue :> assertion;
  post_return : ret_assertion * mem_assertion * ext_assertion
}.

Definition to_shallow_assertion_continue (a : assertion) :=
  match a with (a_mem, a_ext) =>
  (fun (st : state) => let (m, es) := st in
    to_shallow_assertion this a_mem m /\
    ext_to_shallow_assertion this a_ext es)
  end.

Definition to_shallow_assertion_return (a : ret_assertion * mem_assertion * ext_assertion) :=
  match a with (a_ret, a_mem, a_ext) =>
  (fun vret (st : state) => let (m, es) := st in
    ret_to_shallow_assertion a_ret vret /\
    to_shallow_assertion this a_mem m /\
    ext_to_shallow_assertion this a_ext es)
  end.

Definition to_shallow_post_assertion (post : post_assertion) : Hoare.post_assertion :=
  match post with mk_post_assertion a_continue a_return =>
  Hoare.mk_post_assertion (to_shallow_assertion_continue a_continue) (to_shallow_assertion_return a_return)
  end.

Definition implies (pre : assertion) (post : assertion) : bool :=
  AssertionLang.implies (fst pre) (fst post) && ext_implies (snd pre) (snd post).

Lemma implies_sound : forall (pre post : assertion),
  implies pre post ->
  Hoare.implies (to_shallow_assertion_continue pre) (to_shallow_assertion_continue post).
Proof.
  intros * H_implies. destruct pre; destruct post.
  apply Reflect.andE in H_implies. destruct H_implies.
  intros [] []. split.
  - eapply AssertionLangSoundness.implies_sound; eassumption.
  - eapply ext_implies_sound; eassumption.
Qed.

Definition hoare_expr (pre : assertion) (expr : Expression) (v : Val) : Prop :=
  eval_expr ge (fst pre) expr = Some v.

Lemma hoare_expr_sound : forall (pre : assertion) expr v,
  wellformed (fst pre) ->
  hoare_expr pre expr v ->
  Hoare.hoare_expr ge this (to_shallow_assertion_continue pre) expr v.
Proof.
  unfold Hoare.hoare_expr; intros.
  destruct pre; destruct st; destruct H1.
  eapply eval_expr_sound; try eassumption; eassumption.
Qed.

Definition hoare_lexpr (pre : assertion) (expr : Expression) (lv : Lval) : Prop :=
  eval_lexpr expr = Some lv.

Lemma hoare_lexpr_sound : forall pre expr lv,
  hoare_lexpr pre expr lv ->
  Hoare.hoare_lexpr ge this (to_shallow_assertion_continue pre) expr (lval_to_semlval lv).
Proof.
  unfold Hoare.hoare_lexpr; intros.
  eapply eval_lexpr_sound; eassumption.
Qed.

Definition hoare_write (pre : assertion) (lv : Lval) (v : Val) (post : assertion) : Prop :=
  is_writable_lval lv (fst pre) /\ eval_write (fst pre) lv v = (fst post) /\ (snd pre = snd post).

Lemma exec_write_preserve_extern_state : forall st lv v st',
  exec_write (H := V1Model) this st lv v st' ->
  snd st = snd st'.
Proof.
  intros * H_exec_write.
  induction H_exec_write; only 2-5 : assumption.
  destruct st; destruct st'. inversion H. constructor.
Qed.

Lemma hoare_write_sound : forall pre lv v post,
  wellformed (fst pre) ->
  hoare_write pre lv v post ->
  Hoare.hoare_write this (to_shallow_assertion_continue pre) (lval_to_semlval lv) v (to_shallow_assertion_continue post).
Proof.
  unfold Hoare.hoare_write; intros.
  destruct pre; destruct post;
    destruct st as [m es]; destruct st' as [m' es'];
    destruct H0 as [? []]; destruct H1; simpl in *; subst.
  split.
  - eapply (eval_write_sound (H := V1Model)) with (st := (m, es)) (st' := (m', es')); eassumption.
  - pose proof (exec_write_preserve_extern_state _ _ _ _ (ltac:(eassumption))).
    scongruence.
Qed.

End WithThisPath.

Inductive hoare_stmt : path -> assertion -> (@Statement tags_t) -> post_assertion -> Prop :=
  | hoare_stmt_assignment : forall p pre tags lhs rhs typ (post : post_assertion) lv v,
      hoare_lexpr pre lhs lv ->
      hoare_expr pre rhs v ->
      hoare_write pre lv v post ->
      hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.

Inductive hoare_block : path -> assertion -> (@Block tags_t) -> post_assertion -> Prop :=
  | hoare_block_nil : forall p pre (post : post_assertion) tags,
      implies pre post ->
      hoare_block p pre (BlockEmpty tags) post
  | hoare_block_cons : forall p pre stmt rest mid (post : post_assertion),
      hoare_stmt p pre stmt mid ->
      wellformed (fst (mid : assertion)) ->
      hoare_block p mid rest post ->
      hoare_block p pre (BlockCons stmt rest) post.

Lemma hoare_stmt_sound : forall p pre stmt post,
  wellformed (fst pre) ->
  hoare_stmt p pre stmt post ->
  Hoare.deep_hoare_stmt ge inst_m p (to_shallow_assertion_continue p pre) stmt (to_shallow_post_assertion p post).
Proof.
  intros * H_wellformed H_hoare_stmt.
  apply deep_hoare_stmt_intro.
  induction H_hoare_stmt.
  - hnf. intros. pinv @exec_stmt.
    + assert (is_valid_field (fst pre) lv). {
        destruct H1. hauto unfold: is_true, is_writable_lval, andb, fst, assertion.
      }
      repeat lazymatch goal with
      | H : hoare_lexpr _ _ _ |- _ => apply hoare_lexpr_sound with (this := p) in H
      | H : hoare_expr _ _ _ |- _ => apply hoare_expr_sound with (this := p) in H; only 2 : assumption
      | H : hoare_write _ _ _ _ |- _ => eapply hoare_write_sound with (this := p) in H; only 2 : assumption
      end.
      specialize (H _ _ _ H2 H14) as [? H]; subst sig0.
      specialize (H0 _ _ H2 H13); subst v0.
      eapply exec_write_congruent in H15.
        3 : eassumption.
        2 : {
          destruct st; destruct pre; destruct H2.
          eapply mem_is_valid_field_sound, is_valid_field_sound; eassumption.
        }
      specialize (H1 _ _ H2 H15). simpl. destruct post; sfirstorder.
    + pinv @exec_call; pinv hoare_expr.
    Unshelve. all : exact V1Model. (* try remove this *)
Qed.

Lemma hoare_block_sound : forall p pre block post,
  wellformed (fst pre) ->
  hoare_block p pre block post ->
  Hoare.deep_hoare_block ge inst_m p (to_shallow_assertion_continue p pre) block (to_shallow_post_assertion p post).
Proof.
  intros * H_wellformed H_hoare_block.
  induction H_hoare_block.
  - constructor.
    destruct post. intros st ?; eapply implies_sound; eassumption.
  - apply hoare_stmt_sound in H; only 2 : assumption.
    destruct mid; econstructor; eauto.
Qed.

End ConcreteHoare.
