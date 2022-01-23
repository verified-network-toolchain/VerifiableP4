Require Import Coq.Lists.List.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.ExprInd.
Require Import ProD3.core.Hoare.
Require ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.ConcreteHoare.
Require Import Hammer.Plugin.Hammer.

Section Modifies.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}.

Context (ge : genv).

Definition func_modifies_vars (p : path) (func : @fundef tags_t) (vars : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    forall q, ~(In q vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st').

Definition func_modifies_exts (p : path) (func : @fundef tags_t) (exts : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    forall q, ~(In q exts) -> PathMap.get q (snd st) = PathMap.get q (snd st').

Definition modifies (vars : option (list path)) (exts : list path) (st st' : state) : Prop :=
  match vars with
  | Some vars =>
      forall q, ~(In q vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st')
  | None => True
  end
    /\ forall q, ~(In q exts) -> PathMap.get q (snd st) = PathMap.get q (snd st').

Lemma modifies_refl : forall (vars : option (list path)) (exts : list path) (st : state),
  modifies vars exts st st.
Proof.
  unfold modifies; intros; destruct vars; auto.
Qed.

Local Hint Resolve modifies_refl : core.

Lemma modifies_trans : forall (vars : option (list path)) (exts : list path) (st1 st2 st3 : state),
  modifies vars exts st1 st2 ->
  modifies vars exts st2 st3 ->
  modifies vars exts st1 st3.
Proof.
  unfold modifies; intros; destruct vars; sfirstorder.
Qed.

Local Hint Resolve modifies_trans : core.

Definition stmt_modifies (p : path) (stmt : Statement) (vars : option (list path))
    (exts : list path) :=
  forall st st' sig,
    exec_stmt ge read_ndetbit p st stmt st' sig ->
    modifies vars exts st st'.

Definition block_modifies (p : path) (block : Block) (vars : option (list path))
    (exts : list path) :=
  forall st st' sig,
    exec_block ge read_ndetbit p st block st' sig ->
    modifies vars exts st st'.

Definition call_modifies (p : path) (expr : Expression) (vars : option (list path))
    (exts : list path) :=
  forall st st' sig,
    exec_call ge read_ndetbit p st expr st' sig ->
    modifies vars exts st st'.

Definition func_modifies (p : path) (func : @fundef tags_t) (vars : option (list path))
    (exts : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    modifies vars exts st st'.

(* Ltac specialize_hoare_block :=
  lazymatch goal with
  | H : hoare_block _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_block _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_stmt :=
  lazymatch goal with
  | H : hoare_stmt _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_stmt _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_expr_det :=
  lazymatch goal with
  | H : hoare_expr_det _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(first [eassumption | repeat constructor]))
  | H : forall _ _ _, _ -> exec_expr_det _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(first [eassumption | repeat constructor]))
  end.

Ltac specialize_hoare_lexpr :=
  lazymatch goal with
  | H : hoare_lexpr _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_lexpr _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_write :=
  lazymatch goal with
  | H : hoare_write _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_write _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_call :=
  lazymatch goal with
  | H : hoare_call _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_call _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end. *)

Lemma block_modifies_nil : forall p tags vars exts,
  block_modifies p (BlockEmpty tags) vars exts.
Proof.
  unfold block_modifies. intros. inv H.
  auto.
Qed.

Local Hint Resolve block_modifies_nil : core.

Lemma block_modifies_empty_block : forall (p : path) (vars : option (list path)) (exts : list path)
         (st st' : state) (sig : signal),
  exec_block ge read_ndetbit p st empty_block st' sig ->
  modifies vars exts st st'.
Proof.
  intros. inv H.
  auto.
Qed.

Local Hint Resolve block_modifies_empty_block : core.

Lemma block_modifies_cons : forall p stmt block vars exts,
  stmt_modifies p stmt vars exts ->
  block_modifies p block vars exts ->
  block_modifies p (BlockCons stmt block) vars exts.
Proof.
  unfold stmt_modifies, block_modifies. intros.
  inv H1. destruct sig0; eauto.
Qed.

Fixpoint get_lval_base (lv : Lval) : option path :=
  let '(MkValueLvalue lv _ ) := lv in
  match lv with
  | ValLeftName _ (LInstance p) => Some p
  | ValLeftName _ (LGlobal _) => None
  | ValLeftMember lv _
  | ValLeftBitAccess lv _ _
  | ValLeftArrayAccess lv _
    => get_lval_base lv
  end.

Fixpoint get_lexpr_base (expr : @Expression tags_t) : option path :=
  let '(MkExpression _ expr _ _) := expr in
  match expr with
  | ExpName _ (LInstance p) => Some p
  | ExpName _ (LGlobal p) => None
  | ExpArrayAccess expr _
  | ExpBitStringAccess expr _ _
  | ExpExpressionMember expr _
    => get_lexpr_base expr
  | _ => None
  end.

Lemma get_lexpr_base_sound : forall p expr lv p',
  get_lexpr_base expr = Some p' ->
  forall st sig,
    exec_lexpr ge read_ndetbit p st expr lv sig ->
  get_lval_base lv = Some p'.
Proof.
  induction expr using expr_ind; intros; inv H0;
    only 2, 3, 4, 5 : (simpl in *; eauto).
  destruct l; auto.
Qed.

Local Hint Resolve get_lexpr_base_sound : core.

Definition In_vars (p : path) (vars : option (list path)) : Prop :=
  force True (option_map (In p) vars).

Lemma write_modifies_intro : forall lv p st sv st' vars exts,
  get_lval_base lv = Some p ->
  exec_write ge st lv sv st' ->
  In_vars p vars ->
  modifies vars exts st st'.
Proof.
  induction 2; intros; simpl in *; only 2, 3, 4, 5 : eauto.
  destruct loc; inv H.
  destruct vars as [vars | ].
  - unfold In_vars in H1; simpl in H1.
    destruct st; split; only 2 : auto.
    intros.
    assert (p <> q) by sfirstorder.
    symmetry.
    eapply PathMap.get_set_diff; eauto.
  - destruct st.
    sfirstorder.
Qed.

Local Hint Resolve write_modifies_intro : core.

Lemma stmt_modifies_assign : forall p tags lhs rhs typ p' vars exts,
  is_call_expression rhs = false ->
  get_lexpr_base lhs = Some p' ->
  In_vars p' vars ->
  stmt_modifies p (MkStatement tags (StatAssignment lhs rhs) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H2. 2 : {
    (* rule out the call case *)
    inv H11; inv H.
  }
  destruct sig; simpl in *; subst; eauto.
Qed.

End Modifies.
