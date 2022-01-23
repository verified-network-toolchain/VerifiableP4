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

Lemma stmt_modifies_assign : forall p tags lhs rhs typ lv vars exts,
  is_call_expression rhs = false ->
  get_lexpr_base lhs = Some lv ->
  In_vars lv vars ->
  stmt_modifies p (MkStatement tags (StatAssignment lhs rhs) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H2. 2 : {
    (* rule out the call case *)
    inv H11; inv H.
  }
  destruct sig; simpl in *; subst; eauto.
Qed.

Lemma stmt_modifies_assign_call : forall p tags lhs rhs typ lv vars exts,
  is_call_expression rhs = true ->
  call_modifies p rhs vars exts ->
  get_lexpr_base lhs = Some lv ->
  In_vars lv vars ->
  stmt_modifies p (MkStatement tags (StatAssignment lhs rhs) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H3. 1 : {
    (* rule out the non-call case *)
    pose proof (exec_expr_det_not_call _ _ _ _ _ _ H10).
    congruence.
  }
  destruct sig0; only 2, 3, 4 : destruct H14; subst; eauto.
  destruct sig'; only 1, 3, 4 : destruct H14; subst; eauto.
  destruct H14 as [? []]; subst; eauto.
Qed.

Lemma call_modifies_builtin : forall p tags tags' expr fname tparams params typ' dir' args typ dir lv vars exts,
  let dirs := map get_param_dir params in
  get_lexpr_base expr = Some lv ->
  In_vars lv vars ->
  call_modifies p
    (MkExpression tags (ExpFunctionCall
      (MkExpression tags' (ExpExpressionMember expr fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir)
      nil args) typ dir')
    vars exts.
Proof.
  unfold call_modifies.
  intros.
  inv H1. 2 : { inv H8. }
  destruct sig0; only 2, 3, 4 : destruct H19; subst; eauto.
  destruct sig'; only 1, 3, 4 : destruct H19; subst; eauto.
  destruct H19; subst; eauto.
Qed.

Inductive out_arg_In_vars (vars : option (list path)) : option Expression -> direction -> Prop :=
| out_arg_In_vars_in : forall expr,
    out_arg_In_vars vars expr Typed.In
| out_arg_In_vars_out_dontcare :
    out_arg_In_vars vars None Out
| out_arg_In_vars_out : forall expr lv,
    get_lexpr_base expr = Some lv ->
    In_vars lv vars ->
    out_arg_In_vars vars (Some expr) Out
| out_arg_In_vars_inout : forall expr lv,
    get_lexpr_base expr = Some lv ->
    In_vars lv vars ->
    out_arg_In_vars vars (Some expr) InOut.

Lemma call_modifies_func_part1 : forall p st0 st args dirs argvals sig outvals st' vars exts,
  Forall2 (out_arg_In_vars vars) args dirs ->
  exec_args ge read_ndetbit p st0 args dirs argvals sig ->
  exec_call_copy_out ge (combine (map snd argvals) dirs) outvals st st' ->
  modifies vars exts st st'.
Proof.
  intros * H.
  revert st0 st argvals sig outvals st'.
  induction H as [ | expr dir]; intros.
  - inv H; inv H0; auto.
  - inv H1. inv H9.
    + eauto.
    + inv H2. inv H5. eauto.
    + inv H2. inv H6. inv H. eauto.
    + inv H2. inv H9. inv H. eauto.
Qed.

Lemma call_modifies_func : forall p tags func targs args typ dir obj_path fd vars exts,
  is_builtin_func func = false ->
  let dirs := get_arg_directions func in
  Forall2 (out_arg_In_vars vars) args dirs ->
  lookup_func ge p func = Some (obj_path, fd) ->
  func_modifies (force p obj_path) fd (if is_some obj_path then None else vars) exts ->
  call_modifies p (MkExpression tags (ExpFunctionCall func targs args) typ dir) vars exts.
Proof.
  unfold call_modifies, func_modifies.
  intros.
  inv H3. { inv H. }
  rewrite H1 in H14; inv H14.
  assert (modifies vars exts st (if is_some obj_path0 then set_memory (get_memory st) s3 else s3)). {
    destruct (is_some obj_path0).
    - destruct st. destruct s3.
      apply H2 in H18.
      destruct H18; destruct vars; split; eauto.
    - eauto.
  }
  assert (modifies vars exts (if is_some obj_path0 then set_memory (get_memory st) s3 else s3) s5). {
    eapply call_modifies_func_part1; eauto.
  }
  destruct sig0; destruct H21; subst; eauto.
Qed.

End Modifies.
