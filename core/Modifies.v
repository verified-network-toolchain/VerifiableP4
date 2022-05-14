Require Import Coq.Lists.List.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.ConcreteHoare.
Require Import ProD3.core.ExtPred.
Require Import Hammer.Plugin.Hammer.

Section Modifies.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}.

Context (ge : genv).

Definition modifies_vars (vars : option (list path)) (st st' : state) : Prop :=
  match vars with
  | Some vars =>
      forall q, ~(In q vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st')
  | None => True
  end.

Definition modifies_exts (exts : list path) (st st' : state) : Prop :=
  forall q, ~(in_scopes q exts) -> PathMap.get q (snd st) = PathMap.get q (snd st').

Hint Unfold modifies_exts modifies_vars : core.

Definition modifies (vars : option (list path)) (exts : list path) (st st' : state) : Prop :=
  modifies_vars vars st st' /\ modifies_exts exts st st'.

Definition func_modifies_vars (p : path) (func : @fundef tags_t) (vars : option (list path)) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    modifies_vars vars st st'.

Definition func_modifies_exts (p : path) (func : @fundef tags_t) (exts : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    modifies_exts exts st st'.

Lemma modifies_refl : forall (vars : option (list path)) (exts : list path) (st : state),
  modifies vars exts st st.
Proof.
  unfold modifies, modifies_exts, modifies_vars; intros; destruct vars; auto.
Qed.

Local Hint Resolve modifies_refl : core.

Lemma modifies_trans : forall (vars : option (list path)) (exts : list path) (st1 st2 st3 : state),
  modifies vars exts st1 st2 ->
  modifies vars exts st2 st3 ->
  modifies vars exts st1 st3.
Proof.
  intros. unfold modifies, modifies_exts, modifies_vars in *.
  fcrush.
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
  match lv with
  | ValLeftName (LInstance p) => Some p
  | ValLeftName (LGlobal _) => None
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

Lemma In_vars_None : forall p,
  In_vars p None.
Proof.
  intros; apply I.
Qed.

Lemma In_vars_Some : forall p vars,
  In p vars ->
  In_vars p (Some vars).
Proof.
  intros; apply H.
Qed.

Lemma write_var_modifies_intro : forall p v vars exts st,
  In_vars p vars ->
  modifies vars exts st (update_memory (PathMap.set p v) st).
Proof.
  unfold modifies, modifies_exts, modifies_vars; intros; destruct st.
  destruct vars as [vars | ].
  - split. 2 : sfirstorder.
    intros.
    unfold In_vars in H. simpl in H.
    assert (p <> q) by sfirstorder.
    symmetry.
    eapply PathMap.get_set_diff; eauto.
  - sfirstorder.
Qed.

Local Hint Resolve write_var_modifies_intro : core.

Lemma write_modifies_intro : forall lv p st sv st' vars exts,
  get_lval_base lv = Some p ->
  exec_write st lv sv st' ->
  In_vars p vars ->
  modifies vars exts st st'.
Proof.
  induction 2; intros; simpl in *; only 2, 3, 4, 5 : eauto.
  destruct loc; inv H.
  eapply write_var_modifies_intro; auto.
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
  destruct H14 as [? [? [? ?]]]; subst; eauto.
Qed.

Lemma stmt_modifies_method_call : forall p tags func targs args typ vars exts,
  call_modifies p (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless)
      vars exts ->
  stmt_modifies p (MkStatement tags (StatMethodCall func targs args) typ) vars exts.
Proof.
  unfold call_modifies, stmt_modifies. intros.
  inv H0; eauto.
Qed.

Lemma stmt_modifies_var : forall p tags typ' name e p' typ vars exts,
  is_call_expression e = false ->
  In_vars p' vars ->
  stmt_modifies p (MkStatement tags (StatVariable typ' name (Some e) (LInstance p')) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H1. 2 : {
    (* rule out the call case *)
    inv H12; inv H.
  }
  inv H14. eapply write_var_modifies_intro; auto.
Qed.

Lemma stmt_modifies_var_call : forall p tags typ' name e p' typ vars exts,
  is_call_expression e = true ->
  call_modifies p e vars exts ->
  In_vars p' vars ->
  stmt_modifies p (MkStatement tags (StatVariable typ' name (Some e) (LInstance p')) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H2. 1 : {
    (* rule out the non-call case *)
    pose proof (exec_expr_det_not_call _ _ _ _ _ _ H13).
    congruence.
  }
  destruct sig0; only 1, 3, 4 : destruct H14; subst; eauto.
  destruct H14; subst.
  eapply modifies_trans.
  - eapply H0; eauto.
  - eapply write_modifies_intro; eauto.
    eauto.
Qed.

Lemma stmt_modifies_direct_application : forall p tags typ' func_typ args typ vars exts,
  call_modifies p
    (MkExpression dummy_tags (ExpFunctionCall
          (direct_application_expression typ' func_typ)
          nil args) TypVoid Directionless)
    vars exts ->
  stmt_modifies p (MkStatement tags (StatDirectApplication typ' func_typ args) typ) vars exts.
Proof.
  unfold call_modifies, stmt_modifies; intros.
  inv H0; eauto.
Qed.

Lemma stmt_modifies_if : forall p tags cond tru ofls typ vars exts,
  stmt_modifies p tru vars exts ->
  stmt_modifies p (force empty_statement ofls) vars exts ->
  stmt_modifies p (MkStatement tags (StatConditional cond tru ofls) typ) vars exts.
Proof.
  unfold stmt_modifies. intros.
  inv H1; destruct b; eauto.
Qed.

Lemma stmt_modifies_if_none : forall p tags cond tru typ vars exts,
  stmt_modifies p tru vars exts ->
  stmt_modifies p empty_statement vars exts ->
  stmt_modifies p (MkStatement tags (StatConditional cond tru None) typ) vars exts.
Proof.
  intros; eapply stmt_modifies_if; eauto.
Qed.

Lemma stmt_modifies_if_some : forall p tags cond tru fls typ vars exts,
  stmt_modifies p tru vars exts ->
  stmt_modifies p fls vars exts ->
  stmt_modifies p (MkStatement tags (StatConditional cond tru (Some fls)) typ) vars exts.
Proof.
  intros; eapply stmt_modifies_if; eauto.
Qed.

Lemma stmt_modifies_block : forall p tags block typ vars exts,
  block_modifies p block vars exts ->
  stmt_modifies p (MkStatement tags (StatBlock block) typ) vars exts.
Proof.
  unfold block_modifies, stmt_modifies; intros.
  inv H0; eauto.
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
  exec_call_copy_out (combine (map snd argvals) dirs) outvals st st' ->
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

Inductive incl_vars : (option (list path)) -> (option (list path)) -> Prop :=
| incl_vars_None_None :
    incl_vars None None
| incl_vars_None_Some : forall vars',
    incl_vars None (Some vars')
| incl_vars_Some_Some : forall vars vars',
    Forall (fun x => In x vars) vars' ->
    incl_vars (Some vars) (Some vars').

Lemma Forall_In : forall {A} (l l' : list A),
  Forall (fun x => In x l) l' ->
  forall x,
    In x l' ->
    In x l.
Proof.
  induction 1; intros.
  - inv H.
  - inv H1; auto.
Qed.

Lemma modifies_exts_incl:
     forall (exts exts' : list path) st st',
       modifies_exts exts' st st' ->
       (forall x : path, In x exts' -> In x exts) -> modifies_exts exts st st'.
Proof.
  intros. unfold modifies_exts in *. intros. apply H.
  intro. apply H1. eapply in_scopes_incl; eauto.
Qed.

Lemma func_modifies_frame : forall p fd vars exts vars' exts',
  func_modifies p fd vars' exts' ->
  incl_vars vars vars' ->
  Forall (fun x => in_scopes x exts) exts' ->
  func_modifies p fd vars exts.
Proof.
  unfold func_modifies.
  intros.
  apply H in H2. clear H.
  unfold modifies in *; destruct st; destruct st'.
    assert (forall q, in_scopes q exts' -> in_scopes q exts). {
      clear -H1; intros.
      induction H1.
      - inv H.
      - simpl in H. rewrite Reflect.orE in H. destruct H.
        + eauto using in_scopes_trans.
        + auto.
    }
    inv H0;
    try pose proof (Forall_In _ _ H3);
    split; destruct H2; try sfirstorder;
    eapply modifies_exts_incl; eauto.
Qed.

Lemma func_modifies_internal_part1 : forall in_params vars exts st inargs,
  Forall (fun x => In_vars x vars) in_params ->
  modifies vars exts st (update_memory (PathMap.sets in_params inargs) st).
Proof.
  intros.
  revert inargs st.
  induction H; intros.
  - destruct st; auto.
  - destruct inargs.
    + destruct st; auto.
    + destruct st; simpl.
    eapply modifies_trans.
    * refine (write_var_modifies_intro _ _ _ _ _ _); eauto.
    * refine (IHForall _ _).
Qed.

Lemma func_modifies_internal : forall p params body vars exts,
  Forall (fun x => In_vars x vars) (filter_in params) ->
  block_modifies p body vars exts ->
  func_modifies p (FInternal params body) vars exts.
Proof.
  unfold block_modifies, func_modifies.
  intros.
  inv H1.
  eauto using func_modifies_internal_part1.
Qed.

End Modifies.

(* Importnant note: in order to avoid backtracking, there should be only one hint
  works in one case. *)

#[export] Hint Resolve In_vars_None In_vars_Some : modifies.
#[export] Hint Resolve in_eq in_cons : modifies.
#[export] Hint Constructors Forall : modifies.
#[export] Hint Constructors incl_vars : modifies.
#[export] Hint Extern 0 (Forall _ (filter_in _)) => (progress (simpl filter_in)) : modifies.
#[export] Hint Extern 0 (Forall2 _ _ (get_arg_directions _))
    => (progress (simpl get_arg_directions)) : modifies.
#[export] Hint Constructors Forall2 : modifies.
#[export] Hint Resolve block_modifies_nil : modifies.
#[export] Hint Resolve block_modifies_cons : modifies.
#[export] Hint Resolve
    stmt_modifies_assign stmt_modifies_assign_call stmt_modifies_method_call stmt_modifies_direct_application
    stmt_modifies_var stmt_modifies_var_call stmt_modifies_if_none stmt_modifies_if_some stmt_modifies_block
    : modifies.
#[export] Hint Resolve call_modifies_builtin call_modifies_func : modifies.
#[export] Hint Extern 2 (func_modifies _ _ _ _ _) => apply func_modifies_internal : modifies.
(* This is needed, because (simple apply eq_refl) cannot unify. I don't think it causes any
  backtracking, because it seems eauto does not backtrack terminal rules. *)
#[export] Hint Extern 0 (eq _ (Some _)) => reflexivity : modifies.
#[export] Hint Extern 1 (is_true _) => reflexivity : modifies.
#[export] Hint Resolve eq_refl : modifies.
#[export] Hint Constructors out_arg_In_vars : modifies.
(* Apply func_modifies_frame only if there is already a function body proof. *)
#[export] Hint Extern 1 (func_modifies _ _ _ _ _) =>
  eapply func_modifies_frame; only 1 : solve [eauto 15 with nocore func_specs] : modifies.
