Require Import Coq.NArith.BinNat.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import Poulet4.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Lemma path_eqb_refl : forall (p : list String.string),
  path_eqb p p.
Proof.
  unfold path_eqb, list_eqb.
  induction p.
  - auto.
  - simpl. rewrite String.eqb_refl. auto.
Qed.

#[export] Hint Resolve path_eqb_refl : core.

Section Hoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation Expression := (@Expression tags_t).

Context `{@Target tags_t Expression}.

Variable ge : (@genv tags_t _).

(* shallow assertions *)
Definition assertion := state -> Prop.
Definition arg_assertion := list Sval -> state -> Prop.
Definition ret_assertion := Val -> state -> Prop.
Definition arg_ret_assertion := list Sval -> Val -> state -> Prop.

Record post_assertion := mk_post_assertion {
  post_continue :> assertion;
  post_return : ret_assertion
}.

Definition continue_post_assertion (a : assertion) : post_assertion :=
  mk_post_assertion a (fun _ _ => False).

Definition return_post_assertion (a : ret_assertion) : post_assertion :=
  mk_post_assertion (fun _ => False) a.

(* Either finish with a return statement or return (ValBaseNull) by default. *)
Definition return_post_assertion_1 (a : ret_assertion) : post_assertion :=
  mk_post_assertion (a ValBaseNull) a.

Definition hoare_expr (p : path) (pre : assertion) (expr : Expression) (sv : Sval) :=
  forall st sv',
    pre st ->
    exec_expr ge read_ndetbit p st expr sv' ->
    sval_refine sv sv'.

Definition hoare_expr_1 (p : path) (pre : assertion) (expr : Expression) (sv : Sval) :=
  forall st,
    pre st ->
    exec_expr ge read_ndetbit p st expr sv.

Definition hoare_expr_det (p : path) (pre : assertion) (expr : Expression) (sv : Sval) :=
  forall st v' sv',
    pre st ->
    exec_expr_det ge read_ndetbit p st expr v' ->
    val_to_sval v' sv' ->
    sval_refine sv sv'.

Definition locator_eqb (loc1 loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_eqb p1 p2
  | LGlobal p1, LGlobal p2 => path_eqb p1 p2
  | _, _ => false
  end.

(* lval_eqb ignores the "name" argument of ValLeftName, because I believe this field should be removed. *)
Fixpoint lval_eqb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | ValLeftName loc1, ValLeftName loc2 =>
      locator_eqb loc1 loc2
  | ValLeftMember lv1 member1, ValLeftMember lv2 member2 =>
      lval_eqb lv1 lv2 && String.eqb member1 member2
  | ValLeftBitAccess lv1 msb1 lsb1, ValLeftBitAccess lv2 msb2 lsb2 =>
      lval_eqb lv1 lv2 && N.eqb msb1 msb2 && N.eqb lsb1 lsb2
  | ValLeftArrayAccess lv1 idx1, ValLeftArrayAccess lv2 idx2 =>
      lval_eqb lv1 lv2 && BinInt.Z.eqb idx1 idx2
  | _, _ => false
  end.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) :=
  forall st lv' sig,
    pre st ->
    exec_lexpr ge read_ndetbit p st expr lv' sig ->
    sig = SContinue /\ lval_eqb lv lv'.

Definition hoare_read_var (pre : assertion) (p : path) (sv : Sval) :=
  forall st sv',
    pre st ->
    PathMap.get p (fst st) = Some sv' ->
    sval_refine sv sv'.

Definition hoare_write_var (pre : assertion) (p : path) (sv : Sval) (post : assertion) :=
  forall st sv' st',
    pre st ->
    sval_refine sv sv' ->
    update_memory (PathMap.set p sv') st = st' ->
    post st'.

Definition hoare_read (pre : assertion) (lv : Lval) (sv : Sval) :=
  forall st sv',
    pre st ->
    exec_read st lv sv' ->
    sval_refine sv sv'.

Definition hoare_write (pre : assertion) (lv : Lval) (sv : Sval) (post : assertion) :=
  forall st sv' st',
    pre st ->
    sval_refine sv sv' ->
    exec_write st lv sv' st' ->
    post st'.

Definition hoare_read_vars (pre : assertion) (ps : list path) (svs : list Sval) :=
  forall st svs',
    pre st ->
    PathMap.gets ps (fst st) = map Some svs' ->
    Forall2 sval_refine svs svs'.

Definition hoare_read_vars' (pre : assertion) (ps : list path) (svs : list Sval) :=
  Forall2 (hoare_read_var pre) ps svs.

Lemma hoare_read_vars_intro : forall pre ps svs,
  hoare_read_vars' pre ps svs ->
  hoare_read_vars pre ps svs.
Proof.
  induction 1.
  - unfold hoare_read_vars; intros. destruct svs'; inv H1. constructor.
  - unfold hoare_read_vars in *; intros.
    destruct svs'; inv H3.
    constructor; eauto.
Qed.

Definition hoare_write_vars (pre : assertion) (ps : list path) (svs : list Sval) (post : assertion) :=
  forall st svs' st',
    pre st ->
    Forall2 sval_refine svs svs' ->
    update_memory (PathMap.sets ps svs') st = st' ->
    post st'.

Definition hoare_write_vars' (pre : assertion) (ps : list path) (svs : list Sval) (post : assertion) :=
  Forall2_fold hoare_write_var pre ps svs post.

Lemma hoare_write_vars_intro : forall pre ps svs post,
  hoare_write_vars' pre ps svs post ->
  hoare_write_vars pre ps svs post.
Proof.
  induction 1.
  - unfold hoare_write_vars; intros. subst; destruct st; auto.
  - unfold hoare_write_vars in *; intros.
    subst; inv H3; destruct st; eapply IHForall2_fold; eauto.
Qed.

Definition hoare_write_option (pre : assertion) (lv : option Lval) (sv : Sval) (post : assertion) :=
  forall st sv' st',
    pre st ->
    sval_refine sv sv' ->
    exec_write_option st lv sv' st' ->
    post st'.

Definition hoare_write_options (pre : assertion) (lvs : list (option Lval)) (svs : list Sval) (post : assertion) :=
  forall st svs' st',
    pre st ->
    Forall2 sval_refine svs svs' ->
    exec_write_options st lvs svs' st' ->
    post st'.

Definition hoare_reads' (pre : assertion) (lvs : list Lval) (svs : list Sval) :=
  Forall2 (hoare_read pre) lvs svs.

Definition hoare_writes' (pre : assertion) (lvs : list Lval) (svs : list Sval) (post : assertion) :=
  Forall2_fold hoare_write pre lvs svs post.


Definition satisfies_ret_assertion (post : ret_assertion) (sig : signal) (st : state) : Prop :=
  match sig with
  | SReturn vret => post vret st
  | _ => False
  end.

Definition satisfies_arg_ret_assertion (post : arg_ret_assertion) (args : list Sval) (sig : signal) (st : state) : Prop :=
  match sig with
  | SReturn vret => post args vret st
  | _ => False
  end.

(* Semantic Hoare judgments. *)

Definition hoare_stmt (p : path) (pre : assertion) (stmt : Statement) (post : post_assertion) :=
  forall st st' sig,
    pre st ->
    exec_stmt ge read_ndetbit p st stmt st' sig ->
    (sig = SContinue /\ (post_continue post) st')
      \/ satisfies_ret_assertion (post_return post) sig st'.

Definition hoare_block (p : path) (pre : assertion) (block : Block) (post : post_assertion) :=
  forall st st' sig,
    pre st ->
    exec_block ge read_ndetbit p st block st' sig ->
    (sig = SContinue /\ (post_continue post) st')
      \/ satisfies_ret_assertion (post_return post) sig st'.

Definition hoare_call (p : path) (pre : assertion) (expr : Expression) (post : ret_assertion) :=
  forall st st' sig,
    pre st ->
    exec_call ge read_ndetbit p st expr st' sig ->
    satisfies_ret_assertion post sig st'.

Definition hoare_func (p : path) (pre : arg_assertion) (func : @fundef tags_t) (targs : list P4Type) (post : arg_ret_assertion) :=
  forall st inargs st' outargs sig,
    pre inargs st ->
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    satisfies_arg_ret_assertion post outargs sig st'.

(* Hoare proof rules ass lemmas. *)

Definition is_call_expression (expr : Expression) : bool :=
  match expr with
  | MkExpression _ (ExpFunctionCall _ _ _) _ _ => true
  | _ => false
  end.

Lemma bit_to_nbit_to_bit : forall nb b nb',
  read_ndetbit nb b ->
  read_detbit b nb' ->
  bit_refine nb nb'.
Proof.
  intros.
  inv H0; inv H1; constructor.
Qed.

Lemma sval_to_val_to_sval : forall (sv : Sval) (v : Val) (sv' : Sval),
  sval_to_val read_ndetbit sv v ->
  val_to_sval v sv' ->
  sval_refine sv sv'.
Proof.
  apply exec_val_trans. exact bit_to_nbit_to_bit.
Qed.

Lemma hoare_expr_det_intro : forall (p : path) (pre : assertion) (expr : Expression) (sv : Sval),
  hoare_expr p pre expr sv ->
  hoare_expr_det p pre expr sv.
Proof.
  unfold hoare_expr, hoare_expr_det. intros.
  inv H2.
  eapply sval_refine_trans.
  - eapply H0; eauto.
  - eapply sval_to_val_to_sval; eauto.
Qed.

(* This is currently not true. *)
Axiom lval_eqb_eq : forall (lv1 lv2 : Lval),
  lval_eqb lv1 lv2 ->
  lv1 = lv2.

Ltac specialize_hoare_block :=
  lazymatch goal with
  | H : hoare_block _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_block _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_stmt :=
  match goal with
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
  end.

Lemma hoare_stmt_assign : forall p pre tags lhs rhs typ post lv sv,
  is_call_expression rhs = false ->
  hoare_lexpr p pre lhs lv ->
  hoare_expr_det p pre rhs sv ->
  hoare_write pre lv sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H5. 2 : {
    (* rule out the call case *)
    inv H14; inv H0.
  }
  specialize_hoare_lexpr.
  inv H1.
  split; only 1 : split.
  apply lval_eqb_eq in H6. subst lv0.
  specialize_hoare_expr_det.
  eapply H3; eauto.
Qed.

Lemma exec_expr_not_call : forall read_one_bit p st expr sv,
  exec_expr ge read_one_bit p st expr sv ->
  is_call_expression expr = false.
Proof.
  intros. inv H0; auto.
Qed.

Lemma exec_expr_det_not_call : forall read_one_bit p st expr v,
  exec_expr_det ge read_one_bit p st expr v ->
  is_call_expression expr = false.
Proof.
  intros. inv H0; eapply exec_expr_not_call; eauto.
Qed.

Lemma hoare_stmt_assign_call : forall p pre tags lhs rhs typ post lv mid sv,
  is_call_expression rhs = true ->
  hoare_lexpr p pre lhs lv ->
  hoare_call p pre rhs (fun v st => (forall sv', val_to_sval v sv' -> sval_refine sv sv') /\ mid st) ->
  hoare_write mid lv sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H5. 1 : {
    (* rule out the non-call case *)
    pose proof (exec_expr_det_not_call _ _ _ _ _ H12).
    congruence.
  }
  specialize_hoare_lexpr.
  inv H1.
  apply lval_eqb_eq in H6. subst lv0.
  specialize_hoare_call.
  destruct sig'; only 1, 3, 4 : solve[inv H2].
  destruct H2. destruct H16 as [? []].
  split; only 1 : auto.
  inv H5.
  eapply H3; eauto.
Qed.

Lemma hoare_stmt_method_call : forall p pre tags func targs args typ post sv,
  hoare_call p pre
    (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless)
    (fun v st => (forall sv', val_to_sval v sv' -> sval_refine sv sv') /\ (post_continue post) st) ->
  hoare_stmt p pre (MkStatement tags (StatMethodCall func targs args) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H2.
  specialize_hoare_call.
  destruct sig0; only 1, 3, 4 : solve [inv H0].
  destruct H0.
  auto.
Qed.

Lemma hoare_stmt_var : forall p pre tags typ' name e loc typ post sv,
  is_call_expression e = false ->
  hoare_expr_det p pre e sv ->
  hoare_write pre (ValLeftName loc) sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatVariable typ' name (Some e) loc) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H4. 2 : {
    (* rule out the call case *)
    inv H15; inv H0.
  }
  specialize_hoare_expr_det.
  specialize_hoare_write.
  auto.
Qed.

Lemma hoare_stmt_var_call : forall p pre tags typ' name e loc typ post mid sv,
  is_call_expression e = true ->
  hoare_call p pre e (fun v st => (forall sv', val_to_sval v sv' -> sval_refine sv sv') /\ mid st) ->
  hoare_write mid (ValLeftName loc) sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatVariable typ' name (Some e) loc) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H4. 1 : {
    (* rule out the non-call case *)
    pose proof (exec_expr_det_not_call _ _ _ _ _ ltac:(eassumption)).
    congruence.
  }
  specialize_hoare_call.
  destruct sig0; only 1, 3, 4 : solve[inv H1].
  destruct H1. destruct H16.
  split; only 1 : auto.
  inv H5.
  eapply H2; eauto.
Qed.

Lemma hoare_stmt_direct_application : forall p pre tags typ' func_typ args typ post sv,
  hoare_call p pre
    (MkExpression dummy_tags (ExpFunctionCall
          (direct_application_expression typ' func_typ)
          nil args) TypVoid Directionless)
    (fun v st => (forall sv', val_to_sval v sv' -> sval_refine sv sv') /\ (post_continue post) st) ->
  hoare_stmt p pre (MkStatement tags (StatDirectApplication typ' func_typ args) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H2.
  specialize_hoare_call.
  destruct sig0; only 1, 3, 4 : solve [inv H0].
  destruct H0.
  auto.
Qed.

Lemma hoare_stmt_if_true : forall p pre tags cond tru ofls typ post,
  hoare_expr_det p pre cond (ValBaseBool (Some true)) ->
  hoare_stmt p pre tru post ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  unfold hoare_stmt. intros.
  inv H3.
  - specialize_hoare_expr_det.
    inv H0. inv H5.
    specialize_hoare_stmt.
    auto.
  - specialize_hoare_expr_det.
    inv H0. inv H5.
    specialize_hoare_stmt.
    auto.
Qed.

Lemma hoare_stmt_if_false : forall p pre tags cond tru ofls typ post,
  hoare_expr_det p pre cond (ValBaseBool (Some false)) ->
  hoare_stmt p pre (force empty_statement ofls) post ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  unfold hoare_stmt. intros.
  inv H3.
  - specialize_hoare_expr_det.
    inv H0. inv H5.
    specialize_hoare_stmt.
    auto.
  - specialize_hoare_expr_det.
    inv H0. inv H5.
    specialize_hoare_stmt.
    auto.
Qed.

Definition is_sval_true (v : Sval) :=
  match v with
  | ValBaseBool (Some true)
  | ValBaseBool None
      => True
  | _ => False
  end.

Definition is_sval_false (v : Sval) :=
  match v with
  | ValBaseBool (Some false)
  | ValBaseBool None
      => True
  | _ => False
  end.

Lemma hoare_stmt_if : forall p pre tags cond tru ofls typ post sv,
  hoare_expr_det p pre cond sv ->
  (is_sval_true sv -> hoare_stmt p pre tru post) ->
  (is_sval_false sv -> hoare_stmt p pre (force empty_statement ofls) post) ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  unfold hoare_stmt. intros.
  inv H4;
    specialize_hoare_expr_det;
    inv H0; destruct b; inv H6;
    try specialize (H1 I);
    try specialize (H2 I);
    specialize_hoare_stmt;
    auto.
Qed.

Lemma hoare_stmt_block : forall p pre tags block typ post,
  hoare_block p pre block post ->
  hoare_stmt p pre (MkStatement tags (StatBlock block) typ) post.
Proof.
  unfold hoare_block, hoare_stmt; intros.
  inv H2; eauto.
Qed.

(* These two lemmas about return statements may need adjustment. *)

Lemma hoare_stmt_return_none : forall p (pre : assertion) tags typ post,
  (forall st v, pre st -> (forall sv', val_to_sval v sv' -> sval_refine ValBaseNull sv') -> (post_return post) v st) ->
  hoare_stmt p pre (MkStatement tags (StatReturn None) typ) post.
Proof.
  unfold hoare_stmt; intros.
  inv H2; right; apply H0; eauto.
  intros. inv H2. constructor.
Qed.

(* Maybe need some change in the lemma body. *)
Lemma hoare_stmt_return_some : forall p (pre : assertion) tags e typ post sv,
  hoare_expr_det p pre e sv ->
  (forall st v, pre st -> (forall sv', val_to_sval v sv' -> sval_refine sv sv') -> (post_return post) v st) ->
  hoare_stmt p pre (MkStatement tags (StatReturn (Some e)) typ) post.
Proof.
  unfold hoare_expr_det, hoare_stmt; intros.
  inv H3. right; eapply H1; eauto.
Qed.

Lemma hoare_stmt_empty : forall p post tags typ,
  hoare_stmt p (post_continue post) (MkStatement tags StatEmpty typ) post.
Proof.
  unfold hoare_stmt; intros.
  inv H1; auto.
Qed.

Definition implies (pre post : assertion) :=
  forall st, pre st -> post st.

Lemma hoare_block_nil : forall p pre post tags,
  implies pre (post_continue post) ->
  hoare_block p pre (BlockEmpty tags) post.
Proof.
  unfold hoare_block. intros. inv H2.
  auto.
Qed.

Lemma hoare_block_cons : forall p pre stmt mid block post_con post_ret,
  hoare_stmt p pre stmt (mk_post_assertion mid post_ret) ->
  hoare_block p mid block (mk_post_assertion post_con post_ret) ->
  hoare_block p pre (BlockCons stmt block) (mk_post_assertion post_con post_ret).
Proof.
  unfold hoare_stmt, hoare_block. intros.
  inv H3. destruct sig0.
  - sfirstorder.
  - inv H11. hauto.
  - inv H11. hauto.
  - inv H11. hauto.
Qed.

Lemma hoare_block_pre : forall p pre pre' block post,
  implies pre pre' ->
  hoare_block p pre' block post ->
  hoare_block p pre block post.
Proof.
  unfold implies, hoare_block.
  sfirstorder.
Qed.

Definition ret_implies (P Q : ret_assertion) :=
  forall retv st, P retv st -> Q retv st.

Definition arg_implies (P Q : arg_assertion) :=
  forall args st, P args st -> Q args st.

Definition post_implies (pre post : post_assertion) :=
  implies (post_continue pre) (post_continue post)
    /\ ret_implies (post_return pre) (post_return post).

Lemma hoare_block_post : forall p pre block post' post,
  hoare_block p pre block post' ->
  post_implies post' post ->
  hoare_block p pre block post.
Proof.
  unfold implies, hoare_block; intros.
  destruct post'; destruct post.
  specialize_hoare_block.
  destruct H0.
  - left. sauto.
  - right. destruct sig; only 1, 3, 4 : inv H0. sauto.
Qed.

Definition arg_refine (arg arg' : argument) :=
  match arg, arg' with
  | (osv, olv), (osv', olv') =>
      EquivUtil.relop sval_refine osv osv' /\ EquivUtil.relop (fun lv lv' => lval_eqb lv lv') olv olv'
  end.

Definition args_refine (args args' : list argument) :=
  Forall2 arg_refine args args'.

Definition hoare_builtin (p : path) (pre : arg_assertion) (lv : Lval) (fname : ident) (post : ret_assertion) :=
  forall st inargs st' sig,
    pre inargs st ->
    exec_builtin read_ndetbit p st lv fname inargs st' sig ->
    satisfies_ret_assertion post sig st'.

Definition hoare_arg (p : path) (pre : assertion) (arg : option Expression) dir argval :=
  forall st argval' sig,
    pre st ->
    exec_arg ge read_ndetbit p st arg dir argval' sig ->
    sig = SContinue /\ arg_refine argval argval'.

Definition hoare_args (p : path) (pre : assertion) (args : list (option Expression)) dirs argvals :=
  forall st argvals' sig,
    pre st ->
    exec_args ge read_ndetbit p st args dirs argvals' sig ->
    sig = SContinue /\ args_refine argvals argvals'.

Lemma args_refine_extract_invals : forall args args',
  args_refine args args' ->
  Forall2 sval_refine (extract_invals args) (extract_invals args').
Proof.
  intros.
  induction H0.
  - constructor.
  - destruct x as [[] []]; destruct y as [[] []];
      inv H0; inv H2; inv H3;
      only 1, 2 : constructor; auto.
Qed.

Lemma args_refine_map_snd : forall args args',
  args_refine args args' ->
  map snd args = map snd args'.
Proof.
  intros.
  induction H0.
  - constructor.
  - destruct x; destruct y.
    inv H0; inv H3; simpl; f_equal; auto.
    apply lval_eqb_eq in H0.
    f_equal; auto.
Qed.

Lemma hoare_call_builtin : forall p pre tags tags' expr fname tparams params typ' dir' args typ dir post lv argvals,
  let dirs := map get_param_dir params in
  hoare_lexpr p pre expr lv ->
  hoare_args p pre args dirs argvals ->
  hoare_builtin p (fun inargs st => Forall2 sval_refine (extract_invals argvals) inargs /\ pre st) lv (P4String.str fname) post ->
  hoare_call p pre
    (MkExpression tags (ExpFunctionCall
      (MkExpression tags' (ExpExpressionMember expr fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir)
      nil args) typ dir')
    post.
Proof.
  unfold hoare_lexpr, hoare_args, hoare_builtin, hoare_call.
  intros.
  inv H4. 2 : { inv H11. }
  specialize (H0 _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct H0 as [? H0]. subst.
  specialize (H1 _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct H1 as [? H1]. subst.
  assert (Forall2 sval_refine (extract_invals argvals) (extract_invals argvals0) /\ pre st). {
    split; auto using args_refine_extract_invals.
  }
  apply lval_eqb_eq in H0; subst.
  specialize (H2 _ _ _ _ ltac:(eassumption) H22).
  assumption.
Qed.

Definition hoare_call_copy_out (pre : arg_ret_assertion) (args : list (option Lval * direction)) (post : ret_assertion) : Prop :=
  forall outvals sig st st',
    satisfies_arg_ret_assertion pre outvals sig st ->
    exec_call_copy_out args outvals st  st' ->
      satisfies_ret_assertion post sig st'.

Lemma hoare_call_func : forall p (pre : assertion) tags func targs args typ dir post argvals obj_path fd
    (mid1 : arg_assertion) mid2 mid3,
  is_builtin_func func = false ->
  let dirs := get_arg_directions func in
  hoare_args p pre args dirs argvals ->
  lookup_func ge p func = Some (obj_path, fd) ->
  mid1 = (fun inargs st => Forall2 sval_refine (extract_invals argvals) inargs
    /\ (if is_some obj_path then (fun '(m, es) => m = PathMap.empty /\ exists m', pre (m', es)) else pre) st) ->
  hoare_func (force p obj_path) mid1 fd targs mid2 ->
  mid3 = (
    if is_some obj_path then
      (fun outargs retv '(m, es) => (exists es', pre (m, es')) /\ (exists m', mid2 outargs retv (m', es)))
    else
      mid2) ->
  hoare_call_copy_out mid3 (combine (map snd argvals) dirs) post ->
  hoare_call p pre (MkExpression tags (ExpFunctionCall func targs args) typ dir) post.
Proof.
  unfold hoare_args, hoare_func, hoare_call_copy_out, hoare_call.
  intros.
  inv H8. { inv H0. }
  specialize (H1 _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct H1 as [? H1]. subst.
  rewrite H2 in H19; inv H19.
  unshelve epose proof (H4 _ _ _ _ _ ltac:(shelve) H23). {
    split. { apply args_refine_extract_invals. auto. }
    destruct (is_some obj_path0).
    - destruct st. split; eauto.
    - auto.
  }
  subst dirs.
  erewrite <- args_refine_map_snd in H25 by eauto.
  unshelve epose proof (H6 _ sig' _ _ ltac:(shelve) H25). {
    destruct (is_some obj_path0).
    - destruct s3. destruct sig'; try solve [inv H3].
      split.
      + destruct st; eauto.
      + eauto.
    - auto.
  }
  inv H26.
  assumption.
Qed.

Definition hoare_func_copy_in (pre : arg_assertion) (params : list (path * direction)) (post : assertion) : Prop :=
  forall args st st',
    pre args st ->
    exec_func_copy_in params args st = st' ->
    post st'.

Definition hoare_func_copy_out (pre : ret_assertion) (params : list (path * direction)) (post : arg_ret_assertion) : Prop :=
  forall retv st,
    pre retv st ->
    forall args,
      exec_func_copy_out params st = Some args ->
      post args retv st.

Definition generate_post_condition (params : list (path * direction)) (post : arg_ret_assertion) : ret_assertion :=
  fun retv st =>
    forall args,
      exec_func_copy_out params st = Some args ->
      post args retv st.

Lemma hoare_func_internal : forall p pre params body targs mid1 mid2 post,
  hoare_func_copy_in pre params mid1 ->
  hoare_block p mid1 body (return_post_assertion_1 mid2) ->
  hoare_func_copy_out mid2 params post ->
  hoare_func p pre (FInternal params body) targs post.
Proof.
  unfold hoare_func_copy_in, hoare_block, hoare_func_copy_out, hoare_func.
  intros.
  inv H4.
  specialize (H0 _ _ _ H3 ltac:(reflexivity)).
  specialize (H1 _ _ _ H0 ltac:(eassumption)).
  destruct H1.
  - destruct H1 as [? H1]; subst.
    apply H2; auto.
  - destruct sig0; try solve [inv H1].
    apply H2; auto.
Qed.

Lemma implies_refl : forall (pre : assertion),
  implies pre pre.
Proof.
  unfold implies. intros; auto.
Qed.

Lemma implies_refl_post : forall (pre : assertion),
  implies pre (continue_post_assertion pre).
Proof.
  exact implies_refl.
Qed.

Section DeepEmbeddedHoare.

Lemma implies_trans : forall (pre mid post : assertion),
  implies pre mid ->
  implies mid post ->
  implies pre post.
Proof.
  unfold implies; intros; sfirstorder.
Qed.

(* It's possible to make these functinos and lemmas generic, but that's currently unneeded. *)

Fixpoint is_in (x : path) (al : list path) : bool :=
  match al with
  | y :: al => path_eqb y x || is_in x al
  | [] => false
  end.

Fixpoint is_no_dup (al : list path) : bool :=
  match al with
  | x :: al => ~~(is_in x al) && is_no_dup al
  | [] => true
  end.

Lemma not_is_in_not_In : forall x (al : list path),
  ~~(is_in x al) -> ~In x al.
Proof.
  induction al; intros.
  - auto.
  - simpl in H0. rewrite Reflect.negE, Reflect.orE in H0.
    intros [].
    + subst. rewrite path_eqb_refl in H0. auto.
    + rewrite Reflect.negE in IHal. apply IHal; auto.
Qed.

Lemma is_no_dup_NoDup : forall (al : list path),
  is_no_dup al -> NoDup al.
Proof.
  induction al; intros.
  - constructor.
  - simpl in H0. rewrite Reflect.andE in H0. destruct H0.
    constructor.
    + apply not_is_in_not_In; auto.
    + auto.
Qed.

End DeepEmbeddedHoare.

End Hoare.

Create HintDb hoare.
#[export] Hint Resolve hoare_expr_det_intro : hoare.
#[export] Hint Resolve is_no_dup_NoDup : hoare.
