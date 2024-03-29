Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import Poulet4.P4light.Syntax.SyntaxUtil.
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

Definition hoare_expr_det (p : path) (pre : assertion) (expr : Expression) (sv : Sval) :=
  forall st v' sv',
    pre st ->
    exec_expr_det ge read_ndetbit p st expr v' ->
    val_to_sval v' sv' ->
    sval_refine sv sv'.

Definition hoare_expr_det' (p : path) (pre : assertion) (expr : Expression) (sv : Sval) :=
  forall st v',
    pre st ->
    exec_expr_det ge read_ndetbit p st expr v' ->
    sval_to_val read_ndetbit sv v'.

Definition hoare_exprs_det (p : path) (pre : assertion) (exprs : list Expression) (svs : list Sval) :=
  forall st vs' svs',
    pre st ->
    exec_exprs_det ge read_ndetbit p st exprs vs' ->
    Forall2 val_to_sval vs' svs' ->
    Forall2 sval_refine svs svs'.

Definition hoare_exprs_det' (p : path) (pre : assertion) (exprs : list Expression) (svs : list Sval) :=
  forall st vs',
    pre st ->
    exec_exprs_det ge read_ndetbit p st exprs vs' ->
    Forall2 (sval_to_val read_ndetbit) svs vs'.

Lemma hoare_exprs_det'_hoare_exprs_det : forall p pre exprs svs,
  hoare_exprs_det' p pre exprs svs ->
  hoare_exprs_det p pre exprs svs.
Proof.
  unfold hoare_exprs_det', hoare_exprs_det.
  intros.
  specialize (H0 _ _ ltac:(eassumption) ltac:(eassumption)).
  eapply Forall2_trans; only 2, 3 : eassumption.
  red; eapply exec_val_trans.
  red; clear; sauto lq: on.
Qed.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) :=
  forall st lv' sig,
    pre st ->
    exec_lexpr ge read_ndetbit p st expr lv' sig ->
    sig = SContinue /\ lv = lv'.

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

(* Major semantic Hoare judgments. *)

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

(* Auxiliary Hoare judgments. *)

Definition hoare_table_match (p : path) (pre : assertion) (name : ident) (keys : list TableKey)
      (const_entries : option (list table_entry)) (matched_action : option action_ref) :=
  forall st matched_action',
    pre st ->
    exec_table_match ge read_ndetbit p st name keys const_entries matched_action' ->
    matched_action' = matched_action.

Definition hoare_call_copy_out (pre : arg_ret_assertion) (args : list (option Lval * direction)) (post : ret_assertion) : Prop :=
  forall outvals sig st st',
    satisfies_arg_ret_assertion pre outvals sig st ->
    exec_call_copy_out args outvals st  st' ->
      satisfies_ret_assertion post sig st'.

(* Tactics for forward proof. *)

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
      specialize (H _ _ _ ltac:(eassumption) ltac:(first [eassumption | apply sval_refine_refl]) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_write _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(first [eassumption | apply sval_refine_refl]) ltac:(eassumption))
  end.

Ltac specialize_hoare_call :=
  lazymatch goal with
  | H : hoare_call _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_call _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

Ltac specialize_hoare_func :=
  match goal with
  | H : hoare_func _ _ _ _ _ |- _ =>
      specialize (H _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _ _ _ , _ -> exec_func _ _ _ _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

(* Hoare proof rules as lemmas. *)

(* Assertion implies. *)

Definition implies (P Q : assertion) :=
  forall st, P st -> Q st.

Definition ret_implies (P Q : ret_assertion) :=
  forall retv st, P retv st -> Q retv st.

Definition arg_implies (P Q : arg_assertion) :=
  forall args st, P args st -> Q args st.

Definition arg_ret_implies (P Q : arg_ret_assertion) :=
  forall args retv st, P args retv st -> Q args retv st.

Definition post_implies (pre post : post_assertion) :=
  implies (post_continue pre) (post_continue post)
    /\ ret_implies (post_return pre) (post_return post).

Lemma ret_implies_refl : forall P,
  ret_implies P P.
Proof.
  sfirstorder.
Qed.

Lemma arg_ret_implies_refl : forall P : Hoare.arg_ret_assertion,
  arg_ret_implies P P.
Proof.
  sfirstorder.
Qed.

(* Pre and post rules. *)

Lemma hoare_block_pre : forall p pre pre' block post,
  implies pre pre' ->
  hoare_block p pre' block post ->
  hoare_block p pre block post.
Proof.
  sfirstorder.
Qed.

Lemma hoare_block_pre_prop : forall p (P : Prop) pre block post,
  (P -> hoare_block p pre block post) ->
  hoare_block p (fun st : state => P /\ pre st) block post.
Proof.
  unfold hoare_block.
  intros.
  hauto lq: on.
Qed.

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

Lemma hoare_func_pre : forall p pre pre' func targs post,
  arg_implies pre pre' ->
  hoare_func p pre' func targs post ->
  hoare_func p pre func targs post.
Proof.
  sfirstorder.
Qed.

Lemma hoare_func_post : forall p pre func targs post post',
  hoare_func p pre func targs post' ->
  arg_ret_implies post' post ->
  hoare_func p pre func targs post.
Proof.
  unfold hoare_func, arg_ret_implies; intros.
  specialize_hoare_func.
  destruct sig; sfirstorder.
Qed.

(* This lemma may be not really used. *)
Lemma hoare_call_post : forall p pre expr post post',
  hoare_call p pre expr post' ->
  ret_implies post' post ->
  hoare_call p pre expr post.
Proof.
  unfold hoare_call, ret_implies; intros.
  specialize_hoare_call.
  destruct sig; sfirstorder.
Qed.

Lemma hoare_call_copy_out_pre : forall (pre pre' : Hoare.arg_ret_assertion) args post,
  arg_ret_implies pre pre' ->
  (* (forall args sig st, satisfies_arg_ret_assertion pre args sig st ->
      satisfies_arg_ret_assertion pre' args sig st) -> *)
  hoare_call_copy_out pre' args post ->
  hoare_call_copy_out pre args post.
Proof.
  clear ge.
  unfold hoare_call_copy_out; intros.
  assert (satisfies_arg_ret_assertion pre' outvals sig st). {
    destruct sig; sfirstorder.
  }
  sfirstorder.
Qed.

(* Exists. *)

Definition assr_exists {A} (P : A -> assertion) : Hoare.assertion :=
  fun st => ex (fun x => P x st).

Definition ret_exists {A} (P : A -> ret_assertion) : Hoare.ret_assertion :=
  fun retv st => ex (fun x => P x retv st).

Definition arg_ret_exists {A} (P : A -> arg_ret_assertion) : Hoare.arg_ret_assertion :=
  fun args retv st => ex (fun x => P x args retv st).

Lemma arg_ret_implies_post_ex : forall {A} P (Q : A -> _),
  (exists x, arg_ret_implies P (Q x)) ->
  arg_ret_implies P (arg_ret_exists Q).
Proof.
  clear ge.
  sfirstorder.
Qed.

(* Pre and post ex rules. *)
Lemma hoare_block_pre_ex : forall {A} p (pre : A -> _) block post,
  (forall x, hoare_block p (pre x) block post) ->
  hoare_block p (assr_exists pre) block post.
Proof.
  sfirstorder.
Qed.

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

Lemma hoare_expr_det'_intro : forall (p : path) (pre : assertion) (expr : Expression) (sv : Sval),
  hoare_expr p pre expr sv ->
  hoare_expr_det' p pre expr sv.
Proof.
  unfold hoare_expr, hoare_expr_det'. intros.
  inv H2.
  eapply exec_val_trans.
  2 : {
    eapply H0; eauto.
  }
  2 : eassumption.
  red; clear; sauto lq: on.
Qed.

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
  specialize_hoare_call.
  destruct sig'; only 1, 3, 4 : solve[inv H2].
  destruct H2. destruct H16 as [? [? ?]].
  split; only 1 : destruct H6; auto.
  inv H5. destruct H6.
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

Lemma hoare_stmt_var_none : forall p pre tags typ' name loc typ post rtyp sv,
  get_real_type ge typ' = Some rtyp ->
  uninit_sval_of_typ (Some false) rtyp = Some sv ->
  hoare_write pre (ValLeftName loc) sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatVariable typ' name None loc) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H4.
  assert (sv0 = sv) by congruence; subst.
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

Lemma hoare_stmt_empty : forall p pre post tags typ,
  implies pre (post_continue post) ->
  hoare_stmt p pre (MkStatement tags StatEmpty typ) post.
Proof.
  unfold hoare_stmt; intros.
  inv H2; auto.
Qed.

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

Definition arg_refine (arg arg' : argument) :=
  match arg, arg' with
  | (osv, olv), (osv', olv') =>
      EquivUtil.relop sval_refine osv osv' /\ EquivUtil.relop eq olv olv'
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

Ltac specialize_hoare_args :=
  lazymatch goal with
  | H : hoare_args _ _ _ _ _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  | H : forall _ _ _, _ -> exec_args _ _ _ _ _ _ _ _ -> _ |- _ =>
      specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
  end.

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
  specialize_hoare_lexpr.
  destruct H0 as [? H0]. subst.
  specialize_hoare_args.
  destruct H1 as [? H1]. subst.
  assert (Forall2 sval_refine (extract_invals argvals) (extract_invals argvals0) /\ pre st). {
    split; auto using args_refine_extract_invals.
  }
  specialize (H2 _ _ _ _ ltac:(eassumption) H22).
  assumption.
Qed.

Lemma hoare_call_func : forall p (pre : assertion) tags func targs args typ dir post dirs argvals obj_path fd
    (mid1 : arg_assertion) mid2 mid3,
  is_builtin_func func = false ->
  forall (H_dirs : get_arg_directions func = Result.Ok dirs),
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
  rewrite H16 in H_dirs; inv H_dirs.
  specialize_hoare_args.
  destruct H1 as [? H1]. subst.
  rewrite H2 in H20; inv H20.
  unshelve epose proof (H4 _ _ _ _ _ ltac:(shelve) H24). {
    split. { apply args_refine_extract_invals. auto. }
    destruct (is_some obj_path0).
    - destruct st. split; eauto.
    - auto.
  }
  erewrite <- args_refine_map_snd in H26 by eauto.
  unshelve epose proof (H6 _ sig' _ _ ltac:(shelve) H26). {
    destruct (is_some obj_path0).
    - destruct s3. destruct sig'; try solve [inv H3].
      split.
      + destruct st; eauto.
      + eauto.
    - auto.
  }
  inv H27.
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
  specialize_hoare_block.
  destruct H1.
  - destruct H1 as [? H1]; subst.
    apply H2; auto.
  - destruct sig0; try solve [inv H1].
    apply H2; auto.
Qed.

Definition hoare_table_entries p entries entryvs : Prop :=
  forall entryvs',
    exec_table_entries (tags_t := tags_t) read_ndetbit p entries entryvs' ->
    entryvs' = entryvs.

Lemma exec_table_entries_det : forall p entries entryvs entryvs',
  exec_table_entries (tags_t := tags_t) read_ndetbit p entries entryvs ->
  exec_table_entries read_ndetbit p entries entryvs' ->
  entryvs' = entryvs.
Proof.
  intros. generalize dependent entryvs'.
  induction H0; intros.
  { inv H1; auto. }
  inv H2.
  f_equal; only 2 : eauto.
  clear -H0 H5.
  inv H0; inv H5.
  destruct (PeanoNat.Nat.eqb (length svs) 1); subst; auto.
Qed.

Lemma hoare_table_entries_intros : forall p entries entryvs,
  exec_table_entries (tags_t := tags_t) read_ndetbit p entries entryvs ->
  hoare_table_entries p entries entryvs.
Proof.
  unfold hoare_table_entries; intros.
  eapply exec_table_entries_det; eauto.
Qed.

(* For now, we only support constant entries in this rule. *)
Lemma hoare_table_match_case : forall p pre name keys keysvals keyvals const_entries entryvs matched_action,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  hoare_exprs_det p pre (map table_key_key keys) keysvals ->
  Forall2 val_to_sval keyvals keysvals ->
  hoare_table_entries p entries entryvs ->
  extern_match (combine keyvals match_kinds) entryvs = matched_action ->
  hoare_table_match p pre name keys (Some const_entries) matched_action.
Proof.
  unfold hoare_table_match; intros.
  inv H5.
  assert (
    forall keysvals',
      Forall2 val_to_sval keyvals0 keysvals' ->
      Forall2 sval_refine keysvals keysvals')
    by (intros; eapply H0; eassumption).
  assert (
    forall keysvals',
      Forall2 val_to_sval keyvals0 keysvals' ->
      Forall2 val_to_sval keyvals keysvals'). {
    intros.
    specialize (H3 _ ltac:(eassumption)).
    eapply Forall2_trans; [ | eassumption | eassumption].
    unfold rel_trans.
    eapply exec_val_trans.
    unfold rel_trans.
    (* I don't know why we need to clear here. But after changing AbsMet to be an element of
      ExternSem, sauto no longer wokrs and reports "Anomaly "Unable to handle arbitrary u+k <= v constraints."" *)
    clear; sauto.
  }
  assert (Forall2 val_to_sval keyvals0 (map eval_val_to_sval keyvals0)). {
    clear.
    induction keyvals0; constructor.
    - apply val_to_sval_iff; auto.
    - assumption.
  }
  specialize (H5 _ ltac:(eassumption)).
  assert (Forall2 (sval_to_val strict_read_ndetbit) (map eval_val_to_sval keyvals0) keyvals). {
    eapply Forall2_sym; [ | eassumption].
    eapply exec_val_sym.
    clear; sauto.
  }
  assert (Forall2 (exec_val eq) keyvals0 keyvals). {
    eapply Forall2_trans; [ | eassumption | eassumption].
    unfold rel_trans.
    eapply exec_val_trans.
    unfold rel_trans.
    clear; sauto.
  }
  assert (keyvals0 = keyvals). {
    apply ForallMap.Forall2_eq.
    eapply Forall2_impl; [exact exec_val_eq | eassumption].
  }
  subst.
  specialize (H2 _ ltac:(eassumption)).
  subst.
  reflexivity.
Qed.

(* Hoare rule for table if we know a particular case. *)
Lemma hoare_func_table_case : forall p pre name keys actions default_action const_entries post
      actionref action retv,
  hoare_table_match p pre name keys const_entries actionref ->
  get_table_call actions default_action actionref = Some (action, retv) ->
  hoare_call p pre action (fun _ st => post st) ->
  hoare_func p (fun _ => pre) (FTable name keys actions default_action const_entries)
      [] (fun args retv' st => args = [] /\ retv' = retv /\ post st).
Proof.
  unfold hoare_table_match, hoare_call, hoare_func.
  intros.
  inv H4.
  specialize (H0 _ _ H3 ltac:(eassumption)).
  subst actionref0.
  rewrite H17 in H1; inv H1.
  specialize_hoare_call.
  simpl; auto.
Qed.

(* These two predicates describe the list of cases is corresponding to the matching result. *)

Definition hoare_extern_match_list (keys_match_kinds : list (Val * ident)) (entryvs : list table_entry_valset) :=
  fix hoare_extern_match_list' (cases : list (bool * action_ref)) : Prop :=
    match cases with
    | (cond, matched_action) :: cases' =>
        if cond then
          extern_match keys_match_kinds entryvs = Some matched_action
        else
          hoare_extern_match_list' cases'
    | nil => extern_match keys_match_kinds entryvs = None
    end.

Fixpoint hoare_table_match_list (p : path) (pre : assertion) (name : ident) (keys : list TableKey)
      (const_entries : option (list table_entry)) (cases : list (bool * action_ref)) : Prop :=
  match cases with
  | (cond, matched_action) :: cases' =>
      if cond then
        hoare_table_match p pre name keys const_entries (Some matched_action)
      else
        hoare_table_match_list p pre name keys const_entries cases'
  | nil => hoare_table_match p pre name keys const_entries None
  end.

Lemma hoare_table_match_list_intro : forall p pre name keys keysvals keyvals const_entries entryvs cases,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  hoare_exprs_det p pre (map table_key_key keys) keysvals ->
  Forall2 val_to_sval keyvals keysvals ->
  hoare_table_entries p entries entryvs ->
  hoare_extern_match_list (combine keyvals match_kinds) entryvs cases ->
  hoare_table_match_list p pre name keys (Some const_entries) cases.
Proof.
  intros.
  assert (forall matched_action,
      extern_match (combine keyvals match_kinds) entryvs = matched_action ->
      hoare_table_match p pre name keys (Some const_entries) matched_action). {
    unfold hoare_table_match; intros.
    eapply hoare_table_match_case; eauto.
  }
  induction cases.
  - simpl in H3 |- *.
    auto.
  - simpl in H3 |- *.
    destruct a as [[] ?]; auto.
Qed.

Inductive hoare_table_action_case (p : path) (pre : assertion) (actions : list Expression)
      (default_action : Expression) (post : arg_ret_assertion) (matched_action : option action_ref) : Prop :=
  | hoare_table_action_case_intro : forall action retv,
      get_table_call actions default_action matched_action = Some (action, retv) ->
      hoare_call p pre action (fun _ st => post [] retv st) ->
      hoare_table_action_case p pre actions default_action post matched_action.

(* This predicate desribes that the action execution of the case list satisfies the post condition. *)

Inductive hoare_table_action_cases (p : path) (pre : assertion) (actions : list Expression)
      (default_action : Expression) (post : arg_ret_assertion) : list (bool * action_ref) -> Prop :=
  | hoare_table_action_cases_nil :
      hoare_table_action_case p pre actions default_action post None ->
      hoare_table_action_cases p pre actions default_action post nil
  | hoare_table_action_cases_cons : forall (cond : bool) matched_action cases',
      (cond -> hoare_table_action_case p pre actions default_action post (Some matched_action)) ->
      (~~cond -> hoare_table_action_cases p pre actions default_action post cases') ->
      hoare_table_action_cases p pre actions default_action post ((cond, matched_action) :: cases').

(* We say the application of a table contain to phases: table matching phase and table action phase.
  Table matching phase evaluate the keys and entries, and find the action. The table action phase
  executes the action and return table's return value. *)

Lemma hoare_func_table_action : forall p pre name keys actions default_action const_entries post matched_action,
  hoare_table_match p pre name keys const_entries matched_action ->
  hoare_table_action_case p pre actions default_action post matched_action ->
  hoare_func p (fun _ => pre) (FTable name keys actions default_action const_entries)
      [] post.
Proof.
  intros. inv H1.
  eapply hoare_func_post.
  + eapply hoare_func_table_case; eauto.
  + clear.
    unfold arg_ret_implies; intros.
    hauto lq: on.
Qed.

Lemma hoare_func_table : forall p pre name keys actions default_action const_entries post cases,
  hoare_table_match_list p pre name keys const_entries cases ->
  hoare_table_action_cases p pre actions default_action post cases ->
  hoare_func p (fun _ => pre) (FTable name keys actions default_action const_entries)
      [] post.
Proof.
  induction 2.
  - eapply hoare_func_table_action; eauto.
  - simpl in H0.
    destruct cond.
    + eapply hoare_func_table_action; eauto.
    + auto.
Qed.

Lemma hoare_func_table_action_middle : forall p (pre : assertion) st (keys : list (@TableKey tags_t)) actions default_action post matched_action entryvs keyvals
    action retv st',
  pre st ->
  extern_match (combine keyvals (map table_key_matchkind keys)) entryvs = matched_action ->
  hoare_table_action_case p pre actions default_action post matched_action ->
  get_table_call actions default_action
      (extern_match (combine keyvals (map table_key_matchkind keys)) entryvs) =
    Some (action, retv) ->
  exec_call ge read_ndetbit p st action st' SReturnNull ->
  satisfies_arg_ret_assertion post [] (SReturn retv) st'.
Proof.
  intros.
  inv H2.
  rewrite H5 in H3. inv H3.
  specialize_hoare_call.
  auto.
Qed.

Lemma hoare_func_table_middle : forall p pre name keys actions default_action const_entries post entryvs keysvals,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  hoare_exprs_det' p pre (map table_key_key keys) keysvals ->
  hoare_table_entries p entries entryvs ->
  (forall keyvals,
    Forall2 (sval_to_val read_ndetbit) keysvals keyvals ->
    exists cases,
      hoare_extern_match_list (combine keyvals match_kinds) entryvs cases
        /\ hoare_table_action_cases p pre actions default_action post cases) ->
  hoare_func p (fun _ => pre) (FTable name keys actions default_action (Some const_entries))
      [] post.
Proof.
  intros; red; intros.
  inv H4.
  inv H16.
  specialize (H0 _ _ ltac:(eassumption) ltac:(eassumption)).
  specialize (H1 _ ltac:(eassumption)); subst.
  specialize (H2 _ ltac:(eassumption)). destruct H2 as [cases []].
  (* subst match_kinds match_kinds0. *)
  induction H2.
  - eapply hoare_func_table_action_middle; eauto.
  - simpl in H1.
    destruct cond.
    + eapply hoare_func_table_action_middle; eauto.
    + auto.
Qed.

Definition hoare_extern_match_list_nondet (keys : list Sval) (match_kinds : list ident) (entryvs : list table_entry_valset)
      (cases : list (option bool * action_ref)) : Prop :=
  forall keyvals, Forall2 (sval_to_val read_ndetbit) keys keyvals ->
  (fix hoare_extern_match_list' (cases : list (option bool * action_ref)) : Prop :=
    match cases with
    | (cond, matched_action) :: cases' =>
        match cond with
        | Some cond =>
            if cond then
              extern_match (combine keyvals match_kinds) entryvs = Some matched_action
            else
              hoare_extern_match_list' cases'
        | None =>
            extern_match (combine keyvals match_kinds) entryvs = Some matched_action
              \/ hoare_extern_match_list' cases'
        end
    | nil => extern_match (combine keyvals match_kinds) entryvs = None
    end) cases.

Definition hoare_table_match_list_nondet (p : path) (pre : assertion) (name : ident) (keys : list TableKey)
      (const_entries : option (list table_entry)) (cases : list (option bool * action_ref)) : Prop :=
  forall st matched_action',
    pre st ->
    exec_table_match ge read_ndetbit p st name keys const_entries matched_action' ->
  (fix hoare_table_match_list_nondet' (cases : list (option bool * action_ref)) : Prop :=
    match cases with
    | (cond, matched_action) :: cases' =>
        match cond with
        | Some cond =>
            if cond then
              matched_action' = Some matched_action
            else
              hoare_table_match_list_nondet' cases'
        | None =>
            matched_action' = Some matched_action
              \/ hoare_table_match_list_nondet' cases'
        end
    | nil => matched_action' = None
    end) cases.

Lemma hoare_table_match_list_nondet_intro : forall p pre name keys keysvals const_entries entryvs cases,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  hoare_exprs_det' p pre (map table_key_key keys) keysvals ->
  hoare_table_entries p entries entryvs ->
  hoare_extern_match_list_nondet keysvals match_kinds entryvs cases ->
  hoare_table_match_list_nondet p pre name keys (Some const_entries) cases.
Proof.
  intros. red; intros.
  inv H4.
  specialize (H0 _ _ ltac:(eassumption) ltac:(eassumption)).
  specialize (H2 _ H0).
  specialize (H1 _ ltac:(eassumption)); subst.
  auto.
Qed.

Inductive hoare_table_action_cases_nondet (p : path) (pre : assertion) (actions : list Expression)
      (default_action : Expression) (post : arg_ret_assertion) : list (option bool * action_ref) -> Prop :=
  | hoare_table_action_cases_nondet_nil :
      hoare_table_action_case p pre actions default_action post None ->
      hoare_table_action_cases_nondet p pre actions default_action post nil
  | hoare_table_action_cases_nondet_cons_Some : forall (cond : bool) matched_action cases',
      (cond -> hoare_table_action_case p pre actions default_action post (Some matched_action)) ->
      (~~cond -> hoare_table_action_cases_nondet p pre actions default_action post cases') ->
      hoare_table_action_cases_nondet p pre actions default_action post ((Some cond, matched_action) :: cases')
  | hoare_table_action_cases_nondet_cons_None : forall (cond : bool) matched_action cases',
      hoare_table_action_case p pre actions default_action post (Some matched_action) ->
      hoare_table_action_cases_nondet p pre actions default_action post cases' ->
      hoare_table_action_cases_nondet p pre actions default_action post ((None, matched_action) :: cases').

Lemma hoare_func_table_action' : forall p (pre : assertion) name keys actions default_action const_entries post matched_action,
  forall (st : state) (st' : state) matched_action' action retv,
    pre st ->
    exec_table_match ge read_ndetbit p st name keys const_entries matched_action' ->
    get_table_call actions default_action matched_action' = Some (action, retv) ->
    exec_call ge read_ndetbit p st action st' SReturnNull ->
    matched_action' = matched_action ->
    hoare_table_action_case p pre actions default_action post matched_action ->
    satisfies_arg_ret_assertion post [] (SReturn retv) st'.
Proof.
  intros.
  inv H5.
  rewrite H6 in H2; inv H2.
  specialize_hoare_call.
  apply H7.
Qed.

Lemma hoare_func_table_nondet : forall p pre name keys actions default_action const_entries post cases,
  hoare_table_match_list_nondet p pre name keys const_entries cases ->
  hoare_table_action_cases_nondet p pre actions default_action post cases ->
  hoare_func p (fun _ => pre) (FTable name keys actions default_action const_entries)
      [] post.
Proof.
  intros. red; intros.
  inversion H3; subst.
  specialize (H0 _ _ ltac:(eassumption) ltac:(eassumption)).
  induction H1.
  - eapply hoare_func_table_action'; eauto.
  - destruct cond; simpl in H0.
    + eapply hoare_func_table_action'; eauto.
    + auto.
  - destruct H0.
    + eapply hoare_func_table_action'; eauto.
    + eapply IHhoare_table_action_cases_nondet; eauto.
Qed.

Definition hoare_abstract_method (pre : list Sval -> extern_state -> Prop)
    (func : AbsMet) (post : list Sval -> Val -> extern_state -> Prop) :=
  forall es inargs inargs' es' outargs' outargs sig,
    pre inargs es ->
    svals_to_vals read_ndetbit inargs inargs' ->
    func es inargs' es' outargs' sig ->
    vals_to_svals outargs' outargs ->
    match sig with
    | SReturn vret => post outargs vret es'
    | _ => False
    end.

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

Lemma implies_trans : forall (pre mid post : assertion),
  implies pre mid ->
  implies mid post ->
  implies pre post.
Proof.
  unfold implies; intros; sfirstorder.
Qed.

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

End Hoare.

Create HintDb hoare.
#[export] Hint Resolve hoare_expr_det_intro : hoare.
#[export] Hint Resolve is_no_dup_NoDup : hoare.
