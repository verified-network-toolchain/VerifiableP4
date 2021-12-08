Require Import Coq.NArith.BinNat.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import Poulet4.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Section Hoare.

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

Fixpoint lval_eqb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | MkValueLvalue (ValLeftName _ loc1) _, MkValueLvalue (ValLeftName _ loc2) _ =>
      locator_eqb loc1 loc2
  | MkValueLvalue (ValLeftMember lv1 member1) _, MkValueLvalue (ValLeftMember lv2 member2) _ =>
      lval_eqb lv1 lv2 && String.eqb member1 member2
  | MkValueLvalue (ValLeftBitAccess lv1 msb1 lsb1) _, MkValueLvalue (ValLeftBitAccess lv2 msb2 lsb2) _ =>
      lval_eqb lv1 lv2 && N.eqb msb1 msb2 && N.eqb lsb1 lsb2
  | MkValueLvalue (ValLeftArrayAccess lv1 idx1) _, MkValueLvalue (ValLeftArrayAccess lv2 idx2) _ =>
      lval_eqb lv1 lv2 && N.eqb idx1 idx2
  | _, _ => false
  end.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) :=
  forall st lv' sig,
    pre st ->
    exec_lexpr ge read_ndetbit p st expr lv' sig ->
    sig = SContinue /\ lval_eqb lv' lv.

Definition hoare_loc_to_sval (p : path) (pre : assertion) (loc : Locator) (v : Sval) :=
    forall st,
    pre st ->
    loc_to_sval loc st = Some v.

Definition hoare_update_val_by_loc (p : path) (pre : assertion) (loc : Locator) (v : Sval) (post : assertion) :=
    forall st st',
    pre st ->
    update_val_by_loc st loc v = st' ->
    post st'.

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
    exec_read ge st lv sv' ->
    sval_refine sv sv'.

Definition hoare_write (pre : assertion) (lv : Lval) (sv : Sval) (post : assertion) :=
  forall st sv' st',
    pre st ->
    sval_refine sv sv' ->
    exec_write ge st lv sv' st' ->
    post st'.

Definition hoare_read_vars (pre : assertion) (ps : list path) (svs : list Sval) :=
  Forall2 (hoare_read_var pre) ps svs.

Definition hoare_write_vars (pre : assertion) (ps : list path) (svs : list Sval) (post : assertion) :=
  Forall2_fold hoare_write_var pre ps svs post.

Definition hoare_reads (pre : assertion) (lvs : list Lval) (svs : list Sval) :=
  Forall2 (hoare_read pre) lvs svs.

Definition hoare_writes (pre : assertion) (lvs : list Lval) (svs : list Sval) (post : assertion) :=
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

Lemma hoare_stmt_assign : forall p pre tags lhs rhs typ post lv sv,
  hoare_lexpr p pre lhs lv ->
  is_call_expression rhs = false ->
  hoare_expr_det p pre rhs sv ->
  hoare_write pre lv sv (post_continue post) ->
  hoare_stmt p pre (MkStatement tags (StatAssignment lhs rhs) typ) post.
Proof.
  unfold hoare_stmt. intros.
  left.
  inv H5. 2 : {
    (* rule out the call case *)
    inv H14; inv H1.
  }
  specialize (H0 _ _ _ H4 H15).
  inv H0.
  split; only 1 : split.
  apply lval_eqb_eq in H6. subst lv0.
  specialize (H2 _ _ _ H4 H12 H16).
  specialize (H3 _ _ _ H4 H2 H17).
  apply H3.
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
  hoare_lexpr p pre lhs lv ->
  is_call_expression rhs = true ->
  hoare_call p pre rhs (fun v st => mid st /\ (forall sv', val_to_sval v sv' -> sval_refine sv sv')) ->
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
  specialize (H0 _ _ _ H4 H15).
  inv H0.
  apply lval_eqb_eq in H6. subst lv0.
  specialize (H2 _ _ _ H4 H14).
  destruct sig'; only 1, 3, 4 : solve[inv H2].
  destruct H2. destruct H16 as [? []].
  split; only 1 : auto.
  inv H5.
  specialize (H3 _ _ _ H0 (H2 _ H9) H6).
  apply H3.
Qed.

Lemma hoare_stmt_if_true : forall p pre tags cond tru ofls typ post,
  hoare_expr_det p pre cond (ValBaseBool (Some true)) ->
  hoare_stmt p pre tru post ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
Admitted.

Lemma hoare_stmt_if_false : forall p pre tags cond tru ofls typ post,
  hoare_expr_det p pre cond (ValBaseBool (Some false)) ->
  hoare_stmt p pre (force empty_statement ofls) post ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
Admitted.

Lemma hoare_stmt_if : forall p pre tags cond tru ofls typ post b,
  hoare_expr_det p pre cond (ValBaseBool (Some b)) ->
  (if b then
      hoare_stmt p pre tru post
   else
      hoare_stmt p pre (force empty_statement ofls) post
  ) ->
  hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  intros. destruct b.
  - apply hoare_stmt_if_true; auto.
  - apply hoare_stmt_if_false; auto.
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
  (forall st, pre st -> (post_return post) ValBaseNull st) ->
  hoare_stmt p pre (MkStatement tags (StatReturn None) typ) post.
Proof.
  unfold hoare_stmt; intros.
  inv H2; right; apply H0; eauto.
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

Definition hoare_loc_to_sval_list (p : path) (pre : assertion) (locs : list Locator) (svs : list Sval) : Prop :=
  Forall2 (hoare_loc_to_sval p pre) locs svs.

Inductive hoare_update_val_by_loc_list : path -> assertion -> (list Locator) -> (list Sval) -> assertion -> Prop :=
  | hoare_update_val_by_loc_nil : forall p pre,
      hoare_update_val_by_loc_list p pre nil nil pre
  | hoare_update_val_by_loc_cons : forall p pre loc locs v vs mid post,
      hoare_update_val_by_loc p pre loc v mid ->
      hoare_update_val_by_loc_list p mid locs vs post ->
      hoare_update_val_by_loc_list p pre (loc :: locs) (v :: vs) post.

Definition hoare_func_copy_in (pre : arg_assertion) (params : list (path * direction)) (post : assertion) : Prop :=
  forall args st st',
    pre args st ->
    bind_parameters params args st st' ->
    post st'.

Definition generate_post_condition (out_params : list path) (post : arg_ret_assertion) : ret_assertion :=
  fun retv st =>
    forall args,
      extract_parameters out_params st = Some args ->
      post args retv st.

Lemma hoare_func_internal : forall p pre params init body targs mid1 mid2 post,
  hoare_func_copy_in pre params mid1 ->
  hoare_block p mid1 init (continue_post_assertion mid2) ->
  hoare_block p mid2 body (return_post_assertion_1 (generate_post_condition (filter_out params) post)) ->
  hoare_func p pre (FInternal params init body) targs post.
Proof.
  unfold hoare_func_copy_in, hoare_block, hoare_func.
  intros.
  inv H4.
  specialize (H0 _ _ _ H3 H8).
  specialize (H1 _ _ _ H0 H9).
  destruct sig0; inv H10.
  destruct H1. 2 : { inv H1. }
  destruct H1 as [_ H1].

  specialize (H2 _ _ _ H1 H13).
  destruct H2.
  - destruct H2 as [? H2]; subst sig'.
    apply H2; auto.
  - destruct sig'; try solve [inv H2].
    apply H2; auto.
Qed.

Section DeepEmbeddedHoare.

Lemma implies_refl : forall (pre : assertion),
  implies pre pre.
Proof.
  clear ge. admit.
Admitted.

Lemma implies_trans : forall (pre mid post : assertion),
  implies pre mid ->
  implies mid post ->
  implies pre post.
Proof.
  clear ge. admit.
Admitted.

Fixpoint _in (x : ident) (al : list ident) : bool :=
  match al with
  | y :: al => String.eqb x y || _in x al
  | [] => false
  end.

Fixpoint no_dup (al : list ident) : bool :=
  match al with
  | x :: al => ~~(_in x al) && no_dup al
  | [] => true
  end.

(* Inductive deep_hoare_loc_to_val : path -> assertion -> Locator -> Val -> Prop :=
  | deep_hoare_loc_to_val_intro : forall p pre loc v,
      hoare_loc_to_val p pre loc v ->
      deep_hoare_loc_to_val p pre loc v.

Inductive deep_hoare_loc_to_val_list : path -> assertion -> (list Locator) -> (list Val) -> Prop :=
  | deep_hoare_loc_to_val_nil : forall p pre,
      deep_hoare_loc_to_val_list p pre nil nil
  | deep_hoare_loc_to_val_cons : forall p pre loc locs v vs,
      deep_hoare_loc_to_val p pre loc v ->
      deep_hoare_loc_to_val_list p pre locs vs ->
      deep_hoare_loc_to_val_list p pre (loc :: locs) (v :: vs).

Inductive deep_hoare_update_val_by_loc : path -> assertion -> Locator -> Val -> assertion -> Prop :=
  | deep_hoare_update_val_by_loc_intro : forall p pre loc v post,
      hoare_update_val_by_loc p pre loc v post ->
      deep_hoare_update_val_by_loc p pre loc v post.

Inductive deep_hoare_update_val_by_loc_list : path -> assertion -> (list Locator) -> (list Val) -> assertion -> Prop :=
  | deep_hoare_update_val_by_loc_nil : forall p pre,
      deep_hoare_update_val_by_loc_list p pre nil nil pre
  | deep_hoare_update_val_by_loc_cons : forall p pre loc locs v vs mid post,
      deep_hoare_update_val_by_loc p pre loc v mid ->
      deep_hoare_update_val_by_loc_list p mid locs vs post ->
      deep_hoare_update_val_by_loc_list p pre (loc :: locs) (v :: vs) post.

Definition generate_post_condition (p : path) (locs : list Locator) (post : arg_ret_assertion) : ret_assertion :=
  fun vret st =>
    let step ov ovs :=
      match ov, ovs with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end in
    match fold_right step (Some nil) (map (fun loc => loc_to_val p loc st) locs) with
    | Some outargs => post outargs vret st
    | None => True
    end.

(* Definition deep_hoare_expr (p : path) (pre : assertion) (expr : Expression) (v : Val) : Prop :=
  forall st,
    pre st ->
    exec_expr ge p st expr v.

Definition deep_hoare_lexpr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) : Prop :=
  forall st,
    pre st ->
    exec_lexpr ge p st expr lv SContinue. *)

Definition ret_assertion_to_assertion (a : ret_assertion) : assertion :=
  fun st => exists vret, a vret st.

Inductive deep_hoare_stmt : path -> assertion -> Statement -> post_assertion -> Prop :=
  | deep_hoare_stmt_fallback : forall p pre stmt post,
      hoare_stmt p pre stmt post ->
      deep_hoare_stmt p pre stmt post

  | deep_hoare_stmt_block : forall p pre tags block typ post,
      deep_hoare_block p pre block post ->
      deep_hoare_stmt p pre (MkStatement tags (StatBlock block) typ) post

  | deep_hoare_stmt_if_true : forall p pre tags cond tru ofls typ post,
      hoare_expr p pre cond (ValBaseBool true) ->
      deep_hoare_stmt p pre tru post ->
      deep_hoare_stmt p pre (MkStatement tags (StatConditional cond tru ofls) typ) post

  | deep_hoare_stmt_method_call : forall p pre tags func args typ mid (post : post_assertion),
      hoare_call p pre (MkExpression default (ExpFunctionCall func nil args) TypVoid Directionless) mid ->
      ret_assertion_to_assertion mid = post ->
      deep_hoare_stmt p pre (MkStatement tags (StatMethodCall func nil args) typ) post

with deep_hoare_block : path -> assertion -> Block -> post_assertion -> Prop :=
  | deep_hoare_block_nil : forall p pre post tags,
      implies pre (post_continue post) ->
      deep_hoare_block p pre (BlockEmpty tags) post

  | deep_hoare_block_cons : forall p pre stmt mid block post,
      deep_hoare_stmt p pre stmt mid ->
      deep_hoare_block p mid block post ->
      deep_hoare_block p pre (BlockCons stmt block) post.

Inductive deep_hoare_copy_in : path -> arg_assertion -> list Locator -> assertion -> Prop := 
  | deep_hoare_copy_in_intro : forall p pre params post,
      (forall inargs, deep_hoare_update_val_by_loc_list p (pre inargs) params inargs post) ->
      deep_hoare_copy_in p pre params post.

Inductive deep_hoare_func : path -> arg_assertion -> @fundef tags_t -> list (@P4Type tags_t) -> arg_ret_assertion -> Prop :=
  | deep_hoare_func_internal : forall p pre params init body targs mid1 mid2 post,
      deep_hoare_copy_in p pre (filter_in params) mid1 ->
      deep_hoare_block p mid1 init (continue_post_assertion mid2) ->
      deep_hoare_block p mid2 body (return_post_assertion_1 (generate_post_condition p (filter_out params) post)) ->
      deep_hoare_func p pre (FInternal params init body) targs post.

Inductive deep_hoare_arg : path -> assertion -> option Expression -> direction -> argument -> Prop :=
  | deep_hoare_arg_in : forall p pre expr val,
      hoare_expr p pre expr val ->
      deep_hoare_arg p pre (Some expr) Typed.In (Some val, None)
  | deep_hoare_arg_out_dontcare : forall p pre,
      deep_hoare_arg p pre None Out (None, None)
  | deep_hoare_arg_out : forall p pre expr lval,
      hoare_lexpr p pre expr lval ->
      deep_hoare_arg p pre (Some expr) Out (None, Some lval)
  | exec_arg_inout : forall p pre expr lval val,
      hoare_lexpr p pre expr lval ->
      hoare_read p pre lval val ->
      deep_hoare_arg p pre (Some expr) InOut (Some val, Some lval).

Inductive deep_hoare_args : path -> assertion -> list (option Expression) -> list direction -> list argument -> Prop :=
  | deep_hoare_args_nil: forall p pre,
      deep_hoare_args p pre nil nil nil
  | deep_hoare_args_cons : forall p pre exp exps dir dirs arg args,
      deep_hoare_arg p pre exp dir arg ->
      deep_hoare_args p pre exps dirs args ->
      deep_hoare_args p pre (exp :: exps) (dir :: dirs) (arg :: args).

Inductive deep_hoare_write_option : path -> assertion -> option Lval -> Val -> assertion -> Prop :=
  | deep_hoare_write_option_some : forall p pre lval val post,
      hoare_write p pre lval val post ->
      deep_hoare_write_option p pre (Some lval) val post
  | deep_hoare_write_option_none : forall p pre val,
      deep_hoare_write_option p pre None val pre.

Inductive deep_hoare_write_options : path -> assertion -> list (option Lval) -> list Val -> assertion -> Prop :=
  | deep_hoare_write_options_nil : forall p pre post,
      implies pre post ->
      deep_hoare_write_options p pre nil nil post
  | exec_write_option_none : forall p pre mid post lv lvs val vals,
      deep_hoare_write_option p pre lv val mid ->
      deep_hoare_write_options p mid lvs vals post ->
      deep_hoare_write_options p pre (lv :: lvs) (val :: vals) post.

Inductive deep_hoare_outargs : path -> assertion -> list direction -> list (option Expression) -> list (option Lval) -> Prop :=
  | deep_hoare_outargs_intro : forall p (pre : assertion) dirs args lvs,
      (forall st argvals sig,
          pre st -> exec_args ge p st args dirs argvals sig ->
          extract_outlvals dirs argvals = lvs /\ sig = SContinue) ->
      deep_hoare_outargs p pre dirs args lvs.

Inductive deep_hoare_inargs : path -> assertion -> list direction -> list (option Expression) -> arg_assertion -> Prop :=
  | deep_hoare_inargs_intro : forall p (pre : assertion) dirs args,
      let post inargs st :=
        pre st /\ exists argvals, exec_args ge p st args dirs argvals SContinue /\ extract_invals argvals = inargs in
      deep_hoare_inargs p pre dirs args post.

Inductive deep_hoare_write_copy_out : path -> arg_ret_assertion -> list (option Lval) -> ret_assertion -> Prop :=
  | deep_hoare_write_copy_out_intro : forall p (pre : arg_ret_assertion) outlvs post,
      (forall outargs vret, deep_hoare_write_options p (pre outargs vret) outlvs outargs (post vret)) ->
      deep_hoare_write_copy_out p pre outlvs post.

Inductive deep_hoare_call : path -> assertion -> Expression -> ret_assertion -> Prop :=
  | deep_hoare_call_func : forall p (pre : assertion) tags func targs args typ dir outlvs obj_path fd
          (mid1 : arg_assertion) (mid2 : arg_ret_assertion) (post : ret_assertion),
      let dirs := get_arg_directions func in
      deep_hoare_outargs p pre dirs args outlvs ->
      deep_hoare_inargs p pre dirs args mid1 ->
      lookup_func ge p inst_m func = Some (obj_path, fd) ->
      deep_hoare_func obj_path mid1 fd targs mid2 ->
      deep_hoare_write_copy_out p mid2 outlvs post ->
      deep_hoare_call p pre (MkExpression tags (ExpFunctionCall func targs args) typ dir) post. *)

End DeepEmbeddedHoare.

End Hoare.

