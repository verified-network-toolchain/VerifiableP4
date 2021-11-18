Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import Poulet4.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Section Hoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t bool).
Notation Sval := (@ValueBase tags_t (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Context `{@Target tags_t Expression}.

Variable ge : (@genv tags_t _).

Definition assertion := state -> Prop. (* shallow assertion *)
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

Definition return_post_assertion_1 (a : ret_assertion) : post_assertion :=
  mk_post_assertion (a ValBaseNull) a.

Definition hoare_expr (p : path) (pre : assertion) (expr : Expression) (v : Sval) :=
  forall st v',
    pre st ->
    exec_expr ge read_ndetbit p st expr v' ->
    v' = v.

Definition hoare_expr_1 (p : path) (pre : assertion) (expr : Expression) (v : Sval) :=
  forall st,
    pre st ->
    exec_expr ge read_ndetbit p st expr v.

Definition hoare_lexpr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) :=
  forall st lv' sig,
    pre st ->
    exec_lexpr ge read_ndetbit p st expr lv' sig ->
    sig = SContinue /\ lval_equivb lv' lv.

(* Definition hoare_loc_to_val (p : path) (pre : assertion) (loc : Locator) (v : Sval) :=
    forall st,
    pre st ->
    loc_to_val p loc st = Some v. *)

Definition hoare_update_val_by_loc (p : path) (pre : assertion) (loc : Locator) (v : Sval) (post : assertion) :=
    forall st st',
    pre st ->
    update_val_by_loc p st loc v = st' ->
    post st'.

Definition hoare_read (p : path) (pre : assertion) (lv : Lval) (v : Sval) :=
  forall st v',
    pre st ->
    exec_read ge p st lv v' ->
    v' = v.

Definition hoare_write (p : path) (pre : assertion) (lv : Lval) (v : Sval) (post : assertion) :=
  forall st st',
    pre st ->
    exec_write ge p st lv v st' ->
    post st'.

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
  | y :: al => P4String.equivb x y || _in x al
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

