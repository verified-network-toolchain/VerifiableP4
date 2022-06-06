Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.Utils.Utils.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.EvalExpr.
Require Import ProD3.core.EvalBuiltin.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.
Require Import Coq.ZArith.BinInt.

Section ConcreteHoare.

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

Lemma hoare_stmt_assign' : forall p pre_mem pre_ext tags lhs rhs typ post_mem ret_post lv sv,
  is_call_expression rhs = false ->
  is_no_dup (map fst pre_mem) ->
  eval_lexpr ge p pre_mem lhs = Some lv ->
  eval_expr ge p pre_mem rhs = Some sv ->
  eval_write pre_mem lv sv = Some post_mem ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatAssignment lhs rhs) typ)
      (mk_post_assertion (MEM post_mem (EXT pre_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_assign; eauto with hoare.
Qed.

Lemma hoare_stmt_assign_call' : forall p pre_mem pre_ext tags lhs rhs typ lv vret mid_mem post_mem post_ext ret_post,
  is_call_expression rhs = true ->
  eval_lexpr ge p pre_mem lhs = Some lv ->
  hoare_call ge p (MEM pre_mem (EXT pre_ext)) rhs (RET vret (MEM mid_mem (EXT post_ext))) ->
  is_no_dup (map fst mid_mem) ->
  eval_write mid_mem lv vret = Some post_mem ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatAssignment lhs rhs) typ)
      (mk_post_assertion (MEM post_mem (EXT post_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_assign_call; eauto with hoare.
Qed.

Lemma hoare_stmt_method_call' : forall p pre_mem pre_ext tags func targs args typ vret post_mem post_ext ret_post,
  hoare_call ge p
    (MEM pre_mem (EXT pre_ext))
    (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless)
    (RET vret (MEM post_mem (EXT post_ext))) ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatMethodCall func targs args) typ)
    (mk_post_assertion (MEM post_mem (EXT post_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_method_call; eauto with hoare.
Qed.

Inductive hoare_stmt_method_call_ex_layer : Hoare.ret_assertion -> Hoare.assertion -> Prop :=
  | hoare_stmt_method_call_ex_layer_base : forall vret post_mem post_ext,
      hoare_stmt_method_call_ex_layer
        (RET vret (MEM post_mem (EXT post_ext)))
        (MEM post_mem (EXT post_ext))
  | hoare_stmt_method_call_ex_layer_ex : forall [A] (P : A -> Hoare.ret_assertion) Q,
      (forall (x : A), hoare_stmt_method_call_ex_layer (P x) (Q x)) ->
      hoare_stmt_method_call_ex_layer (ret_exists P) (assr_exists Q).

Lemma hoare_stmt_method_call'_ex : forall p pre_mem pre_ext tags func targs args typ post' post ret_post,
  hoare_call ge p
    (MEM pre_mem (EXT pre_ext))
    (MkExpression dummy_tags (ExpFunctionCall func targs args) TypVoid Directionless)
    post' ->
  hoare_stmt_method_call_ex_layer post' post ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatMethodCall func targs args) typ)
    (mk_post_assertion post ret_post).
Proof.
  unfold hoare_stmt. intros.
  inv H3.
  specialize (H0 _ _ _ H2 H13).
  clear -H0 H1.
  left.
  induction H1.
  - destruct sig0; inv H0.
    auto.
  - destruct sig0; inv H0.
    specialize (H2 _ ltac:(eauto)).
    split; auto.
    eexists; apply H2.
Qed.

Lemma hoare_stmt_var' : forall p pre_mem pre_ext tags typ' name expr loc typ post_mem ret_post sv,
  is_call_expression expr = false ->
  is_no_dup (map fst pre_mem) ->
  eval_expr ge p pre_mem expr = Some sv ->
  eval_write pre_mem (ValLeftName loc) sv = Some post_mem ->
  hoare_stmt ge p
    (MEM pre_mem (EXT pre_ext))
    (MkStatement tags (StatVariable typ' name (Some expr) loc) typ)
    (mk_post_assertion (MEM post_mem (EXT pre_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_var; eauto with hoare.
Qed.

Lemma hoare_stmt_var_none' : forall p pre_mem pre_ext tags typ' name loc typ post_mem ret_post rtyp sv,
  is_no_dup (map fst pre_mem) ->
  get_real_type ge typ' = Some rtyp ->
  uninit_sval_of_typ (Some false) rtyp = Some sv ->
  eval_write pre_mem (ValLeftName loc) sv = Some post_mem ->
  hoare_stmt ge p
    (MEM pre_mem (EXT pre_ext))
    (MkStatement tags (StatVariable typ' name None loc) typ)
    (mk_post_assertion (MEM post_mem (EXT pre_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_var_none; eauto with hoare.
Qed.

Lemma hoare_stmt_var_call' : forall p pre_mem pre_ext tags typ' name expr loc typ vret mid_mem post_mem post_ext ret_post,
  is_call_expression expr = true ->
  hoare_call ge p (MEM pre_mem (EXT pre_ext)) expr (RET vret (MEM mid_mem (EXT post_ext))) ->
  is_no_dup (map fst mid_mem) ->
  eval_write mid_mem (ValLeftName loc) vret = Some post_mem ->
  hoare_stmt ge p
    (MEM pre_mem (EXT pre_ext))
    (MkStatement tags (StatVariable typ' name (Some expr) loc) typ)
    (mk_post_assertion (MEM post_mem (EXT post_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_var_call; eauto with hoare.
Qed.

Lemma hoare_stmt_direct_application' : forall p pre_mem pre_ext tags typ' func_typ args typ vret post_mem post_ext ret_post,
  hoare_call ge p
    (MEM pre_mem (EXT pre_ext))
    (MkExpression dummy_tags (ExpFunctionCall
          (direct_application_expression typ' func_typ)
          nil args) TypVoid Directionless)
    (RET vret (MEM post_mem (EXT post_ext))) ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatDirectApplication typ' func_typ args) typ)
    (mk_post_assertion (MEM post_mem (EXT post_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_direct_application; eauto with hoare.
Qed.

Lemma hoare_stmt_if_true' : forall p pre_mem pre_ext tags cond tru ofls typ post,
  eval_expr ge p pre_mem cond = Some (ValBaseBool (Some true)) ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) tru post ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  intros.
  eapply hoare_stmt_if_true; eauto with hoare.
Qed.

Lemma hoare_stmt_if_false' : forall p pre_mem pre_ext tags cond tru ofls typ post,
  eval_expr ge p pre_mem cond = Some (ValBaseBool (Some false)) ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (force empty_statement ofls) post ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  intros.
  eapply hoare_stmt_if_false; eauto with hoare.
Qed.

Lemma hoare_stmt_if' : forall p pre_mem pre_ext tags cond tru ofls typ post sv,
  eval_expr ge p pre_mem cond = Some sv ->
  (is_sval_true sv -> hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) tru post) ->
  (is_sval_false sv  -> hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (force empty_statement ofls) post) ->
  hoare_stmt ge p (MEM pre_mem (EXT pre_ext)) (MkStatement tags (StatConditional cond tru ofls) typ) post.
Proof.
  intros.
  eapply hoare_stmt_if; eauto with hoare.
Qed.

Lemma hoare_call_builtin' : forall p pre_mem pre_ext tags tags' dir' expr fname tparams params typ
    args typ' dir post_mem retv lv argvals,
  is_no_dup (map fst pre_mem) ->
  let dirs := map get_param_dir params in
  eval_lexpr ge p pre_mem expr = Some lv ->
  eval_args ge p pre_mem args dirs = Some argvals ->
  eval_builtin pre_mem lv (P4String.str fname) (extract_invals argvals) = Some (post_mem, retv) ->
  hoare_call ge p (MEM pre_mem (EXT pre_ext))
    (MkExpression tags (ExpFunctionCall
      (MkExpression tags' (ExpExpressionMember expr fname) (TypFunction (MkFunctionType tparams params FunBuiltin typ')) dir')
      nil args) typ dir)
    (RET retv (MEM post_mem (EXT pre_ext))).
Proof.
  intros.
  eapply hoare_call_builtin; eauto with hoare.
Qed.

(* Start function lemmas *)

Definition eval_write_option (a : mem_assertion) (lv : option Lval) (sv : Sval) : option mem_assertion :=
  match lv with
  | Some lv => eval_write a lv sv
  | None => Some a
  end.

Lemma eval_write_option_NoDup : forall (a : mem_assertion) (lv : option Lval) sv a',
  NoDup (map fst a) ->
  eval_write_option a lv sv = Some a' ->
  NoDup (map fst a').
Proof.
  intros. destruct lv.
  - eapply eval_write_preserve_NoDup; eauto.
  - inv H1; eauto.
Qed.

Lemma eval_write_option_sound : forall a_mem a_ext (lv : option Lval) sv a_mem',
  NoDup (map fst a_mem) ->
  eval_write_option a_mem lv sv = Some a_mem' ->
  hoare_write_option (MEM a_mem (EXT a_ext)) lv sv (MEM a_mem' (EXT a_ext)).
Proof.
  unfold hoare_write_option; intros.
  inv H4.
  - eapply eval_write_sound; eauto.
  - inv H1; eauto.
Qed.

Definition eval_write_options (a : mem_assertion) (lvs : list (option Lval)) (svs : list Sval) : option mem_assertion :=
  fold_left
    (fun a '(lv, sv) =>
      match a with
      | Some a => eval_write_option a lv sv
      | None => None
      end)
    (combine lvs svs) (Some a).

Lemma eval_write_options_inv : forall a lv lvs sv svs a',
  eval_write_options a (lv :: lvs) (sv :: svs) = Some a' ->
  exists a'',
    eval_write_option a lv sv = Some a'' /\ eval_write_options a'' lvs svs = Some a'.
Proof.
  intros.
  unfold eval_write_options in H0. simpl in H0.
  destruct (eval_write_option a lv sv).
  - eexists; eauto.
  - assert (fold_left
       (fun (a : option mem_assertion) '(lv, sv) =>
        match a with
        | Some a0 => eval_write_option a0 lv sv
        | None => None
        end) (combine lvs svs) None = None). {
      clear H0. generalize dependent svs. clear.
      induction lvs; intros.
      - auto.
      - destruct svs; auto.
        apply IHlvs.
    }
    hauto.
Qed.

Lemma eval_write_options_sound : forall a_mem a_ext lvs svs a_mem',
  NoDup (map fst a_mem) ->
  eval_write_options a_mem lvs svs = Some a_mem' ->
  hoare_write_options (MEM a_mem (EXT a_ext)) lvs svs (MEM a_mem' (EXT a_ext)).
Proof.
  intros a_mem a_ext lvs; revert a_mem a_ext; induction lvs; intros.
  - inv H1.
    unfold hoare_write_options; intros.
    inv H3; auto.
  - unfold hoare_write_options; intros.
    inv H4; inv H3.
    apply eval_write_options_inv in H1.
    destruct H1 as [a_mem'' []].
    epose proof (eval_write_option_sound _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
    eapply IHlvs.
    + eapply eval_write_option_NoDup; eauto.
    + eauto.
    + eapply H4; eauto.
    + eauto.
    + eauto.
Qed.

Definition eval_call_copy_out (a : mem_assertion) (args : list (option Lval * direction)) (outvals : list Sval) :=
  eval_write_options a (filter_out args) outvals.

Lemma eval_call_copy_out_sound : forall outvals vret a_mem a_ext args a_mem',
  NoDup (map fst a_mem) ->
  eval_call_copy_out a_mem args outvals = Some a_mem' ->
  hoare_call_copy_out (ARG_RET outvals vret (MEM a_mem (EXT a_ext))) args (RET vret (MEM a_mem' (EXT a_ext))).
Proof.
  unfold hoare_call_copy_out; intros.
  destruct sig; only 1, 3, 4 : solve [inv H2].
  destruct H2 as [? []].
  split; eauto.
  eapply eval_write_options_sound; eauto.
Qed.

(* This is quite dirty, maybe some improvement. *)
Lemma hoare_call_func' : forall p pre_mem pre_ext tags func targs args typ dir argvals obj_path fd
    outargs vret mid_mem post_mem post_ext,
  is_builtin_func func = false ->
  let dirs := get_arg_directions func in
  eval_args ge p pre_mem args dirs = Some argvals ->
  lookup_func ge p func = Some (obj_path, fd) ->
  hoare_func ge (force p obj_path)
      (ARG (extract_invals argvals) (MEM (if is_some obj_path then [] else pre_mem) (EXT pre_ext)))
      fd targs
      (ARG_RET outargs vret (MEM mid_mem (EXT post_ext))) ->
  is_no_dup (map fst (if is_some obj_path then pre_mem else mid_mem)) ->
  eval_call_copy_out (if is_some obj_path then pre_mem else mid_mem) (combine (map snd argvals) dirs) outargs = Some post_mem ->
  hoare_call ge p
    (MEM pre_mem (EXT pre_ext))
    (MkExpression tags (ExpFunctionCall func targs args) typ dir)
    (RET vret (MEM post_mem (EXT post_ext))).
Proof.
  intros.
  eapply hoare_call_func.
  - assumption.
  - eapply eval_args_sound. eassumption.
  - eassumption.
  - reflexivity.
  - eapply hoare_func_pre. 2 : eassumption.
    clear; unfold arg_implies; intros.
    destruct (is_some obj_path).
    + destruct st. destruct H0 as [? [? [? []]]].
      split. { auto. }
      split. { subst. constructor. }
      auto.
    + destruct H0; split; assumption.
  - reflexivity.
  - eapply hoare_call_copy_out_pre. 2 : { eapply eval_call_copy_out_sound; eauto with hoare. }
    clear; unfold arg_ret_implies; intros.
    destruct (is_some obj_path).
    + destruct st. destruct H0 as [[? []] [? [? [? []]]]].
      repeat split; auto.
    + auto.
Qed.

Inductive hoare_call_func_ex_layer (obj_path : option path) pre_mem out_argvals : arg_ret_assertion -> Hoare.ret_assertion -> Prop :=
  | hoare_call_func_ex_layer_base : forall outargs vret mid_mem post_ext post_mem,
      is_no_dup (map fst (if is_some obj_path then pre_mem else mid_mem)) ->
      eval_call_copy_out (if is_some obj_path then pre_mem else mid_mem) out_argvals outargs = Some post_mem ->
      hoare_call_func_ex_layer obj_path pre_mem out_argvals
        (ARG_RET outargs vret (MEM mid_mem (EXT post_ext)))
        (RET vret (MEM post_mem (EXT post_ext)))
  | hoare_call_func_ex_layer_ex : forall [A] (P : A -> arg_ret_assertion) Q,
      (forall (x : A), hoare_call_func_ex_layer obj_path pre_mem out_argvals (P x) (Q x)) ->
      hoare_call_func_ex_layer obj_path pre_mem out_argvals
        (arg_ret_exists P) (ret_exists Q).

Lemma hoare_call_func'_ex : forall p pre_mem pre_ext tags func targs args typ dir argvals obj_path fd
    mid post,
  is_builtin_func func = false ->
  let dirs := get_arg_directions func in
  eval_args ge p pre_mem args dirs = Some argvals ->
  lookup_func ge p func = Some (obj_path, fd) ->
  hoare_func ge (force p obj_path)
      (ARG (extract_invals argvals) (MEM (if is_some obj_path then [] else pre_mem) (EXT pre_ext)))
      fd targs
      mid ->
  hoare_call_func_ex_layer obj_path pre_mem (combine (map snd argvals) dirs) mid post ->
  hoare_call ge p
    (MEM pre_mem (EXT pre_ext))
    (MkExpression tags (ExpFunctionCall func targs args) typ dir)
    post.
Proof.
  intros.
  eapply hoare_call_func.
  - assumption.
  - eapply eval_args_sound. eassumption.
  - eassumption.
  - reflexivity.
  - eapply hoare_func_pre. 2 : eassumption.
    clear; unfold arg_implies; intros.
    destruct (is_some obj_path).
    + destruct st. destruct H0 as [? [? [? []]]].
      split. { auto. }
      split. { subst. constructor. }
      auto.
    + destruct H0; split; assumption.
  - reflexivity.
  - clear -H4.
    induction H4.
    + eapply hoare_call_copy_out_pre. 2 : { eapply eval_call_copy_out_sound; eauto with hoare. }
      clear; unfold arg_ret_implies; intros.
      destruct (is_some obj_path).
      * destruct st. destruct H0 as [[? []] [? [? [? []]]]].
        repeat split; auto.
      * auto.
    + clear H0; unfold hoare_call_copy_out; intros.
      destruct (is_some obj_path).
      * destruct st; destruct sig; destruct H0.
        destruct H0; destruct H3 as [? []].
        unshelve (epose proof (H1 _ _ (SReturn v) _ _ _ H2));
          shelve_unifiable.
        { split; eauto. }
        { econstructor. eapply H4. }
      * destruct sig; inv H0.
        specialize (H1 _ _ (SReturn v) _ _ ltac:(eauto) H2).
        econstructor. eapply H1.
Qed.

Inductive inv_func_copy_out (out_params : list path) : Hoare.ret_assertion -> Hoare.arg_ret_assertion -> Prop :=
  | inv_func_copy_out_base : forall a_arg a_ret a_mem a_ext,
      length out_params = length a_arg ->
      is_no_dup (out_params ++ (map fst a_mem)) ->
      inv_func_copy_out out_params
        (RET a_ret (MEM (eval_write_vars a_mem out_params a_arg) (EXT a_ext)))
        (ARG_RET a_arg a_ret (MEM a_mem (EXT a_ext)))
  | inv_func_copy_out_ex : forall {A} (P : A -> Hoare.ret_assertion) Q,
      (forall (x : A), inv_func_copy_out out_params (P x) (Q x)) ->
      inv_func_copy_out out_params (ret_exists P) (arg_ret_exists Q).

Lemma AList_get_set_some_neq : forall (a_mem : mem_assertion) (p p' : path) sv,
  p <> p' ->
  AList.get (AList.set_some a_mem p' sv) p = AList.get a_mem p.
Proof.
  intros. apply AList.set_some_get_miss. intro. red in H1. apply H0. now subst.
Qed.

Lemma eval_read_var_eval_write_vars_disjoint : forall p ps vs a_mem,
  ~In p ps ->
  eval_read_var (eval_write_vars a_mem ps vs) p = eval_read_var a_mem p.
Proof.
  induction ps; intros.
  - auto.
  - destruct vs. { auto. }
    change (eval_write_vars a_mem (a :: ps) (v :: vs)) with
      (eval_write_vars (eval_write_var a_mem a v) ps vs).
    rewrite IHps. 2 : { intro. apply H0. right. auto. }
    apply AList_get_set_some_neq.
    intro. subst. apply H0. left. auto.
Qed.

Lemma eval_write_vars_cons : forall p ps v vs a_mem,
  eval_write_vars a_mem (p :: ps) (v :: vs) = eval_write_vars (eval_write_var a_mem p v) ps vs.
Proof.
  reflexivity.
Qed.

Lemma eval_read_var_eval_write_var : forall a_mem p v,
  eval_read_var (eval_write_var a_mem p v) p = Some v.
Proof.
  intros. eapply AList.set_some_get.
Qed.

Lemma eval_read_vars_eval_write_vars : forall out_params a_arg a_mem,
  length out_params = length a_arg ->
  NoDup out_params ->
  eval_read_vars (eval_write_vars a_mem out_params a_arg) out_params = map Some a_arg.
Proof.
  induction out_params; intros.
  - destruct a_arg; only 2 : inv H0.
    auto.
  - destruct a_arg; only 1 : inv H0.
    simpl. f_equal.
    + rewrite eval_write_vars_cons.
      rewrite eval_read_var_eval_write_vars_disjoint.
      * apply eval_read_var_eval_write_var.
      * inv H1. auto.
    + change (eval_write_vars a_mem (a :: out_params) (v :: a_arg)) with
        (eval_write_vars (eval_write_var a_mem a v) out_params a_arg).
      apply IHout_params.
      * auto.
      * inv H1. auto.
Qed.

Lemma eval_write_var_disjoint : forall a_mem p sv,
  ~In p (map fst a_mem) ->
  eval_write_var a_mem p sv = a_mem ++ [(p, sv)].
Proof.
  induction a_mem; intros.
  - auto.
  - simpl. destruct a as [p' sv'].
    destruct (EquivDec.list_eqdec EquivUtil.StringEqDec p p') as [H_eqb | H_eqb].
    + cbv in H_eqb. subst. exfalso. apply H0. constructor. auto.
    + rewrite IHa_mem; auto.
      intro. apply H0. right. apply H1.
Qed.

Lemma eval_write_vars_disjoint' : forall a_mem pvs,
  NoDup (map fst pvs ++ map fst a_mem) ->
  fold_left (fun a '(p, sv) => eval_write_var a p sv) pvs a_mem = a_mem ++ pvs.
Proof.
  intros a_mem pvs; revert a_mem.
  induction pvs; intros.
  - simpl. rewrite app_nil_r. auto.
  - simpl.
    destruct a as [p sv].
    rewrite eval_write_var_disjoint. 2 : {
      inv H0.
      intro. apply H3. apply in_app_iff. auto.
    }
    rewrite IHpvs.
    + rewrite <- app_assoc. auto.
    + (* some stupid NoDup proof *)
      eapply Permutation.Permutation_NoDup. 2 : { apply H0. }
      apply Permutation.Permutation_trans with ((map fst pvs ++ [p]) ++ map fst a_mem).
      { apply Permutation.Permutation_app.
        - apply Permutation.Permutation_cons_append.
        - apply Permutation.Permutation_refl.
      }
      rewrite <- app_assoc.
      apply Permutation.Permutation_app.
      * apply Permutation.Permutation_refl.
      * rewrite map_app. apply Permutation.Permutation_cons_append.
Qed.

Lemma eval_write_vars_disjoint : forall a_mem ps svs,
  length ps = length svs ->
  NoDup (ps ++ (map fst a_mem)) ->
  eval_write_vars a_mem ps svs = a_mem ++ (combine ps svs).
Proof.
  unfold eval_write_vars.
  intros. apply eval_write_vars_disjoint'.
  rewrite ForallMap.map_fst_combine; auto.
Qed.

Lemma eval_write_vars_implies' : forall a_mem out_params a_arg,
  length out_params = length a_arg ->
  NoDup (out_params ++ (map fst a_mem)) ->
  forall m,
    mem_denote (eval_write_vars a_mem out_params a_arg) m ->
    mem_denote a_mem m.
Proof.
  intros. rewrite eval_write_vars_disjoint in H2; auto.
  clear H0 H1.
  induction a_mem; intros.
  - constructor.
  - constructor.
    + apply H2.
    + apply IHa_mem, H2.
Qed.

Lemma eval_write_vars_implies : forall a_mem out_params a_arg a_ext,
  length out_params = length a_arg ->
  NoDup (out_params ++ (map fst a_mem)) ->
  implies
    (MEM (eval_write_vars a_mem out_params a_arg) (EXT a_ext))
    (MEM a_mem (EXT a_ext)).
Proof.
  unfold implies; intros.
  destruct st; destruct H2; split.
  - eauto using eval_write_vars_implies'.
  - auto.
Qed.

Lemma NoDup_app_remove_2 : forall {A} (l l' : list A),
  NoDup (l ++ l') ->
  NoDup l.
Proof.
  intros. induction l.
  - constructor.
  - inv H0.
    constructor.
    + rewrite in_app_iff in H3. auto.
    + auto.
Qed.

Lemma inv_func_copy_out_sound_part1 : forall params a_arg a_ret a_mem a_ext,
  length (filter_out params) = length a_arg ->
  NoDup ((filter_out params) ++ (map fst a_mem)) ->
  hoare_func_copy_out
    (RET a_ret (MEM (eval_write_vars a_mem (filter_out params) a_arg) (EXT a_ext))) params
    (ARG_RET a_arg a_ret (MEM a_mem (EXT a_ext))).
Proof.
  unfold hoare_func_copy_out; intros.
  epose proof (eval_read_vars_eval_write_vars (filter_out params) _ _ H0 (NoDup_app_remove_2 _ _ H1)).
  unfold exec_func_copy_out in H3.
  apply lift_option_inv in H3.
  pose proof (eval_read_vars_sound _ _ _ _ H4 _ _ (proj2 H2) H3).
  split. { auto. }
  split. { apply H2. }
  eapply eval_write_vars_implies; eauto.
  apply H2.
Qed.

Lemma inv_func_copy_out_sound : forall params P Q,
  inv_func_copy_out (filter_out params) P Q ->
  hoare_func_copy_out P params Q.
Proof.
  intros.
  induction H0.
  - apply inv_func_copy_out_sound_part1; eauto with hoare.
  - unfold hoare_func_copy_out. intros.
    destruct H2 as [x ?].
    exists x.
    apply H1; eauto.
Qed.

(* Another method of treating implicit (return None) is generate continue_post_condition as
  hoare_stmt .. (return None) ... But here we choose a similar approach to inv_func_copy_out. *)
Inductive inv_implicit_return : Hoare.assertion -> Hoare.ret_assertion -> Prop :=
  | inv_implicit_return_base1 : forall a_mem a_ext,
      inv_implicit_return
        (MEM a_mem (EXT a_ext))
        (RET ValBaseNull (MEM a_mem (EXT a_ext)))
  | inv_implicit_return_base2 : forall a_ret a_mem a_ext,
      inv_implicit_return
        (fun st => False)
        (RET a_ret (MEM a_mem (EXT a_ext)))
  | inv_implicit_return_ex : forall {A} (P : A -> Hoare.assertion) Q,
      (forall (x : A), inv_implicit_return (P x) (Q x)) ->
      inv_implicit_return (assr_exists P) (ret_exists Q).

Lemma inv_implicit_return_sound : forall P Q,
  inv_implicit_return P Q ->
  implies P (Q ValBaseNull).
Proof.
  induction 1.
  - unfold implies; intros.
    split; auto.
    intro; intros. inv H1. apply SvalRefine.sval_refine_refl.
  - unfold implies; intros.
    inv H0.
  - unfold implies; intros.
    sfirstorder.
Qed.

Lemma hoare_func_internal' : forall p pre_arg pre_mem pre_ext params body targs mid1_mem mid2 mid2' post,
  length (filter_in params) = length pre_arg ->
  is_no_dup (map fst pre_mem) ->
  eval_write_vars pre_mem (filter_in params) pre_arg = mid1_mem ->
  hoare_block ge p (MEM mid1_mem (EXT pre_ext)) body (mk_post_assertion mid2' mid2) ->
  inv_func_copy_out (filter_out params) mid2 post ->
  inv_implicit_return mid2' mid2 ->
  hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) (FInternal params body) targs post.
Proof.
  intros.
  eapply hoare_func_internal.
  - eapply hoare_func_copy_in_intro; eauto with hoare.
  - eapply hoare_block_post. only 1 : eauto.
    split.
    + eapply inv_implicit_return_sound. eassumption.
    + sfirstorder.
  - apply inv_func_copy_out_sound; auto.
Qed.

(* For now, we only support constant entries in this rule. *)
Lemma hoare_table_match_case' : forall p pre_mem pre_ext name keys keysvals keyvals const_entries entryvs matched_action,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  eval_exprs ge p pre_mem (map table_key_key keys) = Some keysvals ->
  lift_option (map eval_sval_to_val keysvals) = Some keyvals ->
  hoare_table_entries ge p entries entryvs ->
  extern_match (combine keyvals match_kinds) entryvs = matched_action ->
  hoare_table_match ge p (MEM pre_mem (EXT pre_ext)) name keys (Some const_entries) matched_action.
Proof.
  intros.
  eapply hoare_table_match_case.
  - apply eval_exprs_sound; eauto.
  - assert (Forall2 (sval_to_val strict_read_ndetbit) keysvals keyvals). {
      clear -H1.
      apply lift_option_inv in H1.
      generalize dependent keyvals.
      induction keysvals; destruct keyvals; intros; inv H1.
      - constructor.
      - constructor; auto.
        apply eval_sval_to_val_sval_to_val; auto.
    }
    eapply Forall2_sym; [ | eassumption].
    eapply exec_val_sym.
    clear; sauto.
  - eauto.
  - eauto.
Qed.

Definition hoare_table_match_list_intro' : forall p pre_mem pre_ext name keys keysvals keyvals const_entries entryvs cases,
  let entries := const_entries in
  let match_kinds := map table_key_matchkind keys in
  eval_exprs ge p pre_mem (map table_key_key keys) = Some keysvals ->
  lift_option (map eval_sval_to_val keysvals) = Some keyvals ->
  hoare_table_entries ge p entries entryvs ->
  hoare_extern_match_list (combine keyvals match_kinds) entryvs cases ->
  hoare_table_match_list ge p (MEM pre_mem (EXT pre_ext)) name keys (Some const_entries) cases.
Proof.
  intros.
  assert (forall matched_action,
      extern_match (combine keyvals match_kinds) entryvs = matched_action ->
      hoare_table_match ge p (MEM pre_mem (EXT pre_ext)) name keys (Some const_entries) matched_action). {
    unfold hoare_table_match; intros.
    eapply hoare_table_match_case'; eauto.
  }
  induction cases.
  - simpl in H3 |- *.
    auto.
  - simpl in H3 |- *.
    destruct a as [[] ?]; auto.
Qed.

Inductive hoare_table_action_ex_layer : Sval -> Hoare.ret_assertion -> arg_ret_assertion -> Prop :=
  | hoare_table_action_ex_layer_base : forall post_retv post_mem post_ext,
      hoare_table_action_ex_layer post_retv
        (RET ValBaseNull (MEM post_mem (EXT post_ext)))
        (ARG_RET [] post_retv (MEM post_mem (EXT post_ext)))
  | hoare_table_action_ex_layer_ex : forall sv {A} (P : A -> Hoare.ret_assertion) Q,
      (forall (x : A), hoare_table_action_ex_layer sv (P x) (Q x)) ->
      hoare_table_action_ex_layer sv (ret_exists P) (arg_ret_exists Q).

Inductive hoare_table_action_case' : path -> assertion -> list Expression -> Expression -> arg_ret_assertion ->
      (option action_ref) -> Prop :=
  | hoare_table_action_case'_intro : forall p pre_mem pre_ext actions default_action mid post' post
        matched_action action retv,
      get_table_call actions default_action matched_action = Some (action, retv) ->
      hoare_call ge p (MEM pre_mem (EXT pre_ext)) action mid ->
      hoare_table_action_ex_layer (eval_val_to_sval retv) mid post' ->
      arg_ret_implies post' post ->
      hoare_table_action_case' p
        (MEM pre_mem (EXT pre_ext))
        actions default_action
        post matched_action.

Inductive hoare_table_action_cases' (p : path) (pre : assertion) (actions : list Expression)
      (default_action : Expression) (post : arg_ret_assertion) : list (bool * action_ref) -> Prop :=
  | hoare_table_action_cases'_nil :
      hoare_table_action_case' p pre actions default_action post None ->
      hoare_table_action_cases' p pre actions default_action post nil
  | hoare_table_action_cases'_cons : forall (cond : bool) matched_action cases',
      (cond -> hoare_table_action_case' p pre actions default_action post (Some matched_action)) ->
      (~~cond -> hoare_table_action_cases' p pre actions default_action post cases') ->
      hoare_table_action_cases' p pre actions default_action post ((cond, matched_action) :: cases').

Lemma eval_val_to_sval_ret_denote : forall v sv,
  sv = eval_val_to_sval v ->
  ret_denote sv v.
Proof.
  intros; subst.
  unfold ret_denote, ret_satisfies.
  remember (eval_val_to_sval v) as sv' eqn:H0.
  symmetry in H0.
  rewrite <- val_to_sval_iff in H0.
  intros.
  eapply sval_to_val_to_sval; eauto.
  eapply exec_val_sym; only 2 : eapply H0.
  sauto lq: on.
Qed.

Lemma hoare_table_action_case'_hoare_table_action_case_aux : forall retv mid post' post,
  hoare_table_action_ex_layer (eval_val_to_sval retv) mid post' ->
  arg_ret_implies post' post ->
  ret_implies mid (fun (_ : Val) (st : state) => post [] retv st).
Proof.
  intros.
  enough (ret_implies mid (fun (_ : Val) (st : state) => post' [] retv st)). {
    sfirstorder.
  }
  clear H1.
  remember (eval_val_to_sval retv) as sv.
  induction H0.
  - unfold ret_implies.
    intros. destruct H0. split.
    { constructor. }
    split; auto.
    eapply eval_val_to_sval_ret_denote. eauto.
  - unfold ret_implies. intros.
    destruct H2.
    eexists.
    eapply H1; eauto.
Qed.

Lemma hoare_table_action_case'_hoare_table_action_case : forall p pre actions default_action post matched_action,
  hoare_table_action_case' p pre actions default_action post matched_action ->
  hoare_table_action_case ge p pre actions default_action post matched_action.
Proof.
  intros.
  inv H0.
  econstructor; eauto.
  eapply hoare_call_post. 1 : eauto.
  eapply hoare_table_action_case'_hoare_table_action_case_aux; eauto.
Qed.

Lemma hoare_table_action_cases'_hoare_table_action_cases : forall p pre actions default_action post cases,
  hoare_table_action_cases' p pre actions default_action post cases ->
  hoare_table_action_cases ge p pre actions default_action post cases.
Proof.
  induction 1.
  - constructor.
    eapply hoare_table_action_case'_hoare_table_action_case; eauto.
  - constructor; auto.
    intros; eapply hoare_table_action_case'_hoare_table_action_case; eauto.
Qed.

Lemma hoare_func_table' : forall p pre_mem pre_ext name keys actions default_action const_entries post
      cases,
  hoare_table_match_list ge p (MEM pre_mem (EXT pre_ext)) name keys const_entries cases ->
  hoare_table_action_cases' p
    (MEM pre_mem (EXT pre_ext))
    actions default_action
    post cases ->
  hoare_func ge p
    (ARG [] (MEM pre_mem (EXT pre_ext)))
    (FTable name keys actions (Some default_action) const_entries) []
    post.
Proof.
  intros.
  eapply hoare_func_pre.
  2 : { eapply hoare_func_table; eauto.
    eapply hoare_table_action_cases'_hoare_table_action_cases; eauto.
  }
  sfirstorder.
Qed.

Definition AM_ARG (a_arg : list Sval) (a : extern_state -> Prop) :=
  fun args es => arg_denote a_arg args /\ a es.

Definition AM_ARG_RET (a_arg : list Sval) (a_ret : Sval) (a : extern_state -> Prop) :=
  fun args retv es => arg_denote a_arg args
    /\ ret_denote a_ret retv
    /\ a es.

Definition AM_EXT (a_ext : ext_assertion) : extern_state -> Prop :=
  ext_denote a_ext.

Lemma hoare_abstract_method_intro' : forall am_ge p fd pre_arg pre_ext post_arg
    post_retv post_ext,
  hoare_func am_ge p
    (ARG pre_arg (MEM [] (EXT pre_ext)))
    fd []
    (ARG_RET post_arg post_retv (MEM [] (EXT post_ext))) ->
  hoare_abstract_method
    (AM_ARG pre_arg (AM_EXT pre_ext))
    (exec_abstract_method am_ge p fd)
    (AM_ARG_RET post_arg post_retv (AM_EXT post_ext)).
Proof.
  clear ge.
  unfold hoare_func, hoare_abstract_method; intros.
  inv H3.
  eapply H0 in H6.
  2 : {
    split.
    destruct H1.
    2 : { simpl. sfirstorder. }
    eapply Forall2_trans; [ | eassumption | eapply Forall2_trans; [ | eassumption | eassumption ]].
    { refine sval_refine_trans. }
    { refine sval_to_val_to_sval. }
  }
  destruct sig; inv H6.
  unfold AM_ARG_RET.
  intuition.
  2 : { destruct H9; auto. }
  eapply Forall2_trans; [ | eassumption | eapply Forall2_trans; [ | eassumption | eassumption ]].
  { refine sval_refine_trans. }
  { refine sval_to_val_to_sval. }
Qed.

End ConcreteHoare.
