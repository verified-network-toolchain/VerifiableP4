Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.EvalExpr.
Require Import Poulet4.V1Model.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.
Require Import Coq.ZArith.BinInt.

Section ConcreteHoare.

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

Lemma hoare_stmt_assign' : forall p a_mem a_ext tags lhs rhs typ a_mem' ret_post lv sv,
  is_call_expression rhs = false ->
  is_no_dup (map fst a_mem) ->
  eval_lexpr lhs = Some lv ->
  eval_expr ge p a_mem rhs = Some sv ->
  eval_write a_mem lv sv = Some a_mem' ->
  hoare_stmt ge p (MEM a_mem (EXT a_ext)) (MkStatement tags (StatAssignment lhs rhs) typ)
      (mk_post_assertion (MEM a_mem' (EXT a_ext)) ret_post).
Proof.
  intros.
  eapply hoare_stmt_assign.
  - assumption.
  - apply eval_lexpr_sound; eassumption.
  - apply hoare_expr_det_intro, eval_expr_sound; eassumption.
  - apply eval_write_sound; only 1 : apply is_no_dup_NoDup; eassumption.
Qed.

(* Inductive Disjoint {A} : list A -> list A -> Prop :=
  | Disjoint_nil : forall al', Disjoint  [] al'
  | Disjoint_cons : forall a al al', ~In a al' -> Disjoint al al' -> Disjoint (a :: al) al'.

Fixpoint is_disjoint (al bl : list path) : bool :=
  match al with
  | x :: al => ~~(is_in x bl) && is_disjoint al bl
  | [] => true
  end.

Lemma is_disjoint_Disjoint : forall (al bl : list path),
  is_disjoint al bl -> Disjoint al bl.
Proof.
  induction al; intros.
  - constructor.
  - simpl in H0. rewrite Reflect.andE in H0. destruct H0.
    constructor.
    + apply not_is_in_not_In; auto.
    + auto.
Qed. *)

Definition ret_implies (P Q : Hoare.ret_assertion) :=
  forall retv st, P retv st -> Q retv st.

Definition ret_exists {A} (a : A -> Hoare.ret_assertion) : Hoare.ret_assertion :=
  fun retv st => ex (fun x => a x retv st).

Definition arg_ret_exists {A} (a : A -> Hoare.arg_ret_assertion) : Hoare.arg_ret_assertion :=
  fun args retv st => ex (fun x => a x args retv st).

Declare Scope post_cond.
Delimit Scope post_cond with post_cond.
Notation "'EX' x .. y , P " :=
  (arg_ret_exists (fun x => .. (arg_ret_exists (fun y => P%post_cond)) ..)) (at level 65, x binder, y binder, right associativity) : post_cond.

Inductive inv_func_copy_out (out_params : list path) : Hoare.ret_assertion -> Hoare.arg_ret_assertion -> Prop :=
  | inv_func_copy_out_base : forall a_arg a_ret a_mem a_ext,
      length out_params = length a_arg ->
      NoDup (out_params ++ (map fst a_mem)) ->
      inv_func_copy_out out_params
        (RET a_ret (MEM (eval_write_vars a_mem out_params a_arg) (EXT a_ext)))
        (ARG_RET a_arg a_ret (MEM a_mem (EXT a_ext)))
  | inv_func_copy_out_ex : forall {A} (P : A -> Hoare.ret_assertion) Q,
      (forall (x : A), inv_func_copy_out out_params (P x) (Q x)) ->
      inv_func_copy_out out_params (ret_exists P) (arg_ret_exists Q).

Axiom AList_get_set_some_neq : forall (a_mem : mem_assertion) (p p' : path) sv,
  p <> p' ->
  AList.get (AList.set_some a_mem p' sv) p = AList.get a_mem p.

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

Lemma lift_option_inv : forall {A} (xl : list (option A)) (al : list A),
  lift_option xl = Some al ->
  xl = map Some al.
Proof.
  induction xl; intros.
  - inv H0. auto.
  - destruct a.
    + simpl in H0. destruct (lift_option xl).
      * inv H0. simpl; f_equal; auto.
      * inv H0.
    + inv H0.
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
  rewrite Utils.map_fst_combine; auto.
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
  - eapply eval_write_vars_implies'; eauto.
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
  unfold extract_parameters in H3.
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
  - apply inv_func_copy_out_sound_part1; auto.
  - unfold hoare_func_copy_out. intros.
    destruct H2 as [x ?].
    exists x.
    apply H1; eauto.
Qed.

Lemma hoare_func_internal' : forall p pre_arg pre_mem pre_ext params init body targs mid1_mem mid2 mid3 post,
  length (filter_in params) = length pre_arg ->
  is_no_dup (map fst pre_mem) ->
  eval_write_vars pre_mem (filter_in params) pre_arg = mid1_mem ->
  hoare_block ge p (MEM mid1_mem (EXT pre_ext)) init (mk_post_assertion mid2 mid3) ->
  hoare_block ge p mid2 body (return_post_assertion_1 mid3) ->
  inv_func_copy_out (filter_out params) mid3 post ->
  hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) (FInternal params init body) targs post.
Proof.
Admitted.

End ConcreteHoare.
