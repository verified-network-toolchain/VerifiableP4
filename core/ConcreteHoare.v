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
Require Import Coq.ZArith.BinInt.

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
  post_return : ret_assertion * (mem_assertion * ext_assertion)
}.

Definition to_shallow_assertion_continue (a : assertion) :=
  match a with (a_mem, a_ext) =>
  (fun (st : state) => let (m, es) := st in
    to_shallow_assertion this a_mem m /\
    ext_to_shallow_assertion this a_ext es)
  end.

Definition to_shallow_assertion_return (a : ret_assertion * (mem_assertion * ext_assertion)) :=
  match a with (a_ret, (a_mem, a_ext)) =>
  (fun vret (st : state) => let (m, es) := st in
    ret_to_shallow_assertion a_ret vret /\
    to_shallow_assertion this a_mem m /\
    ext_to_shallow_assertion this a_ext es)
  end.

Definition to_shallow_post_assertion (post : post_assertion) : Hoare.post_assertion :=
  match post with mk_post_assertion a_continue a_return =>
  Hoare.mk_post_assertion (to_shallow_assertion_continue a_continue) (to_shallow_assertion_return a_return)
  end.

Definition to_shallow_arg_assertion (a : arg_assertion * (mem_assertion * ext_assertion)) : Hoare.arg_assertion :=
  match a with (a_arg, (a_mem, a_ext)) =>
  (fun args (st : state) =>
    arg_to_shallow_assertion a_arg args /\
    to_shallow_assertion_continue (a_mem, a_ext) st)
  end.

Definition to_shallow_arg_ret_assertion (a : arg_assertion * ret_assertion * (mem_assertion * ext_assertion)) : Hoare.arg_ret_assertion :=
  match a with (a_arg, a_ret, (a_mem, a_ext)) =>
  (fun args vret (st : state) =>
    arg_to_shallow_assertion a_arg args /\
    ret_to_shallow_assertion a_ret vret /\
    to_shallow_assertion_continue (a_mem, a_ext) st)
  end.

Definition to_shallow_ret_assertion (a : ret_assertion * (mem_assertion * ext_assertion)) : Hoare.ret_assertion :=
  match a with (a_ret, (a_mem, a_ext)) =>
  (fun vret (st : state) =>
    ret_to_shallow_assertion a_ret vret /\
    to_shallow_assertion_continue (a_mem, a_ext) st)
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

Lemma implies_refl : forall (a : assertion),
  implies a a.
Proof.
  clear ge inst_m this. admit.
Admitted.

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
  is_writable_lval lv (fst pre) /\ (eval_write (fst pre) lv v, snd pre) = post.

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

Definition option_to_list {A} (ox : option A) : list A :=
  match ox with
  | Some x => [x]
  | None => nil
  end.

Definition eval_copy_in (pre : arg_assertion * assertion) (params : list Locator) : assertion :=
  match pre with (pre_arg, (pre_mem, pre_ext)) =>
    let pre_mem_1 := fold_left clear_loc params pre_mem in
    let post_mem := fold_left
        (fun post_mem a_unit => post_mem ++ option_to_list (arg_assertion_unit_to_assertion_unit params a_unit))
        pre_arg
        pre_mem_1 in
    (post_mem, pre_ext)
  end.

Inductive hoare_copy_in : arg_assertion * assertion -> list Locator -> assertion -> Prop :=
  | hoare_copy_in_intro : forall pre params post,
      eval_copy_in pre params = post ->
      hoare_copy_in pre params post.

Fixpoint eval_outargs (* (pre : assertion) *) (dirs : list direction) (args : list (option Expression))
    : option (list (option Lval)) :=
  match dirs, args with
  | [], [] => Some nil
  | dir :: dirs, arg :: args =>
      let olvs := eval_outargs (* pre *) dirs args in
      match dir with
      | Out | InOut =>
          match arg with
          | Some expr =>
              match eval_lexpr expr with
              | Some lv => option_map (cons (Some lv)) olvs
              | None => None
              end
          | None => option_map (cons None) olvs
          end
      | _ => olvs
      end
  | _, _ => None
  end.

Inductive hoare_outargs : assertion -> list direction -> list (option Expression) -> list (option Lval) -> Prop :=
  | hoare_outargs_intro : forall pre dirs args lvs,
      eval_outargs dirs args = Some lvs ->
      hoare_outargs pre dirs args lvs.

(*   | exec_expr_name: forall name loc v this st tag typ dir,
                    loc_to_val this loc st = Some v ->
                    exec_expr this st
                    (MkExpression tag (ExpName name loc) typ dir)
                    v *)

Definition assertion_unit_to_arg_assertion_unit (a_unit : @assertion_unit tags_t) (cnt : Z) : arg_assertion_unit :=
  match a_unit with
  | AVal (_, fl) v => ArgVal (cnt, fl) v
  | AType (_, fl) typ => ArgType (cnt, fl) typ
  end.

Fixpoint filter_locator_replace (a : mem_assertion) (loc : Locator) (cnt : Z) : arg_assertion :=
  match a with
  | a_unit :: a =>
      let loc' :=
        match a_unit with
        | AVal (loc', _) _ => loc'
        | AType (loc', _) _ => loc'
        end in
      if locator_equivb loc' loc then
        assertion_unit_to_arg_assertion_unit a_unit cnt :: filter_locator_replace a loc cnt
      else
        filter_locator_replace a loc cnt
  | [] => []
  end.

Fixpoint eval_inargs (pre : assertion) (dirs : list direction) (args : list (option Expression)) (cnt : Z) : option arg_assertion :=
  match dirs, args with
  | [], [] => Some nil
  | dir :: dirs, arg :: args =>
      match dir with
      | Typed.In | InOut =>
          match arg with
          | Some expr =>
              match expr with
              | MkExpression _ (ExpName _ loc) _ _ =>
                  option_map (app (filter_locator_replace (fst pre) loc cnt)) (eval_inargs pre dirs args (cnt + 1))
              | _ =>
                  match eval_expr ge (fst pre) expr with
                  | Some v => option_map (cons (ArgVal (cnt, []) v)) (eval_inargs pre dirs args (cnt + 1))
                  | None => None
                  end
              end
          | None => None
          end
      | _ => eval_inargs pre dirs args cnt
      end
  | _, _ => None
  end.

Inductive hoare_inargs : assertion -> list direction -> list (option Expression) -> arg_assertion * assertion -> Prop :=
  | hoare_inargs_intro : forall pre dirs args post,
      eval_inargs pre dirs args 0 = Some post ->
      hoare_inargs pre dirs args (post, pre).

Fixpoint eval_copy_out (pre : assertion) (params : list Locator) (cnt : Z) : arg_assertion :=
  match params with
  | param :: params =>
      app (filter_locator_replace (fst pre) param cnt) (eval_copy_out pre params (cnt + 1))
  | [] => []
  end.

Inductive hoare_copy_out : assertion -> list Locator -> arg_assertion * assertion -> Prop :=
  | hoare_copy_out_intro : forall pre params post_arg,
      eval_copy_out pre params 0 = post_arg ->
      hoare_copy_out pre params (post_arg, pre).

(* Definition eval_copy_in (pre : arg_assertion * assertion) (params : list Locator) : assertion :=
  match pre with (pre_arg, (pre_mem, pre_ext)) =>
    let pre_mem_1 := fold_left clear_loc params pre_mem in
    let post_mem := fold_left
        (fun post_mem a_unit => post_mem ++ option_to_list (arg_assertion_unit_to_assertion_unit params a_unit))
        pre_arg
        pre_mem_1 in
    (post_mem, pre_ext)
  end. *)

(* Inductive hoare_copy_in : arg_assertion * assertion -> list Locator -> assertion -> Prop :=
  | hoare_copy_in_intro : forall pre params post,
      eval_copy_in pre params = post ->
      hoare_copy_in pre params post. *)

Fixpoint olvals_to_locs (outlvs : list (option Lval)) : option (list Locator) :=
  match outlvs with
  | lv :: outlvs =>
      match lv with
      | Some (loc, []) => option_map (cons loc) (olvals_to_locs outlvs)
      | _ => None
      end
  | [] => Some []
  end.

Definition eval_write_copy_out (pre : arg_assertion * ret_assertion * assertion) (outlvs : list (option Lval)) : option (ret_assertion * assertion) :=
  match olvals_to_locs outlvs with
  | Some locs =>
      match pre with (pre_arg, pre_ret, (pre_mem, pre_ext)) =>
        let pre_mem_1 := fold_left clear_loc locs pre_mem in
        let post_mem := fold_left
            (fun post_mem a_unit => post_mem ++ option_to_list (arg_assertion_unit_to_assertion_unit locs a_unit))
            pre_arg
            pre_mem_1 in
        Some (pre_ret, (post_mem, pre_ext))
      end
  | None => None
  end.

Inductive hoare_write_copy_out : arg_assertion * ret_assertion * assertion -> list (option Lval) -> ret_assertion * assertion -> Prop :=
  | hoare_write_copy_out_intro : forall pre outlvs post,
      eval_write_copy_out pre outlvs = Some post ->
      hoare_write_copy_out pre outlvs post.

Definition ret_assertion_to_assertion (a : ret_assertion * assertion) : assertion :=
  snd a.

Lemma hoare_stmt_sound : forall p pre stmt post,
  wellformed (fst pre) ->
  hoare_stmt p pre stmt post ->
  Hoare.deep_hoare_stmt ge inst_m p (to_shallow_assertion_continue p pre) stmt (to_shallow_post_assertion p post).
Proof.
  intros * H_wellformed H_hoare_stmt.
  apply deep_hoare_stmt_fallback.
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

Lemma hoare_copy_in_sound : forall p pre params post,
  hoare_copy_in pre params post ->
  Hoare.deep_hoare_copy_in p (to_shallow_arg_assertion p pre) params (to_shallow_assertion_continue p post).
Proof.
  clear ge inst_m.
  admit.
Admitted.

Lemma hoare_outargs_sound : forall p pre dirs args lvs,
  hoare_outargs pre dirs args lvs ->
  Hoare.deep_hoare_outargs (H := V1Model) ge p (to_shallow_assertion_continue p pre) dirs args
      (map (option_map lval_to_semlval) lvs).
Proof.
  clear inst_m.
  admit.
Admitted.

Lemma hoare_inargs_sound : forall p pre dirs args post,
  hoare_inargs pre dirs args post ->
  Hoare.deep_hoare_inargs (H := V1Model) ge p (to_shallow_assertion_continue p pre) dirs args
      (to_shallow_arg_assertion p post).
Proof.
  clear inst_m.
  admit.
Admitted.

Lemma hoare_copy_out_sound : forall p pre params post,
  hoare_copy_out pre params post ->
  Hoare.implies (to_shallow_assertion_continue p pre) (return_post_assertion_1 (generate_post_condition p params (to_shallow_arg_ret_assertion p (fst post, [], snd post)))).
Proof.
  clear ge inst_m.
  admit.
Admitted.

Lemma hoare_write_copy_out_sound : forall p pre outlvs post,
  hoare_write_copy_out pre outlvs post ->
  deep_hoare_write_copy_out p (to_shallow_arg_ret_assertion p pre) (map (option_map lval_to_semlval) outlvs) (to_shallow_ret_assertion p post) .
Proof.
  clear ge inst_m.
  admit.
Admitted.

Lemma ret_assertion_to_assertion_sound : forall p pre post,
  ret_assertion_to_assertion pre = post ->
  Hoare.ret_assertion_to_assertion (to_shallow_ret_assertion p pre) = (to_shallow_assertion_continue p post).
Proof.
  clear ge inst_m.
  admit.
Admitted.

End ConcreteHoare.
