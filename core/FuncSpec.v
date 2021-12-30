Require Import Coq.Lists.List.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.ConcreteHoare.
Require Import Hammer.Plugin.Hammer.

Section FuncSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}.

Definition hoare_func_modifies (ge : genv) (p : path) (func : @fundef tags_t) (vars : list path) (exts : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    (forall q, ~(In q vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st'))
    /\ (forall q, ~(In q exts) -> PathMap.get q (snd st) = PathMap.get q (snd st')).

Definition hoare_func_spec (ge : genv) (p : path) (pre : arg_assertion)
    (func : @fundef tags_t) (targs : list P4Type) (post : arg_ret_assertion)
    (vars : list path) (exts : list path) :=
  hoare_func ge p pre func targs post
    /\ hoare_func_modifies ge p func vars exts.

Definition path_eq_dec : forall (p p' : path), {p = p'} + {p <> p'}.
Proof.
  apply list_eq_dec, String.string_dec.
Defined.

Definition exclude {A} (mods : list path) (l : list (path * A)) :=
  filter (fun '(p, _) => negb (In_dec path_eq_dec p mods)) l.

Definition hoare_func_frame (ge : genv) (p : path) (pre : arg_assertion) (func : @fundef tags_t) (targs : list P4Type) (post : assertion) :=
  forall st inargs st' outargs sig,
    pre inargs st ->
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    post st'.

Lemma hoare_func_frame_intro : forall ge p a_arg a_mem a_ext func targs vars exts a_mem' a_ext',
  hoare_func_modifies ge p func vars exts ->
  exclude vars a_mem = a_mem' ->
  exclude exts a_ext = a_ext' ->
  hoare_func_frame ge p (ARG a_arg (MEM a_mem (EXT a_ext))) func targs (MEM a_mem' (EXT a_ext')).
Proof.
  unfold hoare_func_modifies, hoare_func_frame; intros.
  specialize (H _ _  _ _ _ _ H3).
  destruct H.
  destruct st; destruct st'.
  destruct H2 as [_ []].
  split.
  - clear -H H0 H2.
    generalize dependent a_mem'.
    induction a_mem; intros.
    + subst. constructor.
    + simpl in H0. destruct a as [p ?]. destruct (in_dec path_eq_dec p vars) as [H_In | H_In].
      * subst; simpl. apply IHa_mem; auto.
        inv H2; auto.
      * subst; simpl. constructor. 
        ++simpl in H; simpl.
          rewrite <- H by auto.
          inv H2; auto.
        ++apply IHa_mem; auto.
          inv H2; auto.
  - clear -H1 H5 H4.
    generalize dependent a_ext'.
    induction a_ext; intros.
    + subst. constructor.
    + simpl in H1. destruct a as [p ?]. destruct (in_dec path_eq_dec p exts) as [H_In | H_In].
      * subst; simpl. apply IHa_ext; auto.
        inv H5; auto.
      * subst; simpl. constructor. 
        ++simpl in H4; simpl.
          rewrite <- H4 by auto.
          inv H5; auto.
        ++apply IHa_ext; auto.
          inv H5; auto.
Qed.

Inductive func_post_combine : assertion -> arg_ret_assertion -> arg_ret_assertion -> Prop :=
  | func_post_combine_base : forall f_mem f_ext a_arg a_ret a_mem a_ext,
      func_post_combine
        (MEM f_mem (EXT f_ext))
        (ARG_RET a_arg a_ret (MEM a_mem (EXT a_ext)))
        (ARG_RET a_arg a_ret (MEM (f_mem ++ a_mem) (EXT (f_ext ++ a_ext))))
  | func_post_combine_ex : forall [A] F (P : A -> arg_ret_assertion) Q,
      (forall (x : A), func_post_combine F (P x) (Q x)) ->
      func_post_combine F (arg_ret_exists P) (arg_ret_exists Q).

Lemma func_post_combine_sound : forall outargs retv st F P Q,
  func_post_combine F P Q ->
  F st ->
  P outargs retv st ->
  Q outargs retv st.
Proof.
  intros. induction H.
  - destruct H1 as [? []].
    split; eauto.
    split; eauto.
    destruct st; split.
    + apply AssertionLang.mem_denote_app. sfirstorder.
    + apply AssertionLang.ext_denote_app. sfirstorder.
  - destruct H1.
    eexists; eauto.
Qed.

Lemma func_spec_combine : forall ge p pre func targs post vars exts post' frame,
  hoare_func_spec ge p pre func targs post' vars exts ->
  hoare_func_frame ge p pre func targs frame ->
  func_post_combine frame post' post ->
  hoare_func ge p pre func targs post.
Proof.
  unfold hoare_func; intros.
  destruct H.
  epose proof (H _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct sig; only 1, 3, 4 : solve [inv H5].
  eapply (func_post_combine_sound _ _ _ _ _ _ H1); eauto.
Qed.

Lemma func_spec_combine' : forall ge p pre_arg pre_mem pre_ext func targs post vars exts post' f_mem f_ext,
  hoare_func_spec ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) func targs post' vars exts ->
  exclude vars pre_mem = f_mem ->
  exclude exts pre_ext = f_ext ->
  func_post_combine (MEM f_mem (EXT f_ext)) post' post ->
  hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) func targs post.
Proof.
  intros.
  eapply func_spec_combine; eauto.
  destruct H.
  eapply hoare_func_frame_intro; eauto.
Qed.

End FuncSpec.
