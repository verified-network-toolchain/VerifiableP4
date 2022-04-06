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
Require Import ProD3.core.Modifies.
Require Import Hammer.Plugin.Hammer.

Section FuncSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}.

(* A func spec contains two levels binders. A func spec is like
  WITH (p : path) ... ,
    PATH p
    MOD [...] [...]
    WITH (x : X) ... ,
      PRE ...
      POST ...
*)

Inductive func_spec_hoare : Type :=
  | fsh_base : arg_assertion -> arg_ret_assertion -> func_spec_hoare
  | fsh_bind {A} : (A -> func_spec_hoare) -> func_spec_hoare.

Record func_spec_aux : Type := mk_func_spec {
  func_spec_p : path;
  func_spec_body : func_spec_hoare;
  func_spec_mod_vars : option (list path); (* None means anything can be modified. *)
  func_spec_mod_exts : list path
}.

Inductive func_spec : Type :=
  | fs_base : func_spec_aux -> func_spec
  | fs_bind {A} : (A -> func_spec) -> func_spec.

Fixpoint fundef_satisfies_hoare (ge : genv) (p : path) (func : fundef) (targs : list (P4Type)) (fs : func_spec_hoare) :=
  match fs with
  | fsh_base pre post =>
       hoare_func ge p pre func targs post
  | @fsh_bind A fs =>
      (* How can we keep binder names? *)
      forall (x : A), fundef_satisfies_hoare ge p func targs (fs x)
  end.

Definition fundef_satisfies_spec_aux (ge : genv) (func : fundef) (targs : list (P4Type)) (fs : func_spec_aux) :=
  let '(mk_func_spec p body vars exts) := fs in
  fundef_satisfies_hoare ge p func targs body
    /\ func_modifies ge p func vars exts.

Fixpoint fundef_satisfies_spec (ge : genv) (func : fundef) (targs : list (P4Type)) (fs : func_spec) :=
  match fs with
  | fs_base fs =>
      fundef_satisfies_spec_aux ge func targs fs
  | @fs_bind A fs =>
      (* How can we keep binder names? *)
      forall (x : A), fundef_satisfies_spec ge func targs (fs x)
  end.

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
  force True (option_map (func_modifies_vars ge p func) vars) ->
  func_modifies_exts ge p func exts ->
  force (fun _ => []) (option_map exclude vars) a_mem = a_mem' ->
  exclude exts a_ext = a_ext' ->
  hoare_func_frame ge p (ARG a_arg (MEM a_mem (EXT a_ext))) func targs (MEM a_mem' (EXT a_ext')).
Proof.
  unfold func_modifies_vars, func_modifies_exts, hoare_func_frame; intros.
  (* specialize (H _ _  _ _ _ _ H3).
  destruct H. *)
  destruct st; destruct st'.
  (* destruct H3 as [_ []]. *)
  split.
  - clear -H H1 H3 H4.
    destruct vars as [vars | ].
    2 : { subst; constructor. }
    specialize (H _ _  _ _ _ _ H4).
    destruct H3 as [_ []].
    generalize dependent a_mem'.
    induction a_mem; intros.
    + subst. constructor.
    + simpl in H1. destruct a as [p' ?]. destruct (in_dec path_eq_dec p' vars) as [H_In | H_In].
      * subst; simpl. apply IHa_mem; auto.
        inv H0; auto.
      * subst; simpl. constructor.
        ++simpl in H; simpl.
          rewrite <- H by auto.
          inv H0; auto.
        ++apply IHa_mem; auto.
          inv H0; auto.
  - clear -H0 H2 H3 H4.
    generalize dependent a_ext'.
    specialize (H0 _ _  _ _ _ _ H4).
    destruct H3 as [_ []].
    induction a_ext; intros.
    + subst. constructor.
    + simpl in H2. destruct a as [p' ?]. destruct (in_dec path_eq_dec p' exts) as [H_In | H_In].
      * subst; simpl. apply IHa_ext; auto.
        inv H1; auto.
      * subst; simpl. constructor.
        ++simpl in H0; simpl.
          rewrite <- H0 by auto.
          inv H1; auto.
        ++apply IHa_ext; auto.
          inv H1; auto.
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

Lemma func_spec_combine : forall ge p pre pre' func targs post post' frame,
  arg_implies pre pre' ->
  hoare_func ge p pre' func targs post' ->
  hoare_func_frame ge p pre func targs frame ->
  func_post_combine frame post' post ->
  hoare_func ge p pre func targs post.
Proof.
  unfold hoare_func; intros.
  specialize (H _ _ H3).
  epose proof (H0 _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
  destruct sig; only 1, 3, 4 : solve [inv H5].
  eapply (func_post_combine_sound _ _ _ _ _ _ H2); eauto.
Qed.

Lemma func_spec_combine' : forall ge p pre_arg pre_mem pre_ext pre_arg' pre_mem' pre_ext' func targs post vars exts post' f_mem f_ext,
  fundef_satisfies_hoare ge p func targs
    (fsh_base (ARG pre_arg' (MEM pre_mem' (EXT pre_ext'))) post')
    /\ func_modifies ge p func vars exts ->
  arg_implies (ARG pre_arg (MEM pre_mem (EXT pre_ext))) (ARG pre_arg' (MEM pre_mem' (EXT pre_ext'))) ->
  force (fun _ => []) (option_map exclude vars) pre_mem = f_mem ->
  exclude exts pre_ext = f_ext ->
  func_post_combine (MEM f_mem (EXT f_ext)) post' post ->
  hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) func targs post.
Proof.
  intros.
  destruct H.
  eapply func_spec_combine; eauto.
  eapply hoare_func_frame_intro; eauto.
  - destruct vars.
    + unfold func_modifies_vars; simpl; intros.
      refine (proj1 (H4 _ _ _ _ _ _ _) _ _); eauto.
    + simpl; auto.
  - unfold func_modifies_exts; intros.
    refine (proj2 (H4 _ _ _ _ _ _ _) _ _); eauto.
Qed.

End FuncSpec.

Declare Scope func_spec.
Delimit Scope func_spec with func_spec.
Declare Scope func_hoare.
Delimit Scope func_hoare with func_hoare.

Notation "'WITH' , P " :=
  (fs_base P%func_spec) (at level 65, right associativity) : func_spec.

Notation "'WITH' x .. y , P " :=
  (fs_bind (fun x => .. (fs_bind (fun y => fs_base P%func_spec)) ..)) (at level 65, x binder, y binder, right associativity) : func_spec.

Notation "'PATH' p 'MOD' vars exts body" :=
  (mk_func_spec p body%func_hoare vars exts) (at level 64, vars at level 0, exts at level 0) : func_spec.

Notation "'WITH' , 'PRE' pre 'POST' post" :=
  (fsh_base pre post) (at level 63, right associativity) : func_hoare.

Notation "'WITH' x .. y , 'PRE' pre 'POST' post" :=
  (fsh_bind (fun x => .. (fsh_bind (fun y => fsh_base pre post)) ..)) (at level 63, x binder, y binder, right associativity) : func_hoare.
