Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Definitions.

Require Import Poulet4.Utils.Maps.

Require Import Poulet4.P4light.Syntax.Syntax.

Require Import Poulet4.P4light.Architecture.Target.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope list_scope.

Definition lift {A B C D : Type} (f : B -> C -> D) (g : A -> B) (h : A -> C) : A -> D :=
  fun (a : A) => f (g a) (h a).

Notation "A `/\ B" := (lift and A B) (at level 80, right associativity).
Notation "A `\/ B" := (lift or A B) (at level 85, right associativity).

Section ExtPred.

Notation ident := string.
Notation path := (list string).
Context {tags_t : Type}.
Context {target : @Target tags_t (@Expression tags_t)}.

(* We define a kind of ext_pred for extern state, that contains two parts
  ep_pred and ep_paths, with a well-formed condition. If ep_paths = [p1,
  p2, ...], then ep_pred is only relevent with objects in directories of
  p1, p2, ... *)

Record ext_pred_body := mk_ext_pred_body {
  ep_pred :> extern_state -> Prop;
  ep_paths : list path
}.

Fixpoint is_prefix (p1 : path) (p2 : path) : bool :=
  match p1 with
  | [] => true
  | n :: p1 =>
      match p2 with
      | [] => false
      | m :: p2 =>
          if String.eqb n m then is_prefix p1 p2 else false
      end
  end.

Lemma is_prefix_refl : forall p,
  is_prefix p p = true.
Proof.
  intros.
  induction p.
  - reflexivity.
  - simpl. hauto use: eqb_eq inv: bool.
Qed.

Lemma is_prefix_trans : forall p1 p2 p3,
  is_prefix p1 p2 ->
  is_prefix p2 p3 ->
  is_prefix p1 p3.
Proof.
  induction p1; intros.
  - reflexivity.
  - hfcrush use: eqb_eq unfold: is_prefix, is_true inv: list.
Qed.

Lemma is_prefix_cancel : forall p1 p2 p3,
  is_prefix (p1 ++ p2) (p1 ++ p3) = is_prefix p2 p3.
Proof.
  induction p1; intros.
  - reflexivity.
  - simpl. rewrite eqb_refl. auto.
Qed.

Definition in_scope (p1 : path) (p2 : path) : bool :=
  is_prefix p2 p1.

(* Test whether p is inside one of the scopes in ps. *)
Definition in_scopes (p : path) (ps : list path) : bool :=
  existsb (in_scope p) ps.

Lemma in_scopes_trans : forall p1 p2 ps,
  in_scope p1 p2 ->
  in_scopes p2 ps ->
  in_scopes p1 ps.
Proof.
  induction ps; intros.
  - inv H0.
  - simpl. rewrite Reflect.orE.
    simpl in H0. rewrite Reflect.orE in H0. destruct H0.
    + eauto using is_prefix_trans.
    + auto.
Qed.

Lemma in_scopes_app: forall p ps1 ps2,
    in_scopes p (ps1 ++ ps2) = (in_scopes p ps1 || in_scopes p ps2)%bool.
Proof. intros. unfold in_scopes. apply existsb_app. Qed.

Lemma in_scopes_incl: forall exts exts' q,
    (forall x : path, In x exts' -> In x exts) ->
    is_true (in_scopes q exts') -> is_true (in_scopes q exts).
Proof.
  unfold is_true, in_scopes. intros. rewrite existsb_exists in *.
  destruct H0 as [x [? ?]]. exists x. split; auto.
Qed.

Lemma in_scopes_In: forall ps p, In p ps -> is_true (in_scopes p ps).
Proof.
  intros. red. unfold in_scopes. rewrite existsb_exists.
  exists p. split; auto. apply is_prefix_refl.
Qed.

Definition ep_wellformed_prop (ps : list path) (P : extern_state -> Prop) :=
  forall es es' : extern_state,
    (forall p, is_true (in_scopes p ps) -> PathMap.get p es = PathMap.get p es') ->
    P es -> P es'.

Record ext_pred := mk_ext_pred {
  ep_body :> ext_pred_body;
  ep_wellformed : ep_wellformed_prop (ep_paths ep_body) ep_body
}.

Definition mk_ext_pred' a b c :=
  mk_ext_pred (mk_ext_pred_body a b) c.

(* ep_wellformed_prop lemmas *)

Lemma ep_wellformed_prop_True ps :
  ep_wellformed_prop ps (fun _ => True).
Proof.
  unfold ep_wellformed_prop. auto.
Qed.

Lemma ep_wellformed_prop_and : forall (pred1 pred2 : extern_state -> Prop) ps
  (H_pred1 : ep_wellformed_prop ps pred1)
  (H_pred2 : ep_wellformed_prop ps pred2),
  ep_wellformed_prop ps (lift and pred1 pred2).
Proof.
  sfirstorder.
Qed.

Lemma ep_wellformed_prop_and_app : forall (pred1 pred2 : extern_state -> Prop) ps1 ps2
  (H_pred1 : ep_wellformed_prop ps1 pred1)
  (H_pred2 : ep_wellformed_prop ps2 pred2),
  ep_wellformed_prop (ps1 ++ ps2) (lift and pred1 pred2).
Proof.
  intros. red. setoid_rewrite in_scopes_app.
  hauto b: on.
Qed.

Lemma ep_wellformed_prop_wrap1 : forall ps1 (pred : extern_state -> Prop) ps2
  (H_pred : ep_wellformed_prop ps2 pred),
  (forall p : path, in_scopes p ps2 -> in_scopes p ps1) ->
  ep_wellformed_prop ps1 pred.
Proof.
  sfirstorder.
Qed.

Lemma ep_wellformed_prop_wrap2 : forall ps1 (pred : extern_state -> Prop) ps2
  (H_pred : ep_wellformed_prop ps2 pred),
  forallb (fun p : path => in_scopes p ps1) ps2 ->
  ep_wellformed_prop ps1 pred.
Proof.
  intros.
  eapply ep_wellformed_prop_wrap1; only 1 : eauto.
  intros.
  clear -H H0.
  induction ps2.
  - inv H0.
  - simpl in H. rewrite Reflect.andE in H. destruct H.
    simpl in H0. rewrite Reflect.orE in H0. destruct H0.
    + eauto using in_scopes_trans.
    + auto.
Qed.

Local Program Definition prop (P : Prop) : ext_pred :=
  mk_ext_pred' (fun _ => P) [] _.
Next Obligation.
  unfold ep_wellformed_prop; auto.
Qed.

Local Program Definition singleton (p : path) (eo : extern_object) : ext_pred :=
  mk_ext_pred' (fun es => PathMap.get p es = Some eo) [p] _.
Next Obligation.
  unfold ep_wellformed_prop; intros. rewrite <- H; auto.
  unfold in_scopes, in_scope.
  hauto use: is_prefix_refl, ssrbool.orTb.
Qed.

Local Program Definition and (ep1 ep2 : ext_pred) : ext_pred :=
  mk_ext_pred' (ep_pred ep1 `/\ ep_pred ep2) (ep_paths ep1 ++ ep_paths ep2) _.
Next Obligation.
  repeat intro. unfold lift in *. destruct H0.
  destruct ep1 as [[ep1 epp1] ?H]. destruct ep2 as [[ep2 epp2] ?H]. simpl in *.
  split; [eapply H2 with es | eapply H3 with es]; auto; intros; apply H;
    rewrite in_scopes_app; rewrite Reflect.orE; auto.
Qed.

Local Program Definition or (ep1 ep2 : ext_pred) : ext_pred :=
  mk_ext_pred' (ep_pred ep1 `\/ ep_pred ep2) (ep_paths ep1 ++ ep_paths ep2) _.
Next Obligation.
  repeat intro. unfold lift in *.
  destruct ep1 as [[ep1 epp1] ?H]. destruct ep2 as [[ep2 epp2] ?H]. simpl in *.
  destruct H0; [left; eapply H1 with es | right; eapply H2 with es]; auto; intros; apply H;
    rewrite in_scopes_app; rewrite Reflect.orE; auto.
Qed.

Local Program Definition wrap (ps : list path) (eps : list ext_pred)
  (H : forallb (fun (ep : ext_pred) => forallb (fun p => in_scopes p ps) (ep_paths ep)) eps) : ext_pred :=
  mk_ext_pred' (fold_right (lift Logic.and) (fun _ => True) (map (fun (ep : ext_pred) => ep_pred ep) eps)) ps _.
Next Obligation.
  induction eps.
  - apply ep_wellformed_prop_True.
  - simpl in H. rewrite Reflect.andE in H. destruct H.
    simpl.
    eapply ep_wellformed_prop_and; only 2 : auto.
    eapply ep_wellformed_prop_wrap2; eauto using (ep_wellformed a).
Qed.

Local Program Definition ex [A] (ep : A -> ext_pred) (ps : list path)
  (H : forall (x : A), forallb (fun p => in_scopes p ps) (ep_paths (ep x))) : ext_pred :=
  mk_ext_pred' (fun es => exists (x : A), (ep x) es) ps _.
Next Obligation.
  unfold ep_wellformed_prop; intros.
  destruct H1. exists x.
  specialize (H x).
  eapply ep_wellformed_prop_wrap2; eauto using (ep_wellformed (ep x)).
Qed.

Local Program Definition all [A] (ep : A -> ext_pred) (ps : list path)
  (H : forall (x : A), forallb (fun p => in_scopes p ps) (ep_paths (ep x))) : ext_pred :=
  mk_ext_pred' (fun es => forall (x : A), (ep x) es) ps _.
Next Obligation.
  unfold ep_wellformed_prop; intros.
  specialize (H1 x).
  specialize (H x).
  eapply ep_wellformed_prop_wrap2; eauto using (ep_wellformed (ep x)).
Qed.

(* Two ext_pred's are equivalent if their content predicates are the same. *)
Local Definition equiv (ep1 ep2 : ext_pred) : Prop :=
  ep_pred ep1 = ep_pred ep2.

Global Add Parametric Relation : ext_pred equiv
  reflexivity proved by (fun ep => eq_refl (ep_pred ep))
  symmetry proved by (fun ep1 ep2 => eq_sym (x := ep_pred ep1) (y := ep_pred ep2))
  transitivity proved by (fun ep1 ep2 ep3 => eq_trans (x := ep_pred ep1) (y := ep_pred ep2) (z := ep_pred ep3))
  as equiv_rel.

(* Current ununsed, but looks good to have. *)
Add Parametric Morphism : ep_pred with
  signature equiv ==> eq as ep_pred_mor.
Proof. auto. Qed.

End ExtPred.
