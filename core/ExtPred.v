Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Poulet4.Utils.Maps.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Architecture.Target.
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

Definition in_scope (p1 : path) (p2 : path) : bool :=
  is_prefix p2 p1.

(* Test whether p is inside one of the scopes in ps. *)
Definition in_scopes (p : path) (ps : list path) : bool :=
  existsb (in_scope p) ps.

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

Local Program Definition wrap (ps : list path) (ep : ext_pred)
  (H : forall p, is_true (in_scopes p (ep_paths ep)) -> is_true (in_scopes p ps)) : ext_pred :=
  mk_ext_pred' (ep_pred ep) ps _.
Next Obligation.
  red. intros.
  destruct ep as [[ep epp] ?H]. simpl in *.
  eapply H2; eauto.
  (* srun eauto use: ep_wellformed unfold: ep_wellformed_prop. *)
Qed.

End ExtPred.
