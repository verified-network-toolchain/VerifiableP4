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

(* Test whether p is a subdirectory of any path in ps. *)
Definition paths_cover (ps : list path) (p : path) : bool :=
  existsb (fun p1 => is_prefix p1 p) ps.

Lemma paths_cover_app: forall ps1 ps2 p,
    paths_cover (ps1 ++ ps2) p = (paths_cover ps1 p || paths_cover ps2 p)%bool.
Proof. intros. unfold paths_cover. apply existsb_app. Qed.

Definition ep_wellformed_prop (ps : list path) (P : extern_state -> Prop) :=
  forall es es' : extern_state,
    (forall p, is_true (paths_cover ps p) -> es p = es' p) ->
    P es -> P es'.

Record ext_pred := mk_ext_pred {
  ep_body :> ext_pred_body;
  ep_wellformed : ep_wellformed_prop (ep_paths ep_body) ep_body
}.

Definition mk_ext_pred' a b c :=
  mk_ext_pred (mk_ext_pred_body a b) c.

Local Program Definition singleton (p : path) (eo : extern_object) : ext_pred :=
  mk_ext_pred' (fun es => es p = Some eo) [p] _.
Next Obligation.
  unfold ep_wellformed_prop; intros. rewrite <- H; auto.
  hauto use: is_prefix_refl, ssrbool.orTb.
Qed.

Local Program Definition and (ep1 ep2 : ext_pred) : ext_pred :=
  mk_ext_pred' (ep_pred ep1 `/\ ep_pred ep2) (ep_paths ep1 ++ ep_paths ep2) _.
Next Obligation.
  repeat intro. unfold lift in *. destruct H0.
  destruct ep1 as [[ep1 epp1] ?H]. destruct ep2 as [[ep2 epp2] ?H]. simpl in *.
  split; [eapply H2 with es | eapply H3 with es]; auto; intros; apply H;
    rewrite paths_cover_app; rewrite Reflect.orE; auto.
Qed.

Local Program Definition or (ep1 ep2 : ext_pred) : ext_pred :=
  mk_ext_pred' (ep_pred ep1 `\/ ep_pred ep2) (ep_paths ep1 ++ ep_paths ep2) _.
Next Obligation.
  repeat intro. unfold lift in *.
  destruct ep1 as [[ep1 epp1] ?H]. destruct ep2 as [[ep2 epp2] ?H]. simpl in *.
  destruct H0; [left; eapply H1 with es | right; eapply H2 with es]; auto; intros; apply H;
    rewrite paths_cover_app; rewrite Reflect.orE; auto.
Qed.

Local Program Definition wrap (ps : list path) (ep : ext_pred)
  (H : forall p, is_true (paths_cover (ep_paths ep) p) -> is_true (paths_cover ps p)) : ext_pred :=
  mk_ext_pred' (ep_pred ep) ps _.
Next Obligation.
  red. intros.
  destruct ep as [[ep epp] ?H]. simpl in *.
  eapply H2; eauto.
  (* srun eauto use: ep_wellformed unfold: ep_wellformed_prop. *)
Qed.

End ExtPred.
