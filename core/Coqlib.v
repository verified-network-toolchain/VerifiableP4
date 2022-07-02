Require Export Coq.Lists.List.
Require Export Coq.ssr.ssrbool.
Require Export Coq.micromega.Lia.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Poulet4.Utils.Utils.
Require Export Coq.ZArith.Zcomplements.
Require Export VST.zlist.Zlist.
Export ListNotations.

Notation "~~" := negb.

Ltac inv H := inversion H; subst; clear H.
Ltac pinv P :=
  lazymatch goal with
  | H : context [P] |- _ => inv H
  (* | H : P |- _ => inv H
  | H : P _ |- _ => inv H
  | H : P _ _ |- _ => inv H
  | H : P _ _ _ |- _ => inv H
  | H : P _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ _ |- _ => inv H
  | H : P _ _ _ _ _ _ _ _ |- _ => inv H *)
  end.

Inductive Forall_fold {A B} (P : A -> B -> A -> Prop) : A -> list B -> A -> Prop :=
  | Forall_fold_nil : forall a,
      Forall_fold P a [] a
  | Forall_fold_cons : forall a b a' bs a'',
      P a b a' ->
      Forall_fold P a' bs a'' ->
      Forall_fold P a (b :: bs) a''.

Inductive Forall2_fold {A B C} (P : A -> B -> C -> A -> Prop) : A -> list B -> list C -> A -> Prop :=
  | Forall2_fold_nil : forall a,
      Forall2_fold P a [] [] a
  | Forall2_fold_cons : forall a b c a' bs cs a'',
      P a b c a' ->
      Forall2_fold P a' bs cs a'' ->
      Forall2_fold P a (b :: bs) (c :: cs) a''.

(* Hinder too eager typeclass resolution. We should eventually put this into zlist. *)
#[global] Hint Mode Inhabitant + : typeclass_instances.

(* We accept this axiom. Maybe it's avoidable but it makes things simpler by accepting it. *)
Axiom prop_ext : ClassicalFacts.prop_extensionality.
