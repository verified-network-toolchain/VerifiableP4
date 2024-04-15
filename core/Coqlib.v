Require Export Coq.Lists.List.
Require Export Coq.ssr.ssrbool.
Require Export Coq.micromega.Lia.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Poulet4.Utils.Utils.
Require Export Coq.ZArith.BinInt.
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

Open Scope Z_scope.

(* destruct a list into elements when the length is a constant. *)
Lemma Zlength_0_nil {A} : forall (al : list A),
  Zlength al = 0 ->
  al = nil.
Proof.
  intros. destruct al; list_solve.
Qed.

Lemma Zlength_gt_0_destruct {A} : forall (al : list A) n,
  Zlength al = n ->
  0 < n ->
  exists x al', al = x :: al' /\ Zlength al' = n - 1.
Proof.
  intros.
  destruct al; only 1 : list_solve.
  assert (Zlength al = n - 1) by list_solve.
  eauto.
Qed.

Lemma Zlength_lt_0_False {A} : forall (al : list A) n,
  Zlength al = n ->
  0 > n ->
  False.
Proof.
  intros. list_solve.
Qed.

Ltac destruct_list xs :=
  lazymatch goal with
  | H : Zlength xs = ?n |- _ =>
      let n' := eval compute in n in
      lazymatch n' with
      | Z0 => apply Zlength_0_nil in H; subst xs
      | Zpos _ =>
          first [ (* in case of H is used somewhere else *)
            apply Zlength_gt_0_destruct in H; only 2 : reflexivity;
            let xs' := fresh "xs" in
            destruct H as [?x [xs' []]]; subst xs; destruct_list xs'
          | let H' := fresh in
            pose proof H as H';
            apply Zlength_gt_0_destruct in H'; only 2 : reflexivity;
            let xs' := fresh "xs" in
            destruct H' as [?x [xs' []]]; subst xs; destruct_list xs'
          ]
      | Zneg _ =>
          first [ (* in case of H is used somewhere else *)
            apply Zlength_lt_0_False in H; only 2 : reflexivity;
            inversion H
          | let H' := fresh in
            pose proof H as H';
            apply Zlength_lt_0_False in H'; only 2 : reflexivity;
            inversion H'
          ]
      end
  | _ =>
      idtac "Length of" xs "is not found"
  end.

Lemma list_head_app: forall {A: Type} a (l : list A), a :: l = [a] ++ l.
Proof. list_solve. Qed.

Lemma list_app_head_app: forall {A: Type} a (l1 l2 : list A), l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. intros. rewrite <- app_assoc. f_equal. Qed.

#[local] Ltac cut_list_n0_in H n :=
  match n with
  | O => idtac
  | S O => idtac
  | S (S ?n') => rewrite list_app_head_app in H; unfold app in H at 2; (cut_list_n0_in H n')
  end.

Ltac cut_list_n_in H n :=
  match type of n with
  | nat => rewrite list_head_app in H; cut_list_n0_in H n
  | _ => idtac "Error: n must be a nat."
  end.

#[local] Ltac cut_list_n0 n :=
  match n with
  | O => idtac
  | S O => idtac
  | S (S ?n') => rewrite list_app_head_app; unfold app at 2; (cut_list_n0 n')
  end.

Ltac cut_list_n n :=
  match type of n with
  | nat => rewrite list_head_app; cut_list_n0 n
  | _ => idtac "Error: n must be a nat."
  end.
