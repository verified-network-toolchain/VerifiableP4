Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Syntax.Value.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.ExtPred.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Implies.
Require Import Hammer.Plugin.Hammer.
Open Scope type_scope.

Section ExtExtract.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation mem := Semantics.mem.

Context {target : @Target tags_t (@Expression tags_t)}.

Fixpoint replace_nth {A} (n : nat) (al : list A) (x : A) {struct n} : list A :=
  match n, al with
  | O, a :: al => x :: al
  | S n', a :: al' => a :: replace_nth n' al' x
  | _, nil => nil
  end.

Lemma extract_nth_ext_ex : forall n a_ext {A} (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  EXT a_ext =
    (fun es => exists x, EXT (replace_nth n a_ext (S x)) es).
Proof.
  intros.
  f_equal.
  clear -H0.
  generalize dependent n; induction a_ext; intros.
  + extensionality es.
    apply prop_ext.
    split; only 2 : hauto lq: on.
    intros _.
    replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H0. 2 : {
      destruct n; auto.
    }
    assert (exists x, S x es). {
      change (ExtPred.ex S ep H es).
      rewrite <- H0.
      exact I.
    }
    destruct H1 as [x ?].
    exists x. unfold replace_nth; destruct n;
      (* sauto q: on should solve it, but it has some bug. *)
      cbn; auto.
  + destruct n.
    * simpl in H0. rewrite H0.
      clear.
      extensionality es.
      apply prop_ext.
      simpl. (* hammer should solve here. *)
      split; intros.
      --destruct H0.
        destruct H0.
        sfirstorder.
      --destruct H0.
        destruct H0.
        split; sfirstorder.
    * specialize (IHa_ext _ H0).
      change (EXT (a :: a_ext)) with (fun es => a es /\ EXT a_ext es).
      rewrite IHa_ext.
      clear.
      extensionality es.
      apply prop_ext.
      simpl. fcrush.
Qed.

Lemma extract_nth_ext_ex' : forall n a_mem a_ext A (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  MEM a_mem (EXT a_ext) =
    (EX (x : A), MEM a_mem (EXT (replace_nth n a_ext (S x))))%assr.
Proof.
  intros.
  erewrite extract_nth_ext_ex; eauto.
  clear.
  extensionality st.
  apply prop_ext.
  (* hammer should solve here *)
  split; intros.
  - destruct st.
    destruct H.
    destruct H0.
    sfirstorder.
  - destruct st.
    destruct H.
    sfirstorder.
Qed.

Lemma extract_nth_ext_ex'' : forall n pre a_ext A (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  (exists x, ext_implies pre (replace_nth n a_ext (S x))) ->
  ext_implies pre a_ext.
Proof.
  intros.
  destruct H1.
  unfold ext_implies in *.
  change ext_denote with EXT in *.
  erewrite extract_nth_ext_ex with (a_ext := a_ext) by eauto.
  eauto.
Qed.

Fixpoint remove_nth {A} (n : nat) (al : list A) {struct n} : list A :=
  match n, al with
  | O, a :: al => al
  | S n', a :: al' => a :: remove_nth n' al'
  | _, nil => nil
  end.

Lemma extract_nth_ext_prop : forall n a_mem a_ext (S : Prop),
  nth n a_ext (ExtPred.prop True) = (ExtPred.prop S) ->
  MEM a_mem (EXT a_ext) =
    (fun st => S /\ MEM a_mem (EXT (remove_nth n a_ext)) st).
Proof.
  intros.
  transitivity (MEM a_mem (fun es => S /\ EXT (remove_nth n a_ext) es)).
  - f_equal.
    generalize dependent n; induction a_ext; intros.
    + extensionality es.
      apply prop_ext.
      split; only 2 : hauto lq: on.
      intros _.
      replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H. 2 : {
        destruct n; auto.
      }
      split. 2 : {
        (* hammer should solve here *)
        destruct n; simpl; apply I.
      }
      assert (ExtPred.prop S es). {
        rewrite <- H.
        simpl. auto.
      }
      apply H0.
    + destruct n.
      * simpl in H. rewrite H.
        clear.
        reflexivity.
      * specialize (IHa_ext _ H).
        change (EXT (a :: a_ext)) with (fun es => a es /\ EXT a_ext es).
        rewrite IHa_ext.
        clear.
        extensionality es.
        apply prop_ext.
        simpl. fcrush.
  - clear.
    extensionality st.
    apply prop_ext.
    destruct st.
    sauto.
Qed.

End ExtExtract.
