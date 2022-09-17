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

Lemma extract_nth_ext_ex_ext_implies_pre : forall n a_ext post A (S : A -> ext_pred) ep H,
  nth n a_ext (ExtPred.prop True) = (ExtPred.ex S ep H) ->
  (forall x, ext_implies (replace_nth n a_ext (S x)) post) ->
  ext_implies a_ext post.
Proof.
  intros.
  unfold ext_implies in *.
  change ext_denote with EXT in *.
  erewrite extract_nth_ext_ex with (a_ext := a_ext) by eauto.
  intros.
  destruct H2.
  eauto.
Qed.

Lemma extract_nth_ext_ex_ext_implies_post : forall n pre a_ext A (S : A -> ext_pred) ep H,
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

Lemma extract_nth_ext_prop : forall n a_ext (S : Prop),
  nth n a_ext (ExtPred.prop True) = (ExtPred.prop S) ->
  ext_assertion_equiv a_ext (ExtPred.prop S :: remove_nth n a_ext).
Proof.
  intros.
  generalize dependent n; induction a_ext; intros.
  + replace (nth n [] (ExtPred.prop True)) with (ExtPred.prop True) in H. 2 : {
      destruct n; auto.
    }
    rewrite <- H.
    hnf.
    extensionality es.
    apply prop_ext.
    cbn. (* sauto lq: on. *)
    replace (remove_nth n []) with (@nil ext_pred). 2 : {
      destruct n; auto.
    }
    split; auto.
  + destruct n.
    * simpl in H. rewrite H.
      clear.
      reflexivity.
    * specialize (IHa_ext _ H).
      unfold ext_assertion_equiv in *.
      cbn.
      change (ext_denote (a :: a_ext)) with (fun es => a es /\ ext_denote a_ext es).
      rewrite IHa_ext.
      clear.
      extensionality es.
      apply prop_ext.
      fcrush.
Qed.

Lemma ext_implies_pre_prop : forall (P : Prop) pre_ext post_ext,
  (P -> ext_implies pre_ext post_ext) ->
  ext_implies (ExtPred.prop P :: pre_ext) post_ext.
Proof.
  unfold ext_implies.
  intros.
  destruct H0.
  eauto.
Qed.

Lemma hoare_block_pre_ext_prop : forall ge p (P : Prop) pre_mem pre_ext stmt post,
  (P -> hoare_block ge p (MEM pre_mem (EXT pre_ext)) stmt post) ->
  hoare_block ge p (MEM pre_mem (EXT (ExtPred.prop P :: pre_ext))) stmt post.
Proof.
  unfold hoare_block; intros.
  destruct st.
  destruct H0, H2.
  eapply H; try eassumption.
  split; eassumption.
Qed.

Lemma hoare_func_pre_ext_prop : forall ge p (P : Prop) pre_arg pre_mem pre_ext func targs post,
  (P -> hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT pre_ext))) func targs post) ->
  hoare_func ge p (ARG pre_arg (MEM pre_mem (EXT (ExtPred.prop P :: pre_ext)))) func targs post.
Proof.
  unfold hoare_func; intros.
  destruct st.
  destruct H0, H2, H3.
  eapply H; try eassumption.
  split; only 2 : split; eassumption.
Qed.

Lemma hoare_block_assert_Prop : forall ge p pre_mem pre_ext stmt post P,
  ext_implies pre_ext [ExtPred.prop P] ->
  (P -> hoare_block ge p (MEM pre_mem (EXT pre_ext)) stmt post) ->
  hoare_block ge p (MEM pre_mem (EXT pre_ext)) stmt post.
Proof.
  unfold hoare_block; intros.
  assert P. {
    destruct st as [m es].
    destruct H1.
    specialize (H es ltac:(eauto)).
    exact (proj1 H).
  }
  eauto.
Qed.

Lemma ext_implies_assert_Prop : forall pre_ext post_ext P,
  ext_implies pre_ext [ExtPred.prop P] ->
  (P -> ext_implies pre_ext post_ext) ->
  ext_implies pre_ext post_ext.
Proof.
  unfold ext_implies; intros.
  assert P. {
    specialize (H es ltac:(eauto)).
    exact (proj1 H).
  }
  eauto.
Qed.

End ExtExtract.
