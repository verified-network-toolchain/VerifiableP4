Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProD3.examples.sbf.Utils.

Section BLOOM_FILTER.

  (* Number of hashes *)
  Context {Index: Type}.

  Parameter index_eqb: Index -> Index -> bool.

  Parameter index_refl: forall i, index_eqb i i = true.

  Definition HashFunc := Z -> Index.

  Definition Filter := Index -> bool.

  Definition upd (F: Filter) (i:Index) (b:bool): Filter :=
    fun j => if index_eqb i j then b else F j.

  Definition get (F: Filter) (i: Index): bool := F i.

  Definition add_hash (z: Z) (h: HashFunc) (F: Filter) := upd F (h z) true.

  Definition add (hashes: list HashFunc) (fs: list Filter) (z: Z) : list Filter :=
    map2 (add_hash z) hashes fs.

  Definition addm (hashes: list HashFunc) (fs: list Filter) (zs: list Z) :=
    List.fold_left (add hashes) zs fs.

  Definition query (hashes: list HashFunc) (fs: list Filter) (z: Z): bool :=
    List.fold_left andb (map2 (fun h f => get f (h z)) hashes fs) true.

  Lemma bf_add_get_true: forall z h a, get (add_hash z h a) (h z) = true.
  Proof.
    unfold get, add_hash. intros. unfold upd. rewrite index_refl. easy.
  Qed.

  Lemma add_hash_comm: forall x y f h,
      add_hash x h (add_hash y h f) = add_hash y h (add_hash x h f).
  Proof.
    unfold add_hash, upd. intros.
    apply functional_extensionality. intros z.
    destruct (index_eqb (h x) z);
    destruct (index_eqb (h y) z); auto.
  Qed.

  Lemma add_comm x y fs hashes:
    length fs = length hashes -> add hashes (add hashes fs x) y = add hashes (add hashes fs y) x.
  Proof.
    intros. revert fs hashes H. induction fs; intros; simpl; unfold add; destruct hashes.
    - unfold map2. now simpl.
    - simpl in H; inversion H.
    - simpl in H; inversion H.
    - rewrite !map2_cons. rewrite add_hash_comm. f_equal.
      unfold add in IHfs. apply IHfs. now inversion H.
  Qed.

  Lemma bf_add_query_true: forall fs hashes z,
      length fs = length hashes -> query hashes (add hashes fs z) z = true.
  Proof.
    induction fs; intros; simpl; unfold add, query; destruct hashes.
    - now simpl.
    - simpl in H; inversion H.
    - simpl in H; inversion H.
    - rewrite !map2_cons. simpl in H. inversion H. clear H.
      specialize (IHfs _ z H1). unfold add, query in IHfs.
      rewrite bf_add_get_true. simpl fold_left. apply IHfs.
  Qed.

  Lemma add_cons: forall h hs f fs z, add (h :: hs) (f :: fs) z = add_hash z h f :: add hs fs z.
  Proof. intros. unfold add. apply map2_cons. Qed.

  Lemma add_length: forall hashes fs z,
      length fs = length hashes -> length (add hashes fs z) = length fs.
  Proof.
    intros. unfold add, map2. rewrite map_length. rewrite combine_length.
    rewrite H. rewrite Nat.min_id. easy.
  Qed.

  Lemma addm_length: forall hashes fs zs,
      length fs = length hashes -> length (addm hashes fs zs) = length fs.
  Proof.
    intros. revert fs H. unfold addm. induction zs; simpl; auto.
    intros. rewrite IHzs; [| rewrite <- H]; now apply add_length.
  Qed.

  Lemma addm_add_comm : forall x ys fs hashes,
      length fs = length hashes ->
      addm hashes (add hashes fs x) ys = add hashes (addm hashes fs ys) x.
  Proof.
    intros. revert ys fs hashes x H.
    induction ys; intros.
    - simpl; auto.
    - simpl. assert (forall z, length (add hashes fs z) = length hashes). {
        intros. rewrite add_length; auto. }
      rewrite !IHys; auto. rewrite add_comm; auto.
      rewrite addm_length; auto.
  Qed.

  Theorem BFNoFalseNegative: forall z zs fs hashes,
      length fs = length hashes ->
      query hashes (addm hashes (add hashes fs z) zs) z  = true.
  Proof.
    intros. rewrite addm_add_comm; auto. apply bf_add_query_true.
    rewrite addm_length; auto.
  Qed.

End BLOOM_FILTER.
