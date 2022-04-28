Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.ConFilter.

Section BLOOM_FILTER.

  (* Number of hashes *)
  Definition Index := Z.

  Definition index_eqb: Index -> Index -> bool := Z.eqb.

  Lemma index_refl: forall i, index_eqb i i = true.
  Proof. apply Z.eqb_refl. Qed.

  Definition HashFunc := Z -> Index.

  Definition add_hash (z: Z) (h: HashFunc) (F: row) :=
    row_insert F (h z).

  Definition add (hashes: list HashFunc) (fs: frame) (z: Z) : frame :=
    frame_insert fs (map (fun hash => hash z) hashes).

  Definition addm (hashes: list HashFunc) (fs: frame) (zs: list Z) :=
    List.fold_left (add hashes) zs fs.

  Definition query (hashes: list HashFunc) (fs: frame) (z: Z): bool :=
    frame_query fs (map (fun hash => hash z) hashes).

  Definition hash_row_compatible (h: HashFunc) (r: row): Prop :=
    forall x, 0 <= h x < Zlength r.

  Lemma bf_add_get_true: forall z h a,
      hash_row_compatible h a ->
      row_query (add_hash z h a) (h z) = true.
  Proof.
    unfold row_query, add_hash, row_insert. intros.
    rewrite upd_Znth_same; auto.
  Qed.

  Lemma add_hash_comm: forall x y f h,
      add_hash x h (add_hash y h f) = add_hash y h (add_hash x h f).
  Proof.
    unfold add_hash, row_insert. intros.
    list_solve.
  Qed.

  Lemma add_cons: forall h hs f fs z, add (h :: hs) (f :: fs) z = add_hash z h f :: add hs fs z.
  Proof. intros. unfold add, add_hash, frame_insert. apply map2_cons. Qed.

  Lemma add_comm x y fs hashes:
    length fs = length hashes ->
    add hashes (add hashes fs x) y = add hashes (add hashes fs y) x.
  Proof.
    intros. revert fs hashes H. induction fs; intros; simpl; destruct hashes.
    - now simpl.
    - simpl in H; inversion H.
    - simpl in H; inversion H.
    - rewrite !add_cons. rewrite add_hash_comm. f_equal.
      apply IHfs. now inversion H.
  Qed.

  Lemma query_cons: forall h hashes f fs z,
      query (h :: hashes) (f :: fs) z = (row_query f (h z) && query hashes fs z)%bool.
  Proof.
    intros. unfold query. simpl. unfold frame_query. unfold fold_andb.
    rewrite map2_cons. simpl. destruct (row_query f (h z)); simpl; auto.
    now rewrite fold_andb_false.
  Qed.

  Lemma bf_add_query_true: forall fs hashes z,
      Forall2 hash_row_compatible hashes fs ->
      query hashes (add hashes fs z) z = true.
  Proof.
    induction fs; intros; simpl; destruct hashes.
    - now simpl.
    - simpl in H; inversion H.
    - simpl in H; inversion H.
    - rewrite add_cons. rewrite query_cons. inversion H. subst. clear H.
      rewrite IHfs; auto. rewrite Bool.andb_true_r.
      apply bf_add_get_true; auto.
  Qed.

  Lemma add_length: forall hashes fs z,
      length fs = length hashes -> length (add hashes fs z) = length fs.
  Proof.
    intros. unfold add, frame_insert, map2. rewrite map_length, combine_length.
    rewrite map_length, H. rewrite Nat.min_id. easy.
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

  Lemma hash_row_compatible_add_hash:
    forall (z : Z) (x : HashFunc) (y : row),
      hash_row_compatible x y -> hash_row_compatible x (add_hash z x y).
  Proof.
    unfold hash_row_compatible. intros. unfold add_hash, row_insert.
    now rewrite Zlength_upd_Znth.
  Qed.

  Lemma hash_row_compatible_add: forall hashes fs z,
      Forall2 hash_row_compatible hashes fs ->
      Forall2 hash_row_compatible hashes (add hashes fs z).
  Proof.
    intros. induction H.
    - unfold add, frame_insert, map2. simpl. constructor.
    - rewrite add_cons. constructor; auto. now apply hash_row_compatible_add_hash.
  Qed.

  Lemma hash_row_compatible_addm:
    forall (zs : list Z) (fs : list row) (hashes : list HashFunc),
      Forall2 hash_row_compatible hashes fs ->
      Forall2 hash_row_compatible hashes (addm hashes fs zs).
  Proof.
    induction zs; intros; simpl; auto.
    apply IHzs. now apply hash_row_compatible_add.
  Qed.

  Theorem BFNoFalseNegative: forall z zs fs hashes,
      Forall2 hash_row_compatible hashes fs ->
      query hashes (addm hashes (add hashes fs z) zs) z  = true.
  Proof.
    intros. pose proof (Forall2_length H). rewrite addm_add_comm; auto.
    apply bf_add_query_true. now apply hash_row_compatible_addm.
  Qed.

End BLOOM_FILTER.
