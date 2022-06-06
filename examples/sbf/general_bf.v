Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Program.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.ConFilter.

Section BLOOM_FILTER.

  (* Number of hashes *)
  Definition Index := Z.

  Definition HashFunc := Z -> Index.

  Definition add_hash {num_slots} (z: Z) (h: HashFunc) (F: row num_slots) :=
    row_insert F (h z).

  Definition map_hashes {num_rows} z (hashes: listn HashFunc num_rows) :=
    map_listn (fun hash => hash z) hashes.

  Definition add {num_rows num_slots} (hashes: listn HashFunc num_rows)
    (fs: frame num_rows num_slots) (z: Z) : frame num_rows num_slots :=
    frame_insert fs (map_hashes z hashes).

  Definition addm {num_rows num_slots} (hashes: listn HashFunc num_rows)
    (fs: frame num_rows num_slots) (zs: list Z) :=
    List.fold_left (add hashes) zs fs.

  Definition query {num_rows num_slots} (hashes: list HashFunc)
    (fs: frame num_rows num_slots) (z: Z): bool :=
    frame_query fs (map (fun hash => hash z) hashes).

  Definition hash_in_range (num_slots: Z) (h: HashFunc): Prop :=
    forall x, 0 <= h x < num_slots.

  Lemma add_comm {num_rows num_slots} x y (fs: frame num_rows num_slots)
    (hashes: listn HashFunc num_rows):
    add hashes (add hashes fs x) y = add hashes (add hashes fs y) x.
  Proof.
    destruct fs as [fs ?H]. destruct hashes as [hashes ?H].
    revert fs hashes num_rows H H0. induction fs; intros; simpl; destruct hashes.
    - unfold add, frame_insert. simpl. apply subset_eq_compat. auto.
    - exfalso. list_solve.
    - exfalso. list_solve.
    - unfold add, frame_insert. simpl. apply subset_eq_compat. rewrite !map2_cons. f_equal.
      + apply row_insert_comm.
      + assert (Zlength fs = num_rows - 1) by list_solve.
        assert (Zlength hashes = num_rows - 1) by list_solve.
        specialize (IHfs hashes (num_rows - 1) H1 H2).
        unfold add, frame_insert in IHfs. simpl in IHfs.
        apply EqdepFacts.eq_sig_fst in IHfs. apply IHfs.
  Qed.

  Lemma bf_add_query_true:
    forall {num_rows num_slots} (fs: frame num_rows num_slots) (hashes: listn HashFunc num_rows) z,
      Forall (hash_in_range num_slots) (`hashes) ->
      query (`hashes) (add hashes fs z) z = true.
  Proof.
    intros. destruct fs as [fs ?H]. destruct hashes as [hashes ?H]. simpl in *.
    revert fs hashes num_rows H0 H1 H.
    induction fs; intros; simpl; destruct hashes.
    - now simpl.
    - exfalso. list_solve.
    - exfalso. list_solve.
    - inversion H. subst x l.
      assert (Zlength fs = num_rows - 1) by list_solve.
      assert (Zlength hashes = num_rows - 1) by list_solve.
      specialize (IHfs hashes (num_rows - 1) H2 H3 H5).
      unfold query, add, frame_insert, frame_query in *. simpl in *.
      rewrite !map2_cons. rewrite fold_andb_cons. rewrite row_query_insert_true. 2: apply H4.
      simpl. apply IHfs.
  Qed.

  Lemma addm_add_comm : forall {num_rows num_slots} x ys (fs: frame num_rows num_slots)
                          (hashes: listn HashFunc num_rows),
      addm hashes (add hashes fs x) ys = add hashes (addm hashes fs ys) x.
  Proof.
    intros. revert ys fs hashes x.
    induction ys; intros.
    - simpl; auto.
    - simpl. rewrite !IHys. rewrite add_comm; auto.
  Qed.

  Theorem BFNoFalseNegative: forall {num_rows num_slots} z zs (fs: frame num_rows num_slots)
                               (hashes: listn HashFunc num_rows),
      Forall (hash_in_range num_slots) (`hashes) ->
      query (`hashes) (addm hashes (add hashes fs z) zs) z  = true.
  Proof.
    intros. rewrite addm_add_comm. now apply bf_add_query_true.
  Qed.

End BLOOM_FILTER.
