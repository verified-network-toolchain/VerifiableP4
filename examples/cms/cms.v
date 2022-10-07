Require Import Coq.Classes.EquivDec.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Import ListNotations.

Generalizable All Variables.

Open Scope Z_scope.
Open Scope list_scope.

Class Map (K V: Type) {KEq: EqDec K eq} : Type := {
    map_carrier: Type;
    empty: map_carrier;
    lookup: K -> map_carrier -> option V;
    insert: K -> V -> map_carrier -> map_carrier;

    lookup_empty: forall k, lookup k empty = None;
    lookup_insert_spec: forall k1 k2 v m,
      lookup k1 (insert k2 v m) = if equiv_dec k1 k2 then Some v else lookup k1 m;
  }.

Section DerivedProp.
  Context `{M: Map K V}.

  Lemma lookup_insert_same: forall k v m, lookup k (insert k v m) = Some v.
  Proof.
    intros. rewrite lookup_insert_spec. destruct (k == k); auto.
    exfalso. apply c. reflexivity.
  Qed.

  Lemma lookup_insert_diff: forall k1 k2 v m, k1 <> k2 -> lookup k1 (insert k2 v m) = lookup k1 m.
  Proof.
    intros. rewrite lookup_insert_spec. destruct (k1 == k2); auto.
    exfalso. apply H. inversion e. reflexivity.
  Qed.

End DerivedProp.

(* Set Printing All.
About lookup_insert_diff. *)
(* 
Section Z2Map.

  Definition z2map: Type := (Z * Z) -> option Z.

  #[export] Instance zeqdec: EqDec Z eq.
  Proof. red (* unfold EqDec *); unfold equiv, complement; apply Z.eq_dec. Defined.

  #[export] Instance z2eqdec: EqDec (Z * Z) eq.
  Proof. eapply prod_eqdec; apply zeqdec. Defined.

  Definition z2empty: z2map := fun _ => None.

  Definition z2lookup (k: Z * Z) (m: z2map) := m k.

  Definition z2insert (k: Z * Z) (v: Z) (m: z2map) :=
    fun x => if equiv_dec x k then Some v else m x.

  Lemma z2lookup_empty: forall k : Z * Z, z2lookup k z2empty = None.
  Proof. intros. unfold z2lookup, z2empty. reflexivity. Qed.

  Lemma z2insert_spec: forall k1 k2 v m,
      z2lookup k1 (z2insert k2 v m) = if equiv_dec k1 k2 then Some v else z2lookup k1 m.
  Proof. intros. unfold z2lookup, z2insert. reflexivity.  Qed.

  #[export] Instance z2mapIns: Map (Z * Z) Z :=
    Build_Map _ _ z2eqdec z2map z2empty z2lookup z2insert z2lookup_empty z2insert_spec.

End Z2Map. *)

Section CMS.
  
  Context `{M: Map (nat * Z) Z}.

  Variable Key: Type.
  Variable num_rows: nat.
  Hypothesis num_rows_pos: (num_rows > 0)%nat.
  Variable hash: nat -> Key -> Z.

  Definition gen_indexes (k: Key) : list (nat * Z) :=
    map (fun idx => (idx, hash idx k)) (seq 0 num_rows).  

  Lemma gen_indexes_length : forall k,
    length (gen_indexes k) = num_rows.
  Proof.
    intros. unfold gen_indexes. rewrite map_length. apply seq_length.
  Qed.

  Definition z2lookup_default (k: nat * Z) (m: map_carrier) := 
    match lookup k m with
    | None => 0
    | Some v => v
    end.

  Lemma lookup_insert_diff_default: forall k1 k2 v m,
   k1 <> k2 -> z2lookup_default k1 (insert k2 v m) = z2lookup_default k1 m. 
  Proof.
    intros.
    unfold z2lookup_default.
    rewrite lookup_insert_diff; auto.
  Qed.
  
  Lemma lookup_insert_same_default: forall k v m,
   z2lookup_default k (insert k v m) = v. 
  Proof.
    intros.
    unfold z2lookup_default.
    rewrite lookup_insert_same; auto.
  Qed.

  Definition cms_insert (k: Key) (m: map_carrier) : map_carrier := 
    List.fold_left 
      (fun agg idx => insert idx ((z2lookup_default idx agg) + 1) agg)
      (gen_indexes k) m.

  Definition get_hd {A: Type} (l: list A) (H: (length l > 0)%nat): A.
  Proof.
    refine (( 
    match l as k return ((length k > 0)%nat -> A) with
    | nil => fun s => _
    | a :: _ => fun _ => a
    end) H).
    simpl in s. exfalso. apply (gt_irrefl 0). assumption. 
    (* simpl in s. apply gt_irrefl in s. exfalso. assumption. *)
    (* trick: define a commplex lemma and then apply to shorten 
              the definition printed out. *)
  Defined. 

(*  
  Dependent type programming.
  Print get_hd => gives us the definition to replace the above with.
  Lemma test: (length (1::2::3::nil) > 0)%nat.
  Proof. vm_compute. auto. Qed.  
  Compute (get_hd (1::2::3::nil) test). *)

  Definition get_min (l: list Z) (H: (length l > 0)%nat): Z := 
    List.fold_left Z.min l (get_hd l H).

  Lemma fold_left_min_hd: forall l a,
     fold_left Z.min l a <= a.
  Proof. 
    induction l; intros; simpl.
    - lia.
    - transitivity (Z.min a0 a); auto. lia.
  Qed.

  Lemma fold_left_min_tail: forall l a v,
    In v l -> fold_left Z.min l a <= v.
  Proof.
    induction l; intros.
    - inversion H.
    - simpl in *. destruct H.
      + subst v. transitivity (Z.min a0 a); try lia.
        apply fold_left_min_hd.
      + apply IHl; auto. 
  Qed.

  (*  H(type) depends on l(term) *)
  Lemma get_min_spec_ineq: forall l v H, In v l -> get_min l H <= v.
  Proof.
    intros. unfold get_min. apply fold_left_min_tail; auto.
  Qed.
  
  Lemma fold_left_min_in: forall l a,
     fold_left Z.min l a = a \/ In (fold_left Z.min l a) l.
  Proof. 
    induction l; intros; simpl.
    - left; auto.
    - destruct (IHl (Z.min a0 a)); auto.
      rewrite H. destruct (Zmin_spec a0 a) as [[] | []]; auto.
  Qed.

  Lemma get_min_spec_in: forall l H, In (get_min l H) l.
  Proof.
    intros. unfold get_min.
    destruct (fold_left_min_in l (get_hd l H)); auto.
    rewrite H0. clear H0. destruct l.
    - simpl in H. lia.
    - unfold get_hd. now left.
  Qed.

  Lemma cms_lookup_helper m k: 
  (length (map (fun idx : nat * Z => z2lookup_default idx m) (gen_indexes k)) >
 0)%nat.
  Proof.
    rewrite map_length, gen_indexes_length. assumption.
  Qed.

  Definition cms_lookup (k: Key) (m: map_carrier) : Z :=
    get_min (List.map (fun idx => z2lookup_default idx m) (gen_indexes k)) (cms_lookup_helper m k).

  Definition cms_empty : map_carrier := empty.

  Lemma get_min_all_zero: forall {A} (f: A -> Z) l H,
    (forall a, f a = 0) -> get_min (map f l) H = 0.
  Proof.
    intros.
    pose proof (get_min_spec_in (map f l) H).
    assert (forall x, In x (map f l) -> x = 0). {
      clear -H0. intros. induction l; simpl in *. 1: inversion H.
      rewrite H0 in H. destruct H; auto.
    }
    apply H2 in H1. assumption.
  Qed.  
  
  Lemma cms_lookup_empty: forall k : Key, cms_lookup k cms_empty = 0.
    Proof. intros. unfold cms_lookup, z2lookup_default, cms_empty.
    apply get_min_all_zero.
    intros. rewrite lookup_empty. reflexivity. Qed.

  Lemma lookup_insert_diff_0: forall k1 k2 m,
    Hash0 k1 <> Hash0 k2 ->
    z2lookup_default (0, Hash0 k1) (cms_insert k2 m) = 
    z2lookup_default (0, Hash0 k1) m.
  Proof.
    intros. unfold cms_insert. 
    rewrite !lookup_insert_diff_default; [|intro Hs; inversion Hs..];[|contradiction].
    auto.
  Qed.

  Lemma lookup_insert_diff_1: forall k1 k2 m,
    Hash1 k1 <> Hash1 k2 ->
    z2lookup_default (1, Hash1 k1) (cms_insert k2 m) = 
    z2lookup_default (1, Hash1 k1) m.
  Proof.
    intros. unfold cms_insert. 
    rewrite !lookup_insert_diff_default; [|intro Hs; inversion Hs..];[|contradiction].
    auto.
  Qed.

  Lemma lookup_insert_diff_2: forall k1 k2 m,
    Hash2 k1 <> Hash2 k2 ->
    z2lookup_default (2, Hash2 k1) (cms_insert k2 m) = 
    z2lookup_default (2, Hash2 k1) m.
  Proof.
    intros. unfold cms_insert. 
    rewrite !lookup_insert_diff_default; [|intro Hs; inversion Hs..];[|contradiction].
    auto.
  Qed.

  Lemma lookup_insert_same_0: forall k1 k2 m,
    Hash0 k1 = Hash0 k2 ->
    z2lookup_default (0, Hash0 k1) (cms_insert k2 m) = 
    z2lookup_default (0, Hash0 k1) m + 1.
  Proof.
    intros. unfold cms_insert. 
    rewrite 2 lookup_insert_diff_default; [|intro Hs; inversion Hs..].
    rewrite H. rewrite lookup_insert_same_default.
    auto.
  Qed.

  Lemma lookup_insert_same_1: forall k1 k2 m,
    Hash1 k1 = Hash1 k2 ->
    z2lookup_default (1, Hash1 k1) (cms_insert k2 m) = 
    z2lookup_default (1, Hash1 k1) m + 1.
  Proof.
    intros. unfold cms_insert. 
    rewrite lookup_insert_diff_default; [|intro Hs; inversion Hs..].
    rewrite H. rewrite lookup_insert_same_default.
    rewrite lookup_insert_diff_default; [|intro Hs; inversion Hs..].
    auto.
  Qed.

  Lemma lookup_insert_same_2: forall k1 k2 m,
    Hash2 k1 = Hash2 k2 ->
    z2lookup_default (2, Hash2 k1) (cms_insert k2 m) = 
    z2lookup_default (2, Hash2 k1) m + 1.
  Proof.
    intros. unfold cms_insert. 
    rewrite H. rewrite lookup_insert_same_default.
    rewrite 2 lookup_insert_diff_default; [|intro Hs; inversion Hs..].
    auto.
  Qed.

  Lemma lookup_insert_0: forall k m,
    z2lookup_default (0, Hash0 k) (cms_insert k m) = z2lookup_default (0, Hash0 k) m + 1.
  Proof.
    intros. apply lookup_insert_same_0. (* debug *) auto.
  Qed.    

  Lemma lookup_insert_1: forall k m,
    z2lookup_default (1, Hash1 k) (cms_insert k m) = z2lookup_default (1, Hash1 k) m + 1.
  Proof.
    intros. apply lookup_insert_same_1. auto.
  Qed.    
  
  Lemma lookup_insert_2: forall k m,
    z2lookup_default (2, Hash2 k) (cms_insert k m) = z2lookup_default (2, Hash2 k) m + 1.
  Proof.
    intros. apply lookup_insert_same_2. auto.
  Qed.

  Lemma fold_left_Zmin_add: forall l a i, 
    fold_left Z.min (map (fun x => Z.add x a) l) (i + a) =
    fold_left Z.min l i + a.
  Proof.  
    induction l; intros b i; simpl; auto.
    rewrite Z.add_min_distr_r. apply IHl.
  Qed. 

  Lemma cms_lookup_insert: forall k m, cms_lookup k (cms_insert k m) = cms_lookup k m + 1.
  Proof. intros. unfold cms_lookup.
    rewrite lookup_insert_0, lookup_insert_1, lookup_insert_2.
    remember (z2lookup_default (0, Hash0 k) m) as z0.
    remember (z2lookup_default (1, Hash1 k) m) as z1.
    remember (z2lookup_default (2, Hash2 k) m) as z2.
    rewrite <- fold_left_Zmin_add. simpl map. reflexivity.
  Qed.

  
  Lemma z2lookup_cms_insert: forall n k1 k2 m, 
    z2lookup_default (n, hash n k1) (cms_insert k2 m) =
    z2lookup_default (n, hash n k1) m \/
    z2lookup_default (n, hash n k1) (cms_insert k2 m) =
    z2lookup_default (n, hash n k1) m + 1.
  Proof.
    intros. destruct (le_lt_dec num_rows n).
    - left. unfold cms_insert. unfold gen_indexes. clear num_rows_pos.
      induction num_rows.
      + simpl. reflexivity.
      + assert (map (fun idx : nat => (idx, hash idx k2)) (seq 0 (S n0)) = 
          (map (fun idx : nat => (idx, hash idx k2)) (seq 0 n0)) ++ [(n0, hash n0 k2)]). {
            replace (S n0) with (n0 + 1)%nat by lia.
            rewrite seq_app, map_app. f_equal. }
        rewrite H. rewrite fold_left_app.
        remember (fold_left
            (fun (agg : map_carrier) (idx : nat * Z) =>
             insert idx (z2lookup_default idx agg + 1) agg)
            (map (fun idx : nat => (idx, hash idx k2)) (seq 0 n0)) m).
            simpl.
  Qed.
  Lemma cms_lookup_insert_diff: forall k1 k2 m, 
      cms_lookup k2 (cms_insert k1 m) = cms_lookup k2 m \/ 
      cms_lookup k2 (cms_insert k1 m) = cms_lookup k2 m + 1.
  Proof.
    intros.
    unfold cms_lookup.

    destruct ((Hash0 k1 =? Hash0 k2)) eqn:Hh0;
    destruct (Z.eqb (Hash1 k1) (Hash1 k2)) eqn:Hh1;
    destruct (Z.eqb (Hash2 k1) (Hash2 k2)) eqn:Hh2.
    - rewrite Z.eqb_eq in *.
      right.
      unfold cms_lookup.
      rewrite <- Hh0.
      rewrite <- Hh1.
      rewrite <- Hh2.
      rewrite lookup_insert_0, lookup_insert_1, lookup_insert_2.
      rewrite <- fold_left_Zmin_add. reflexivity.
    - rewrite Z.eqb_eq in *.
      right.
      unfold cms_lookup.
      rewrite <- Hh0.
      rewrite <- Hh1.
      rewrite lookup_insert_0, lookup_insert_1.
      rewrite lookup_insert_diff_2.
      


    2: { left. unfold cms_lookup.
    apply Z.eqb_eq in Hh0.
    rewrite <- Hh0.

    lookup
    rewrite lookup_insert0, lookup_insert1, lookup_insert2.
    remember (z2lookup_default (0, Hash0 k) m) as z0.
    remember (z2lookup_default (1, Hash1 k) m) as z1.
    remember (z2lookup_default (2, Hash2 k) m) as z2.


    }


  Admitted.

  Lemma cms_insert_comm: forall k1 k2 m, 
      cms_insert k1 (cms_insert k2 m) = cms_insert k2 (cms_insert k1 m).
  Proof.
    intros.
    apply functional_extensionality.
    

End CMS.