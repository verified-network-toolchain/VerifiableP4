Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.
Require Import Poulet4.Utils.Utils.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.core.Coqlib.
Require Import Poulet4.P4light.Syntax.SyntaxUtil.
Require Import Hammer.Plugin.Hammer.

Definition val_sim {A B : Type} (v : @ValueBase A) (v' : @ValueBase B) : Prop :=
  exec_val (fun _ _ => True) v v'.

Section SvalRefine.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).

(* bit_refine : option bool -> option bool -> Prop
  We treat (option bool) as a set where None means an arbitrary Boolean.
  bit_refine a b means a includes b. *)
Inductive bit_refine : option bool -> option bool -> Prop :=
  | read_none : forall ob, bit_refine None ob
  | read_some : forall b, bit_refine (Some b) (Some b).

(* sval_refine : Sval -> Sval -> Prop
  Similarly, we treat Sval as a set of Val's where None means an arbitrary bit.
  sval_refine a b means a includes b. *)
Definition sval_refine := exec_val bit_refine.

(* In order to handle sval_refine, we prove some generic lemmas about exec_val,
  including exec_val_refl, exec_val_sym, exec_val_trans. *)

(* exec_val_refl : forall {A} (f : A -> A -> Prop),
  (f is reflexive) -> ((exec_val f) is reflexive). *)
Section exec_val_refl.
  Context {A : Type} (f : A -> A -> Prop).
  Hypothesis H_f_refl : forall x, f x x.

  Lemma Forall2_refl : forall v,
    Forall2 f v v.
  Proof.
    induction v; intros.
    - constructor.
    - constructor; eauto.
  Qed.

  Hint Resolve Forall2_refl : core.

  Lemma exec_val_refl_case1 : forall vs,
    Forall (fun v : ValueBase => exec_val f v v) vs ->
    Forall2 (exec_val f) vs vs.
  Proof.
    induction vs; intros; inv H; constructor; auto.
  Qed.

  Lemma exec_val_refl_case2 : forall (vs : list (ident * ValueBase)),
    Forall (fun '(_, v) => exec_val f v v) vs ->
    AList.all_values (exec_val f) vs vs.
  Proof.
    induction vs; intros; inv H; constructor.
    - destruct a; auto.
    - apply IHvs; auto.
  Qed.

  Lemma exec_val_refl : forall v,
    exec_val f v v.
  Proof.
    intros v.
    induction v using custom_ValueBase_ind;
      constructor; eauto.
    - eapply exec_val_refl_case1; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case2; eauto.
    - eapply exec_val_refl_case1; eauto.
  Qed.
End exec_val_refl.

Lemma bit_refine_refl : forall b : option bool,
  bit_refine b b.
Proof.
  destruct b as [[] | ]; constructor.
Qed.

Lemma sval_refine_refl : forall sv,
  sval_refine sv sv.
Proof.
  apply exec_val_refl. exact bit_refine_refl.
Qed.

Lemma sval_refine_refl' : forall sv sv',
  sv = sv' ->
  sval_refine sv sv'.
Proof.
  intros; subst; apply sval_refine_refl.
Qed.

(* exec_val_sym : forall {A B} (f : A -> B -> Prop) (g : B -> A -> Prop),
  (f x y -> g y x) -> (exec_val f x y -> exec_val g y x).
  This is more general than standard symmetricity. *)
Section exec_val_sym.
  Context {A B : Type} (f : A -> B -> Prop) (g : B -> A -> Prop).
  Hypothesis H_rel_sym : forall a b, f a b -> g b a.

  Lemma Forall2_sym : forall v1 v2,
    Forall2 f v1 v2 ->
    Forall2 g v2 v1.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; constructor.
    - inv H; constructor; eauto.
  Qed.

  Hint Resolve Forall2_sym : core.

  Lemma exec_val_sym_case1 : forall vs1 vs2,
    Forall
      (fun v2 : ValueBase =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v1) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs2 vs1.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_sym_case2 : forall (vs1 : list (ident * ValueBase)) vs2,
    Forall
      (fun '(_, v2) =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v1) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs2 vs1.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor.
    - destruct H4; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  Lemma exec_val_sym : forall v1 v2,
    exec_val f v1 v2 ->
    exec_val g v2 v1.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f;
      inv H_f;
      constructor; eauto.
    - eapply exec_val_sym_case1; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case2; eauto.
    - eapply exec_val_sym_case1; eauto.
  Qed.
End exec_val_sym.

Definition rel_trans {A B C} (f : A -> B -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop) :=
  forall a b c,
    f a b ->
    g b c ->
    h a c.

(* exec_val_trans : forall {A B C} f g h,
  rel_trans f g h -> rel_trans (exec_val f) (exec_val g) (exec_val h)
  This is more general than standard transitivity. *)
Section exec_val_trans.
  Context {A B C : Type} (f : A -> B -> Prop) (g : B -> C -> Prop) (h : A -> C -> Prop).
  Hypothesis H_rel_trans : rel_trans f g h.

  Lemma Forall2_trans : forall v1 v2 v3,
    Forall2 f v1 v2 ->
    Forall2 g v2 v3 ->
    Forall2 h v1 v3.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; inv H0; constructor.
    - inv H; inv H0; constructor; eauto.
  Qed.

  Hint Resolve Forall2_trans : core.

  Lemma exec_val_trans_case1 : forall vs1 vs2 vs3,
    Forall
      (fun v2 : ValueBase =>
        forall v1 v3 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v3 -> exec_val h v1 v3) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs2 vs3 ->
    Forall2 (exec_val h) vs1 vs3.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H1; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_trans_case2 : forall (vs1 : list (ident * ValueBase)) vs2 vs3,
    Forall
      (fun '(_, v2) =>
        forall v1 v3 : ValueBase, exec_val f v1 v2 -> exec_val g v2 v3 -> exec_val h v1 v3) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs2 vs3 ->
    AList.all_values (exec_val h) vs1 vs3.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H1; inv H0; inv H; constructor.
    - destruct H4; destruct H5; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  (* rel_trans (exec_val f) (exec_val g) (exec_val h) *)
  Lemma exec_val_trans : forall v1 v2 v3,
    exec_val f v1 v2 ->
    exec_val g v2 v3 ->
    exec_val h v1 v3.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f H_g;
      inv H_f; inv H_g;
      constructor; eauto.
    - eapply exec_val_trans_case1; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case2; eauto.
    - eapply exec_val_trans_case1; eauto.
  Qed.
End exec_val_trans.

Lemma bit_refine_trans : forall b1 b2 b3 : option bool,
  bit_refine b1 b2 ->
  bit_refine b2 b3 ->
  bit_refine b1 b3.
Proof.
  intros.
  inv H; inv H0; constructor.
Qed.

Lemma sval_refine_trans : forall sv1 sv2 sv3,
  sval_refine sv1 sv2 ->
  sval_refine sv2 sv3 ->
  sval_refine sv1 sv3.
Proof.
  apply exec_val_trans. exact bit_refine_trans.
Qed.

(* exec_val_eq : forall {A}
  exec_val eq x y -> x = y *)
Section exec_val_eq.
  Context {A : Type}.

  Hint Resolve -> ForallMap.Forall2_eq : core.

  Lemma exec_val_eq_case1 : forall vs1 vs2,
    Forall
      (fun v2 : ValueBase => forall v1 : ValueBase, exec_val eq v1 v2 -> v1 = v2) vs2 ->
    Forall2 (exec_val (A := A) eq) vs1 vs2 ->
    vs1 = vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; f_equal; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_eq_case2 : forall (vs1 : list (ident * ValueBase)) vs2,
    Forall
      (fun '(_, v2) => forall v1 : ValueBase, exec_val eq v1 v2 -> v1 = v2) vs2 ->
    AList.all_values (exec_val (A := A) eq) vs1 vs2 ->
    vs1 = vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; f_equal.
    - destruct H4. destruct x; destruct a; f_equal.
      + auto.
      + apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  Lemma exec_val_eq : forall v1 v2,
    exec_val (A := A) eq v1 v2 ->
    v1 = v2.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_eq;
      inv H_eq;
      f_equal; eauto.
    - eapply exec_val_eq_case1; eauto.
    - eapply exec_val_eq_case2; eauto.
    - eapply exec_val_eq_case2; eauto.
    - eapply exec_val_eq_case2; eauto.
    - eapply exec_val_eq_case1; eauto.
  Qed.
End exec_val_eq.

(* exec_val_impl : forall {A B} (f g : A -> B -> Prop),
  (f implies g) -> ((exec_val f) implies (exec_val g)) *)
Section exec_val_impl.
  Context {A B : Type} (f : A -> B -> Prop) (g : A -> B -> Prop).
  Hypothesis H_rel_impl : forall a b, f a b -> g a b.

  Lemma Forall2_impl : forall v1 v2,
    Forall2 f v1 v2 ->
    Forall2 g v1 v2.
  Proof.
    intros v1 v2; revert v1.
    induction v2; intros.
    - inv H; constructor.
    - inv H; constructor; eauto.
  Qed.

  Hint Resolve Forall2_impl : core.

  Lemma exec_val_impl_case1 : forall vs1 vs2,
    Forall
      (fun v2 : ValueBase =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v1 v2) vs2 ->
    Forall2 (exec_val f) vs1 vs2 ->
    Forall2 (exec_val g) vs1 vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor; only 1 : apply H2; auto.
  Qed.

  Lemma exec_val_impl_case2 : forall (vs1 : list (ident * ValueBase)) vs2,
    Forall
      (fun '(_, v2) =>
        forall v1 : ValueBase, exec_val f v1 v2 -> exec_val g v1 v2) vs2 ->
    AList.all_values (exec_val f) vs1 vs2 ->
    AList.all_values (exec_val g) vs1 vs2.
  Proof.
    intros vs1 vs2; revert vs1.
    induction vs2; intros; inv H0; inv H; constructor.
    - destruct H4; split.
      + congruence.
      + destruct a; apply H2; auto.
    - apply IHvs2; auto.
  Qed.

  Lemma exec_val_impl : forall v1 v2,
    exec_val f v1 v2 ->
    exec_val g v1 v2.
  Proof.
    intros v1 v2; revert v1.
    induction v2 using custom_ValueBase_ind; intros * H_f;
      inv H_f;
      constructor; eauto.
    - eapply exec_val_impl_case1; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case2; eauto.
    - eapply exec_val_impl_case1; eauto.
  Qed.
End exec_val_impl.

(* We define the following functions to convert between Sval and Val. *)

(* eval_sval_to_val : Sval -> option Val
  eval_sval_to_val sv = (Some v) if all bits of sv are known.
  eval_sval_to_val sv = None if sv has unknown bits. *)
Fixpoint eval_sval_to_val (sval: Sval): option Val :=
  let sval_to_vals (sl: list Sval): option (list Val) :=
    lift_option (map eval_sval_to_val sl) in
  let sval_to_avals (sl: AList.StringAList Sval): option (AList.StringAList Val) :=
    lift_option_kv (kv_map eval_sval_to_val sl) in
  match sval with
  | ValBaseNull => Some ValBaseNull
  | ValBaseBool (Some b) => Some (ValBaseBool b)
  | ValBaseBool None => None
  | ValBaseInteger z => Some (ValBaseInteger z)
  | ValBaseBit bits => match lift_option bits with
                       | Some l => Some (ValBaseBit l)
                       | None => None
                       end
  | ValBaseInt bits => match lift_option bits with
                       | Some l => Some (ValBaseInt l)
                       | None => None
                       end
  | ValBaseVarbit n bits => match lift_option bits with
                            | Some l => Some (ValBaseVarbit n l)
                            | None => None
                            end
  | ValBaseString s => Some (ValBaseString s)
  | ValBaseTuple l => match sval_to_vals l with
                      | Some l' => Some (ValBaseTuple l')
                      | None => None
                      end
  | ValBaseError err => Some (ValBaseError err)
  | ValBaseMatchKind k => Some (ValBaseMatchKind k)
  | ValBaseStruct l => match sval_to_avals l with
                       | Some l' => Some (ValBaseStruct l')
                       | None => None
                       end
  | ValBaseHeader _ None => None
  | ValBaseHeader l (Some b) => match sval_to_avals l with
                                | Some l' => Some (ValBaseHeader l' b)
                                | None => None
                                end
  | ValBaseUnion l => match sval_to_avals l with
                      | Some l' => Some (ValBaseUnion l')
                      | None => None
                      end
  | ValBaseStack l n => match sval_to_vals l with
                          | Some l' => Some (ValBaseStack l' n)
                          | None => None
                          end
  | ValBaseEnumField s1 s2 => Some (ValBaseEnumField s1 s2)
  | ValBaseSenumField s1 s => match eval_sval_to_val s with
                                 | None => None
                                 | Some v => Some (ValBaseSenumField s1 v)
                                 end
  end.

Definition opt_to_bool : option bool -> bool :=
  force false.

(* force_sval_to_val : Sval -> Val
  force_sval_to_val replaces None (unknown) with false. *)
Fixpoint force_sval_to_val (sval: Sval): Val :=
  let sval_to_vals (sl: list Sval): list Val :=
    map force_sval_to_val sl in
  let sval_to_avals (sl: AList.StringAList Sval): AList.StringAList Val :=
    kv_map force_sval_to_val sl in
  match sval with
  | ValBaseNull => ValBaseNull
  | ValBaseBool (Some b) => ValBaseBool b
  | ValBaseBool None => ValBaseBool false
  | ValBaseInteger z => ValBaseInteger z
  | ValBaseBit bits => ValBaseBit (map opt_to_bool bits)
  | ValBaseInt bits => ValBaseInt (map opt_to_bool bits)
  | ValBaseVarbit n bits => ValBaseVarbit n (map opt_to_bool bits)
  | ValBaseString s => ValBaseString s
  | ValBaseTuple l => ValBaseTuple (sval_to_vals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (opt_to_bool valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l n => ValBaseStack (sval_to_vals l) n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s => ValBaseSenumField s1 (force_sval_to_val s)
  end.

Definition bool_to_none: bool -> option bool := fun _ => None.

Lemma map_bool_to_none: forall l,
    map bool_to_none l = repeat None (length l).
Proof.
  induction l; simpl; auto. unfold bool_to_none at 1. now rewrite IHl.
Qed.

(* val_to_liberal_sval : Val -> Sval
  val_to_liberal_sval v returns the most liberal Sval that includes v.
  That means the result only has the shape of v but all bits are unknown.
  This is used to generate results for operators on Svals. *)
Fixpoint val_to_liberal_sval (val: Val): Sval :=
  let sval_to_vals (sl: list Val): list Sval :=
    map val_to_liberal_sval sl in
  let sval_to_avals (sl: AList.StringAList Val): AList.StringAList Sval :=
    kv_map val_to_liberal_sval sl in
  match val with
  | ValBaseNull => ValBaseNull
  | ValBaseBool b => ValBaseBool None
  | ValBaseInteger z => ValBaseInteger z
  | ValBaseBit bits => ValBaseBit (map bool_to_none bits)
  | ValBaseInt bits => ValBaseInt (map bool_to_none bits)
  | ValBaseVarbit n bits => ValBaseVarbit n (map bool_to_none bits)
  | ValBaseString s => ValBaseString s
  | ValBaseTuple l => ValBaseTuple (sval_to_vals l)
  | ValBaseError err => ValBaseError err
  | ValBaseMatchKind k => ValBaseMatchKind k
  | ValBaseStruct l => ValBaseStruct (sval_to_avals l)
  | ValBaseHeader l valid => ValBaseHeader (sval_to_avals l) (bool_to_none valid)
  | ValBaseUnion l => ValBaseUnion (sval_to_avals l)
  | ValBaseStack l n => ValBaseStack (sval_to_vals l) n
  | ValBaseEnumField s1 s2 => ValBaseEnumField s1 s2
  | ValBaseSenumField s1 s => ValBaseSenumField s1 (val_to_liberal_sval s)
  end.

Lemma Forall2_ndetbit : forall l : list bool,
  Forall2 read_ndetbit (map Some l) l.
Proof.
  induction l; constructor; auto.
  constructor.
Qed.

Lemma sval_to_val_eval_p4int_sval : forall {t: P4Int.t tags_t},sval_to_val read_ndetbit (eval_p4int_sval t) (eval_p4int_val t).
Proof.
  intros. unfold eval_p4int_sval, eval_p4int_val.
  destruct (P4Int.width_signed t).
  - destruct p. destruct b; constructor; apply Forall2_ndetbit.
  - constructor.
Qed.

(* Only valid header is converted to Sval, others are all converted to all None *)
Fixpoint val_to_sval_valid_only (val: Val): Sval :=
  let val_to_svals (sl: list Val): list Sval :=
    map val_to_sval_valid_only sl in
  let val_to_asvals (sl: AList.StringAList Val): AList.StringAList Sval :=
    kv_map val_to_sval_valid_only sl in
  match val with
  | ValBaseTuple l => ValBaseTuple (val_to_svals l)
  | ValBaseStack l n => ValBaseStack (val_to_svals l) n
  | ValBaseUnion l => ValBaseUnion (val_to_asvals l)
  | ValBaseStruct l => ValBaseStruct (val_to_asvals l)
  | ValBaseHeader l true => ValBaseHeader (val_to_asvals l) (Some true)
  | ValBaseHeader l false =>
      ValBaseHeader (kv_map val_to_liberal_sval l) (Some false)
  | _ => eval_val_to_sval val
  end.

Lemma sval_refine_liberal:
  forall v1 v2, val_sim v1 v2 -> sval_refine (val_to_liberal_sval v1) v2.
Proof.
  remember (fun (sl : list Val) =>
              map val_to_liberal_sval sl
           ) as to_vals. rename Heqto_vals into Hvals.
  remember (fun (sl : AList.StringAList Val) =>
              kv_map val_to_liberal_sval sl
           ) as to_avals. rename Heqto_avals into Havals.
  induction v1 using custom_ValueBase_ind; intros;
    try (inv H; simpl; now constructor).
  - inv H. simpl. constructor. constructor.
  - inv H. simpl. constructor. induction H1; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inv H. simpl. constructor. induction H1; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inv H. simpl. constructor. induction H3; unfold bool_to_none in *;
      simpl; constructor; auto. constructor.
  - inversion H0. subst lv v2. clear H0. simpl. constructor.
    rewrite <- (equal_f Hvals). revert H lv' H2.
    induction vs; intros; inversion H2; subst lv'; clear H2;
      rewrite Hvals; constructor; inversion H; subst x0 l0; clear H.
    1: now apply H6. rewrite <- (equal_f Hvals). subst x l. apply IHvs; auto.
  - inversion H0. subst kvs v2. clear H0. simpl. constructor.
    rewrite <- (equal_f Havals). revert kvs' H2.
    induction H; intros; inversion H2; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H4. split; auto. apply H. auto.
    + rewrite <- (equal_f Havals). apply IHForall. auto.
  - inversion H0. subst kvs b0 v2. clear H0 H3. simpl. constructor.
    1: unfold bool_to_none; constructor.
    rewrite <- (equal_f Havals). revert kvs' H5.
    induction H; intros; inversion H5; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H3; split; auto. apply H. auto.
    + rewrite <- (equal_f Havals). apply IHForall; auto.
  - inversion H0. subst kvs v2. clear H0. simpl. constructor.
    rewrite <- (equal_f Havals).
    revert kvs' H2. induction H; intros; inversion H2; subst kvs'; rewrite Havals.
    1: constructor. subst x0 l0. destruct x. simpl in *. constructor.
    + simpl. destruct H4. split; auto. apply H. auto.
    + rewrite <- (equal_f Havals). apply IHForall. auto.
  - inversion H0. subst lv next v2. clear H0. simpl. constructor.
    rewrite <- (equal_f Hvals).
    revert H lv' H4. induction vs; intros; inversion H4; subst lv'; clear H4;
      rewrite Hvals; constructor; inversion H; subst x0 l0; clear H.
    1: now apply H6.  rewrite <- (equal_f Hvals). subst x l. apply IHvs; auto.
  - inversion H. subst typ_name v v2. clear H. simpl. constructor. apply IHv1. auto.
Qed.

Lemma val_sim_on_top: forall {A B: Type} (c: A -> B -> Prop) v1 v2,
    exec_val c v1 v2 -> val_sim v1 v2.
Proof. intros. eapply exec_val_impl; eauto. Qed.

Lemma eval_val_to_sval_val_sim: forall v, val_sim v (eval_val_to_sval v).
Proof. intros. apply (val_sim_on_top read_detbit). now rewrite val_to_sval_iff. Qed.

Lemma sval_refine_liberal_eval:
  forall v : Val, sval_refine (val_to_liberal_sval v) (eval_val_to_sval v).
Proof. intros. apply sval_refine_liberal. apply eval_val_to_sval_val_sim. Qed.

End SvalRefine.

(* These four lemmas: Forall2_bit_refine, sval_refine_bit_to_loptbool,
  sval_to_val_bit_to_loptbool, and val_to_sval_bit_to_lbool are not in use. *)

Lemma Forall2_bit_refine:
  forall (l : list bool) (lb' : list (option bool)),
    Forall2 bit_refine (map Some l) lb' -> lb' = map Some l.
Proof.
  induction l; intros.
  - simpl in *. inv H. auto.
  - destruct lb'.
    + simpl in H. inv H.
    + inv H. simpl. apply IHl in H5. inv H3. easy.
Qed.

Lemma sval_refine_bit_to_loptbool: forall width value sv,
    sval_refine (ValBaseBit (P4Arith.to_loptbool width value)) sv ->
    sv = (ValBaseBit (P4Arith.to_loptbool width value)).
Proof.
  intros. inv H. f_equal. unfold P4Arith.to_loptbool in *.
  now apply Forall2_bit_refine.
Qed.

Lemma sval_to_val_bit_to_loptbool: forall width value v,
    sval_to_val read_ndetbit (ValBaseBit (P4Arith.to_loptbool width value)) v ->
    v = (ValBaseBit (P4Arith.to_lbool width value)).
Proof.
  intros. symmetry. eapply sval_to_val_eval_val_to_sval_eq; eauto.
  intros. inv H0. auto.
Qed.

Lemma val_to_sval_bit_to_lbool: forall width value sv,
    val_to_sval (ValBaseBit (P4Arith.to_lbool width value)) sv ->
    sv = (ValBaseBit (P4Arith.to_loptbool width value)).
Proof. intros. rewrite val_to_sval_iff in H. simpl in H. auto. Qed.

Lemma sval_refine_sval_to_val_n_trans : forall v1 v2 v3,
  sval_refine v1 v2 ->
  sval_to_val read_ndetbit v2 v3 ->
  sval_to_val read_ndetbit v1 v3.
Proof.
  intros. eapply exec_val_trans; only 2, 3 : eassumption.
  unfold rel_trans. clear; sauto lq: on.
Qed.

Lemma sval_to_val_n_eval_val_to_sval_eq : forall v1 v2,
  sval_to_val read_ndetbit (eval_val_to_sval v1) v2 -> v2 = v1.
Proof.
  intros. apply sval_to_val_eval_val_to_sval_eq in H; auto.
  intros. now inv H0.
Qed.

Lemma svals_to_vals_n_eval_to_sval_eq: forall l1 l2,
    svals_to_vals read_ndetbit (map eval_val_to_sval l1) l2 -> l1 = l2.
Proof.
  induction l1; intros; inv H; try reflexivity.
  apply sval_to_val_n_eval_val_to_sval_eq in H2. apply IHl1 in H4. subst. easy.
Qed.

Lemma eval_sval_to_val_eq:
  forall v, eval_sval_to_val (eval_val_to_sval v) = Some v.
Proof.
  induction v using custom_ValueBase_ind; simpl; auto;
    rewrite ?lift_option_map_some; auto.
  1, 5: rewrite map_map; induction vs; simpl; auto;
  rewrite Forall_cons_iff in H; destruct H; rewrite H;
  specialize (IHvs H0); remember (lift_option _);
  destruct o; [inversion IHvs; reflexivity | discriminate].
  1 - 3: induction vs; simpl; auto; rewrite Forall_cons_iff in H; destruct H;
  destruct a; simpl; rewrite H; specialize (IHvs H0);
  remember (lift_option_kv _); destruct o;
  [inversion IHvs; reflexivity | discriminate].
  rewrite IHv. reflexivity.
Qed.

Lemma ext_val_typ_to_sval_map_eq: forall {tags_t : Type} vs,
    Forall
      (fun v : ValueBase =>
         forall (typ: @P4Type tags_t),
           ⊫ᵥ v \: typ -> is_packet_typ typ ->
           eval_val_to_sval v = val_to_sval_valid_only v) vs ->
    forallb header_is_valid vs = true ->
    forall ts,
      forallb is_packet_typ ts ->
      Forall2 (@val_typ _ tags_t) vs ts ->
      map eval_val_to_sval vs = map val_to_sval_valid_only vs.
Proof.
  intros tags_t vs. induction vs; intros; inv H2; auto. simpl. inv H.
  simpl in H0, H1. apply andb_prop in H0, H1. destruct H0, H1.
  rewrite (H4 y); [| split; assumption | assumption]. rewrite IHvs with l'; auto.
Qed.

Lemma ext_val_typ_to_sval_kv_map_eq:
  forall (tags_t : Type) (vs : list (string * ValueBase)),
    Forall
      (fun '(_, v) =>
         forall (typ: @P4Type tags_t),
           ⊫ᵥ v \: typ -> is_packet_typ typ ->
           eval_val_to_sval v = val_to_sval_valid_only v) vs ->
    forall ts,
      forallb (is_packet_typ ∘ snd) ts ->
      forallb (header_is_valid ∘ snd) vs = true ->
      AList.all_values (@val_typ _ tags_t) vs ts ->
      kv_map eval_val_to_sval vs = kv_map val_to_sval_valid_only vs.
Proof.
  intros tags_t vs. induction vs; intros; inv H2; auto.
  destruct a as [fa ta]. destruct y as [fy ty]. inv H. simpl in *.
  destruct H5. subst fy. apply andb_prop in H0, H1. destruct H0, H1.
  unfold Basics.compose in H, H0. simpl in H, H1.
  rewrite (H4 ty); [|split; assumption | assumption].
  rewrite IHvs with l'; auto.
Qed.

Lemma forallb_snd_clear_tags_eq:
  forall {tags_t : Type}
    (ts : AList.AList (P4String.t tags_t) P4Type (P4String.equiv (tags_t:=tags_t))),
    forallb ((@is_packet_typ tags_t) ∘ snd) (P4String.clear_AList_tags ts) =
      forallb (is_packet_typ ∘ snd) ts.
Proof.
  intro tgt. induction ts; simpl; [|destruct a as [x v]; rewrite IHts]; reflexivity.
Qed.

Lemma ext_val_typ_to_sval_eq: forall {tags_t: Type} v (typ: @P4Type tags_t),
    ⊫ᵥ v \: typ -> is_packet_typ typ ->
    eval_val_to_sval v = val_to_sval_valid_only v.
Proof.
  intros tags_t v. induction v using custom_ValueBase_ind; intros;
    lazymatch goal with
    | [H: ⊫ᵥ _ \: _ |- _] => destruct H as [Ht ?H]; inv Ht; try reflexivity
    end; simpl in *; try discriminate.
  - f_equal. eapply ext_val_typ_to_sval_map_eq; eauto.
  - f_equal. eapply ext_val_typ_to_sval_kv_map_eq; eauto.
    rewrite forallb_snd_clear_tags_eq. apply andb_prop in H1. destruct H1. apply H2.
  - destruct b; [| discriminate].
    f_equal. eapply ext_val_typ_to_sval_kv_map_eq; eauto.
    rewrite forallb_snd_clear_tags_eq. apply andb_prop in H1. destruct H1. apply H2.
Qed.

Lemma to_sval_typ_inv: forall {tags_t: Type} v (typ: @P4Type tags_t),
    ⊢ᵥ eval_val_to_sval v \: typ <-> ⊢ᵥ v \: typ.
Proof.
  intros. assert (sval_to_val read_ndetbit (eval_val_to_sval v) v). {
    rewrite sval_to_val_eval_val_to_sval_iff; auto. intros.
    split; intros. inv H; auto. subst. constructor. } split; intros.
  - eapply exec_val_preserves_typ; [apply H | apply H0].
  - assert (val_to_sval v (eval_val_to_sval v)). {
      rewrite val_to_sval_iff. reflexivity. }
    eapply exec_val_preserves_typ; [apply H1 | apply H0].
Qed.

Lemma to_liberal_sval_typ_inv: forall {tags_t: Type} v (typ: @P4Type tags_t),
    ⊢ᵥ val_to_liberal_sval v \: typ -> ⊢ᵥ v \: typ.
Proof.
  intros. assert (sval_to_val read_ndetbit (eval_val_to_sval v) v). {
    rewrite sval_to_val_eval_val_to_sval_iff; auto. intros.
    split; intros. inv H0; auto. subst. constructor. }
  pose proof (sval_refine_liberal_eval v).
  assert (val_sim (val_to_liberal_sval v) v). {
    eapply exec_val_trans; eauto. repeat intro; auto. }
  eapply exec_val_preserves_typ; [apply H2 | apply H].
Qed.

Lemma sval_to_val_to_liberal_sval : forall v,
    sval_to_val read_ndetbit (val_to_liberal_sval v) v.
Proof.
  intros. induction v using custom_ValueBase_ind; simpl; try constructor; auto;
    try unfold bool_to_none; try constructor.
  1-3: rewrite Forall2_map1, Forall2_Forall, Forall_forall; intros; constructor.
  1,5: induction H; simpl; constructor; assumption.
  1-3: induction H; simpl; constructor;[| assumption];
  destruct x; simpl in *; split; auto.
Qed.

Lemma sval_to_val_to_sval_valid_only : forall v,
    sval_to_val read_ndetbit (val_to_sval_valid_only v) v.
Proof.
  intros. induction v using custom_ValueBase_ind; simpl; try repeat constructor.
  1-3: rewrite Forall2_map1, Forall2_Forall, Forall_forall; intros; constructor.
  1,5: induction H; simpl; constructor; assumption.
  1,3: (induction H; simpl; constructor; [| assumption];
        destruct x; simpl in *; split; auto).
  - destruct b; constructor; try constructor.
    + induction H; simpl; constructor. 2: assumption.
      destruct x. simpl in *. split; auto.
    + clear H. induction vs; simpl; constructor. 2: assumption.
      destruct a. simpl. split; auto. apply sval_to_val_to_liberal_sval.
  - apply sval_to_val_eval_val_to_sval. intros. constructor.
Qed.

Lemma to_sval_valid_only_typ_inv: forall {tags_t: Type} v (typ: @P4Type tags_t),
    ⊢ᵥ val_to_sval_valid_only v \: typ -> ⊢ᵥ v \: typ.
Proof.
  intros. eapply exec_val_preserves_typ in H; eauto.
  apply sval_to_val_to_sval_valid_only.
Qed.
