Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import Poulet4.Sublist.
Require Import ProD3.core.Coqlib.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Open Scope type_scope.

Section Members.

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

(* Test whether sv has a WRITABLE field f. *)
Definition has_field (f : ident) (sv : Sval) : bool :=
  match sv with
  | ValBaseStruct fields
  | ValBaseHeader fields (Some true)
  | ValBaseUnion fields =>
      is_some (AList.get fields f)
  | _ => false
  end.

Definition get (f : ident) (sv : Sval) : Sval :=
  match sv with
  | ValBaseRecord fields
  | ValBaseStruct fields
  | ValBaseHeader fields _
  | ValBaseUnion fields =>
      force ValBaseNull (AList.get fields f)
  | ValBaseStack headers next =>
      if String.eqb f "size" then
        ValBaseBit (P4Arith.to_loptbool 32%N (Zlength headers))
      else if String.eqb f "lastIndex" then
        (if (next =? 0)%N 
        then (ValBaseBit (Zrepeat (@None bool) 32%Z))
        else (ValBaseBit (P4Arith.to_loptbool 32%N (Z.of_N (next - 1)))))
      else
        ValBaseNull
  | _ => ValBaseNull
  end.

Definition havoc_header (f_is_valid : option bool -> option bool) : Sval -> Sval :=
  fun sv =>
    match sv with
    | ValBaseHeader fields is_valid =>
        ValBaseHeader (kv_map (uninit_sval_of_sval None) fields) (f_is_valid is_valid)
    | _ => ValBaseNull
    end.

Definition update (f : ident) (f_sv : Sval) (sv : Sval) : Sval :=
  match sv with
  | ValBaseStruct fields =>
      ValBaseStruct (force fields (AList.set fields f f_sv))
  | ValBaseHeader fields (Some true) =>
      ValBaseHeader (force fields (AList.set fields f f_sv)) (Some true)
  | ValBaseHeader fields is_valid (* (Some false) or None *) =>
      let uninit_f_sv' := uninit_sval_of_sval None f_sv in
      ValBaseHeader (force fields (AList.set fields f uninit_f_sv')) is_valid
  | ValBaseUnion fields =>
      let havoc_fields :=
        match f_sv with
        | ValBaseHeader hfields (Some true) =>
            kv_map (havoc_header (fun _ => Some false)) fields
        | ValBaseHeader hfields (Some false) =>
            kv_map (havoc_header id) fields
        | ValBaseHeader hfields None =>
            kv_map (havoc_header (fun _ => None)) fields
        | _ => fields
        end in
      ValBaseUnion (force havoc_fields (AList.set havoc_fields f f_sv))
  | _ => sv
  end.

Lemma get_some_get_set_same : forall {A} (l : AList.StringAList A) k (l' : AList.StringAList A) v1 v2,
  AList.get l k = Some v1 ->
  AList.get (force l' (AList.set l k v2)) k = Some v2.
Proof.
  intros.
  erewrite AList.get_some_set by eauto.
  apply AList.set_some_get.
Qed.

Lemma get_update_same : forall sv f f_sv,
  has_field f sv ->
  get f (update f f_sv sv) = f_sv.
Proof.
  intros.
  destruct sv; try solve [inv H].
  - unfold get, update, has_field in *.
    destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set_same by eauto.
      auto.
    + inv H.
  - destruct is_valid as [[] | ].
    * unfold get, update, has_field in *.
      destruct (AList.get fields f) eqn:?.
      + erewrite get_some_get_set_same by eauto.
        auto.
      + inv H.
    * inv H.
    * inv H.
  - unfold get, update, has_field in *.
    admit.
    (* destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set by eauto.
      auto.
    + inv H. *)
(* Qed. *)
Admitted.

Lemma get_update_same' : forall sv f1 f2 f_sv,
  f1 = f2 ->
  has_field f2 sv ->
  get f1 (update f2 f_sv sv) = f_sv.
Proof.
  intros. subst. apply get_update_same; auto.
Qed.

Lemma get_set_diff : forall {A} (l : AList.StringAList A) k1 k2 v,
  k1 <> k2 ->
  AList.get (force l (AList.set l k2 v)) k1 = AList.get l k1.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct a as [k' v'].
    destruct (EquivUtil.StringEqDec k2 k') as [H_k2 | H_k2].
    + simpl. cbv in H_k2; subst.
      rewrite !AList.get_neq_cons; auto.
    + simpl. cbv in H_k2.
      destruct (AList.set l k2 v).
      * simpl.
        destruct (EquivUtil.StringEqDec k1 k') as [H_k1 | H_k1].
        ++rewrite !AList.get_eq_cons; auto.
        ++rewrite !AList.get_neq_cons; auto.
      * simpl.
        destruct (EquivUtil.StringEqDec k1 k') as [H_k1 | H_k1].
        ++rewrite !AList.get_eq_cons; auto.
        ++rewrite !AList.get_neq_cons; auto.
Qed.

Lemma get_update_diff : forall sv f1 f2 f_sv,
  has_field f2 sv ->
  f1 <> f2 ->
  get f1 (update f2 f_sv sv) = get f1 sv.
Proof.
  intros.
  destruct sv; try apply eq_refl.
  - unfold get, update in *.
    rewrite get_set_diff; auto.
  - destruct is_valid as [[] | ].
    * unfold get, update in *.
      rewrite get_set_diff; auto.
    * inv H.
    * inv H.
  - unfold get, update, has_field in *.
    (* TODO union *)
    admit.
    (* destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set by eauto.
      auto.
    + inv H. *)
(* Qed. *)
Admitted.

End Members.
