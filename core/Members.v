Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import ProD3.core.Coqlib.
Require Import Coq.ZArith.BinInt.
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
  | ValBaseStack headers size next =>
      if String.eqb f "size" then
        ValBaseBit (P4Arith.to_loptbool 32%N (Z.of_N size))
      else if String.eqb f "lastIndex" then
        (if (next =? 0)%N 
        then (ValBaseBit (Zrepeat (@None bool) 32%Z))
        else (ValBaseBit (P4Arith.to_loptbool 32%N (Z.of_N (next - 1)))))
      else
        ValBaseNull
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
      ValBaseUnion (force fields (AList.set fields f f_sv))
  | _ => sv
  end.

Lemma get_some_get_set : forall {A} (l : AList.StringAList A) k (l' : AList.StringAList A) v1 v2,
  AList.get l k = Some v1 ->
  AList.get (force l' (AList.set l k v2)) k = Some v2.
Proof.
  intros.
  erewrite AList.get_some_set by eauto.
  apply AList.set_some_get.
Qed.

Lemma get_update : forall sv f f_sv,
  has_field f sv ->
  get f (update f f_sv sv) = f_sv.
Proof.
  intros.
  destruct sv; try solve [inv H].
  - unfold get, update, has_field in *.
    destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set by eauto.
      auto.
    + inv H.
  - destruct is_valid as [[] | ].
    * unfold get, update, has_field in *.
      destruct (AList.get fields f) eqn:?.
      + erewrite get_some_get_set by eauto.
        auto.
      + inv H.
    * inv H.
    * inv H.
  - unfold get, update, has_field in *.
    destruct (AList.get fields f) eqn:?.
    + erewrite get_some_get_set by eauto.
      auto.
    + inv H.
Qed.

End Members.
