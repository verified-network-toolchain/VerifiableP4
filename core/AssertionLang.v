Require Import Coq.ssr.ssrbool.
Require Import Coq.ssr.ssreflect.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.

Section AssertionLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Definition assertion := list (@Locator tags_t * Val).

Variable this : path.

Definition satisfies_unit (st : state) (a_unit : @Locator tags_t * Val) : Prop :=
  let (loc, v) := a_unit in
  loc_to_val this loc st = Some v.

Definition satisfies (st : state) (a : assertion) : Prop :=
  fold_left and (map (satisfies_unit st) a) True.

Definition to_shallow_assertion (a : assertion) : state -> Prop :=
  fun st => satisfies st a.

Definition no_overlapping_unit_unit (a_unit1 a_unit2 : @Locator tags_t * Val) : bool :=
  let (loc1, _) := a_unit1 in
  let (loc2, _) := a_unit2 in
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => ~~ (path_equivb p1 p2)
  | _, _ => false
  end.

Fixpoint no_overlapping_unit (a_unit : @Locator tags_t * Val) (a : assertion) : bool :=
  match a with
  | hd :: tl => no_overlapping_unit_unit a_unit hd && no_overlapping_unit a_unit tl
  | [] => true
  end.

Fixpoint no_overlapping (a : assertion) : bool :=
  match a with
  | hd :: tl => no_overlapping_unit hd tl && no_overlapping tl
  | [] => true
  end.

Definition locator_equiv (loc1 loc2 : @Locator tags_t) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => path_equivb p1 p2
  | LGlobal p1, LGlobal p2 => path_equivb p1 p2
  | _, _ => false
  end.

Fixpoint update_val_by_loc (a : assertion) (loc : Locator) (v : Val) : assertion :=
  match a with
  | (hd_loc, hd_v) :: tl =>
      if locator_equiv loc hd_loc then
        (hd_loc, v) :: tl
      else
        (hd_loc, hd_v) :: update_val_by_loc tl loc v
  | [] => [(loc, v)]
  end.

Definition is_instance (loc : @Locator tags_t) : bool :=
  match loc with
  | LInstance _ => true
  | LGlobal _ => false
  end.

(* Lemma update_val_by_loc_sound : forall st a loc v,
  no_overlapping a ->
  is_instance loc = true ->
  to_shallow_assertion a st ->
  to_shallow_assertion (update_val_by_loc a loc v) (Semantics.update_val_by_loc this st loc v).
Proof.
  intros * H_no_overlapping H_is_instance H_pre.
  destruct loc; only 1 : inversion H_is_instance.
  unfold to_shallow_assertion in *.
  induction a; intros.
  - destruct st. simpl. unfold satisfies. simpl. repeat split.
    unfold loc_to_val. simpl.
    replace (PathMap.get (this ++ p) (PathMap.set (this ++ p) v m)) with (Some v) by admit.
    reflexivity.
  - assert (satisfies (Semantics.update_val_by_loc this st (LInstance p) v)
        (update_val_by_loc a0 (LInstance p) v)). {
      apply IHa.
      - simpl in H_no_overlapping. Search reflect and. move /andP : H_no_overlapping => H_no_overlapping. apply H_no_overlapping. *)

End AssertionLang.










