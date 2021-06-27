Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import Poulet4.V1Model.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Section V1ModelLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation SemLval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation Expression := (@Expression tags_t).
Notation extern_state := (@Target.extern_state tags_t Expression V1ModelExternSem).

Notation object := (@object tags_t Expression).

Variable this : path.

Definition ext_assertion_unit : Type := Locator * object.

Definition ext_assertion := list ext_assertion_unit.

Definition ext_satisfies_unit (es : extern_state) (a_unit : ext_assertion_unit) : Prop :=
  let (loc, obj) := a_unit in
  PathMap.get (loc_to_path this loc) es = Some obj.

Definition ext_satisfies (es : extern_state) (a : ext_assertion) : Prop :=
  fold_right and True (map (ext_satisfies_unit es) a).

Definition ext_to_shallow_assertion (a : ext_assertion) : extern_state -> Prop :=
  fun es => ext_satisfies es a.

Axiom object_eqb : (object -> object -> bool).

Axiom object_eqb_spec : forall obj1 obj2, reflect (obj1 = obj2) (object_eqb obj1 obj2).

Definition ext_assretion_unit_equivb (a_unit1 a_unit2 : ext_assertion_unit) :=
  match a_unit1, a_unit2 with
  | (loc1, obj1), (loc2, obj2) =>
      locator_equivb loc1 loc2 && object_eqb obj1 obj2
  end.

Fixpoint ext_implies_unit (a : ext_assertion) (a_unit : ext_assertion_unit) :=
  match a with
  | hd :: tl =>
      ext_assretion_unit_equivb hd a_unit || ext_implies_unit tl a_unit
  | [] =>
      false
  end.

Fixpoint ext_implies (a1 a2 : ext_assertion) :=
  match a2 with
  | hd :: tl =>
      ext_implies_unit a1 hd && ext_implies a1 tl
  | [] =>
      true
  end.

Lemma ext_implies_unit_sound es a a_unit :
  ext_to_shallow_assertion a es ->
  ext_implies_unit a a_unit ->
  ext_satisfies_unit es a_unit.
Proof.
Admitted.
(*   intros H_pre H_implies_unit.
  induction a as [ | hd tl].
  - inversion H_implies_unit.
  - destruct (assretion_unit_equivb hd a_unit) eqn:H_assretion_unit_equivb.
    + assert (satisfies_unit m hd) by (clear -H_pre; sfirstorder).
      destruct hd as [lv1 v1 | lv1 v1]; destruct a_unit as [lv2 v2 | lv2 v2];
        only 2-4 : sfirstorder.
      simpl in H_assretion_unit_equivb.
      assert (lv1 = lv2) by (apply lval_equivb_eq; hauto unfold: is_true, andb).
      assert (v1 = v2) by (apply val_eqb_eq; hauto unfold: is_true, andb).
      sfirstorder.
    + apply IHtl.
      * sfirstorder.
      * hauto.
Qed. *)

Lemma ext_implies_sound es pre post :
  ext_to_shallow_assertion pre es ->
  ext_implies pre post ->
  ext_to_shallow_assertion post es.
Proof.
  intros H_pre H_implies.
  induction post as [ | hd tl].
  - exact I.
  - split.
    + apply ext_implies_unit_sound with (a := pre); only 1 : assumption.
      hauto b: on.
    + apply IHtl. hauto b: on.
Qed.

End V1ModelLang.
