Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import ProD3.core.Coqlib.
Open Scope type_scope.

Section AssertionLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t bool).
Notation Sval := (@ValueBase tags_t (option bool)).
Notation SemLval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation mem := (@Semantics.mem tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Variable this : path.

(* Definition Field : Type := string.
Definition Lval : Type := Locator * list Field. *)

Definition assertion_unit := path * Sval.

Definition assertion := list assertion_unit.

(* Notation alist_get l s := (AList.get l (P4String.Build_t _ default s)).

Definition extract (v : Val) (f : Field) : option Val :=
  match v with
  | ValBaseStruct fields =>
      alist_get fields f
  | ValBaseHeader fields true =>
      alist_get fields f
  | _ => None
  end.

Definition extract_option (ov : option Val) (f : Field) : option Val :=
  match ov with
  | Some v => extract v f
  | None => None
  end. *)

Inductive bit_refine : option bool -> option bool -> Prop :=
  | read_none : forall ob, bit_refine None ob
  | read_some : forall b, bit_refine (Some b) (Some b).

Definition sval_refine := exec_val (tags_t := tags_t) bit_refine.

(* Definition mem_eval_read (m : mem) (lv : Lval) : option Val :=
  let (loc, fl) := lv in
  fold_left extract_option fl (PathMap.get (loc_to_path this loc) m).

Definition isNil {A} (l : list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Definition mem_is_valid_field (m : mem) (lv : Lval) : bool :=
  let (loc, fl) := lv in
  isNil fl || isSome (mem_eval_read m lv). *)

Definition satisfies_unit (m : mem) (a_unit : assertion_unit) : Prop :=
  let (p, sv) := a_unit in
  match PathMap.get p m with
  | Some sv' => sval_refine sv sv'
  | None => False
  end.

Definition satisfies (m : mem) (a : assertion) : Prop :=
  fold_right and True (map (satisfies_unit m) a).

Definition denote (a : assertion) : mem -> Prop :=
  fun m => satisfies m a.

(* Definition loc_no_overlapping (loc1 : Locator) (loc2 : Locator) : bool :=
  match loc1, loc2 with
  | LInstance p1, LInstance p2 => ~~ (path_equivb p1 p2)
  | _, _ => false
  end.

Fixpoint field_list_no_overlapping (fl1 fl2 : list Field) : bool :=
  match fl1, fl2 with
  | hd1 :: tl1, hd2 :: tl2 =>
      ~~(String.eqb hd1 hd2) || field_list_no_overlapping tl1 tl2
  | _, _ => false
  end.

Definition is_instance (loc : Locator) : bool :=
  match loc with
  | LInstance _ => true
  | LGlobal _ => false
  end.

Definition lval_no_overlapping (lv1 : Lval) (lv2 : Lval) : bool :=
  match lv1, lv2 with
  | (loc1, fl1), (loc2, fl2) =>
      is_instance loc1 && is_instance loc2 && (loc_no_overlapping loc1 loc2 || field_list_no_overlapping fl1 fl2)
  end.

Fixpoint no_overlapping (lv : Lval) (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      match hd with
      | AVal hd_lv _ =>
          lval_no_overlapping lv hd_lv && no_overlapping lv tl
      | AType _ _ =>
          no_overlapping lv tl
      end
  | [] => true
  end.

Definition is_lval_instance (lv : Lval) : bool :=
  match lv with
  | (loc, _) =>
      is_instance loc
  end.

Fixpoint wellformed (a : assertion) : bool :=
  match a with
  | hd :: tl =>
      match hd with
      | AVal lv _ =>
          is_lval_instance lv && no_overlapping lv tl && wellformed tl
      | AType lv _ =>
          is_lval_instance lv && wellformed tl
      end
  | [] => true
  end.

Definition field_equivb (f1 f2 : Field) : bool :=
  match f1, f2 with
  | s1, s2 =>
      String.eqb s1 s2
  end.

Definition lval_equivb (lv1 lv2 : Lval) : bool :=
  match lv1, lv2 with
  | (loc1, fl1), (loc2, fl2) =>
      locator_equivb loc1 loc2 && list_eqb field_equivb fl1 fl2
  end.

Definition val_eqb (v1 v2 : Val) : bool :=
  match v1, v2 with
  | ValBaseNull, ValBaseNull => true
  | ValBaseBool b1, ValBaseBool b2 => Bool.eqb b1 b2
  | ValBaseInteger i1, ValBaseInteger i2 => BinInt.Z.eqb i1 i2
  | ValBaseBit w1 i1, ValBaseBit w2 i2 => Nat.eqb w1 w2 && BinInt.Z.eqb i1 i2
  | ValBaseInt w1 i1, ValBaseInt w2 i2 => Nat.eqb w1 w2 && BinInt.Z.eqb i1 i2
  | _, _ => false
  end.

Definition assretion_unit_equivb (a_unit1 a_unit2 : assertion_unit) :=
  match a_unit1, a_unit2 with
  | AVal lv1 v1, AVal lv2 v2 =>
      lval_equivb lv1 lv2 && val_eqb v1 v2
  | _, _ => false (* ignore AType for now *)
  end.

Fixpoint implies_unit (a : assertion) (a_unit : assertion_unit) :=
  match a with
  | hd :: tl =>
      assretion_unit_equivb hd a_unit || implies_unit tl a_unit
  | [] =>
      false
  end.

Fixpoint implies (a1 a2 : assertion) :=
  match a2 with
  | hd :: tl =>
      implies_unit a1 hd && implies a1 tl
  | [] =>
      true
  end.

(*************** Argument and return value assertion language **********)

Import BinNums.

Instance Inhabitant_option {T: Type} : Inhabitant (option T) := None.

Definition Znth_option {T} n (l : list T) :=
  Znth n (map Some l).

Definition arg_Lval : Type := Z * list Field.

Definition arg_eval_read (args : list Val) (lv : arg_Lval) : option Val :=
  let (n, fl) := lv in
  fold_left extract_option fl (Znth_option n args).

Inductive arg_assertion_unit :=
| ArgVal: arg_Lval -> Val -> arg_assertion_unit
| ArgType : arg_Lval -> P4Type -> arg_assertion_unit.

Definition arg_assertion := list arg_assertion_unit.

Definition arg_satisfies_unit (args : list Val) (a_unit : arg_assertion_unit) : Prop :=
  match a_unit with
  | ArgVal lv v =>
      arg_eval_read args lv = Some v
  | ArgType lv typ =>
      True
  end.

Definition arg_satisfies (args : list Val) (a : arg_assertion) : Prop :=
  fold_right and True (map (arg_satisfies_unit args) a).

Definition arg_to_shallow_assertion (a : arg_assertion) : list Val -> Prop :=
  fun args => arg_satisfies args a.

Definition ret_Lval : Type := list Field.

Definition ret_eval_read (vret : Val) (lv : ret_Lval) : option Val :=
  fold_left extract_option lv (Some vret).

Inductive ret_assertion_unit :=
| RetVal: ret_Lval -> Val -> ret_assertion_unit
| RetType : ret_Lval -> P4Type -> ret_assertion_unit.

Definition ret_assertion := list ret_assertion_unit.

Definition ret_satisfies_unit (vret : Val) (a_unit : ret_assertion_unit) : Prop :=
  match a_unit with
  | RetVal lv v =>
      ret_eval_read vret lv = Some v
  | RetType lv typ =>
      True
  end.

Definition ret_satisfies (vret : Val) (a : ret_assertion) : Prop :=
  fold_right and True (map (ret_satisfies_unit vret) a).

Definition ret_to_shallow_assertion (a : ret_assertion) : Val -> Prop :=
  fun vret => ret_satisfies vret a. *)

End AssertionLang.
