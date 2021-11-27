Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import Coq.Numbers.BinNums.
Open Scope type_scope.

Section AssertionLang.

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

Context `{@Target tags_t (@Expression tags_t)}.

Definition mem_unit := path * Sval.

Definition mem_assertion := list mem_unit.

Definition mem_satisfies_unit (m : mem) (a_unit : mem_unit) : Prop :=
  let (p, sv) := a_unit in
  match PathMap.get p m with
  | Some sv' => sval_refine sv sv'
  | None => False
  end.

Definition mem_satisfies (m : mem) (a : mem_assertion) : Prop :=
  fold_right and True (map (mem_satisfies_unit m) a).

Definition mem_denote (a : mem_assertion) : mem -> Prop :=
  fun m => mem_satisfies m a.

Definition arg_assertion := list Sval.

Definition arg_satisfies (args : list Sval) (a : arg_assertion) : Prop :=
  Forall2 sval_refine a args.

Definition arg_denote (a : arg_assertion) : list Sval -> Prop :=
  fun args => arg_satisfies args a.

Definition ret_assertion := Sval.

Definition ret_satisfies (retv : Sval) (a : ret_assertion) : Prop :=
  sval_refine a retv.

Definition ret_denote (a : ret_assertion) : Sval -> Prop :=
  fun retv => ret_satisfies retv a.

Definition ext_unit := path * extern_object.

Definition ext_assertion := list ext_unit.

Definition ext_satisfies_unit (es : extern_state) (a_unit : ext_unit) : Prop :=
  let (p, eo) := a_unit in
  match PathMap.get p es with
  | Some eo' => eo = eo'
  | None => False
  end.

Definition ext_satisfies (es : extern_state) (a : ext_assertion) : Prop :=
  fold_right and True (map (ext_satisfies_unit es) a).

Definition ext_denote (a : ext_assertion) : extern_state -> Prop :=
  fun es => ext_satisfies es a.

(** * Update and Get *)

(* Current behavior:
    validate a header regardless of the sucess of writing *)
Fixpoint upd_sval_once (v: Sval) (p: path) (f: Sval) : Sval :=
  match v, p with
  | _, [] => f
  | ValBaseStruct fields, hd :: tl =>
      match AList.get fields hd with
      | Some v' => 
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseStruct fields'
          | None => v (* Impossible *)
          end
      | None => v
      end
  | ValBaseRecord fields, hd :: tl =>
      match AList.get fields hd with
      | Some v' => 
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseRecord fields'
          | None => v (* Impossible *)
          end
      | None => v
      end
  | ValBaseUnion fields, hd :: tl =>
      match AList.get fields hd with
      | Some v' => 
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseUnion fields'
          | None => v (* Impossible *)
          end
      | None => v
      end
  | ValBaseHeader fields vbit, hd :: tl =>
      match AList.get fields hd with
      | Some v' => 
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseHeader fields' (Some true)
          | None => v (* Impossible *)
          end
      | None => v
      end
  | _, _ => v
  end.

Definition upd_sval (v: Sval) (upds: list (path * Sval)): Sval :=
  List.fold_left (fun v pf => upd_sval_once v (fst pf) (snd pf)) upds v.

Definition gen_sval (typ: P4Type) (upds: list (path * Sval)): option Sval :=
  match uninit_sval_of_typ (Some false) typ with
  | Some v =>
      Some (List.fold_left (fun v pf => upd_sval_once v (fst pf) (snd pf)) upds v)
  | None =>
      None
  end.

Definition extract (v : Val) (f : ident) : option Val :=
  match v with
  | ValBaseStruct fields =>
      AList.get fields f
  | ValBaseHeader fields true =>
      AList.get fields f
  | _ => None
  end.

Definition extract_option (ov : option Val) (f : ident) : option Val :=
  match ov with
  | Some v => extract v f
  | None => None
  end.

Definition extract_sval (v : Sval) (f : ident) : option Sval :=
  match v with
  | ValBaseStruct fields =>
      AList.get fields f
  | ValBaseHeader fields (Some true) =>
      AList.get fields f
  | _ => None
  end.

Definition extract_option_sval (ov : option Sval) (f : ident) : option Sval :=
  match ov with
  | Some v => extract_sval v f
  | None => None
  end.

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
*)

End AssertionLang.
