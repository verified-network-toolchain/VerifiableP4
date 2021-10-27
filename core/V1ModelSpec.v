Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Notations.
Require Import BinNat.
(* Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer. *)

Section V1ModelSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t bool).
Notation Sval := (@ValueBase tags_t (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Notation extern_state := (@Target.extern_state tags_t Expression V1ModelExternSem).

Notation object := (@object tags_t Expression).

Instance target : @Target tags_t Expression := V1Model.

Variable ge : (@genv tags_t).

Definition register_read_pre (p : path) reg i :=
  fun (args : list Sval) st =>
    args = [ValBaseBit (P4Arith.to_loptbool 32%N i)]
    /\ PathMap.get p (get_external_state st) = Some (ObjRegister reg).

Definition register_read_post (p : path) reg i :=
  fun (args : list Sval) st =>
    args = [ValBaseBit (P4Arith.to_loptbool (reg_width reg) (Znth i (reg_content reg)))]
    /\ PathMap.get p (get_external_state st) = Some (ObjRegister reg).

Definition hoare_func_modifies (ge : genv) (p : path) (func : @fundef tags_t) (vars : list Locator) (exts : list Locator) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    (forall q, ~(In (LInstance q) vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st'))
    /\ (forall q, ~(In q (map (loc_to_path p) exts)) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st')).

Definition hoare_func_spec (ge : genv) (p : path) (pre : arg_assertion)
    (func : @fundef tags_t) (targs : list P4Type) (post : arg_ret_assertion)
    (vars : list Locator) (exts : list Locator) :=
  hoare_func ge p pre func targs post
    /\ hoare_func_modifies ge p func vars exts.

Definition register_read_spec : Prop :=
  forall (p : path) (reg : register) (i : Z),
    hoare_func_spec ge p
        (register_read_pre p reg i)
        (FExternal !"Register" !"read")
        nil
        (fun args _ => register_read_post p reg i args)
        [] [].




