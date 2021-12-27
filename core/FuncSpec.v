Require Import Coq.Lists.List.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.

Section FuncSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}.

Definition hoare_func_modifies (ge : genv) (p : path) (func : @fundef tags_t) (vars : list path) (exts : list path) :=
  forall st inargs targs st' outargs sig,
    exec_func ge read_ndetbit p st func targs inargs st' outargs sig ->
    (forall q, ~(In q vars) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st'))
    /\ (forall q, ~(In q exts) -> PathMap.get q (get_memory st) = PathMap.get q (get_memory st')).

Definition hoare_func_spec (ge : genv) (p : path) (pre : arg_assertion)
    (func : @fundef tags_t) (targs : list P4Type) (post : arg_ret_assertion)
    (vars : list path) (exts : list path) :=
  hoare_func ge p pre func targs post
    /\ hoare_func_modifies ge p func vars exts.

End FuncSpec.
