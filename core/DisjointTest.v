Require Import Coq.Lists.List.
Require Import ProD3.core.ExtPred.
Require Import ProD3.core.Result.
Require Import ProD3.core.FuncSpec.
Require Import Hammer.Plugin.Hammer.

(* Section DisjointTest. *)

(* Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).

Context `{target : @Target tags_t (@Expression tags_t)}. *)

Ltac res_list :=
  lazymatch goal with
  | |- res_list ?P ?l =>
      first [
        apply rnil
      | apply rcons;
        only 2 : res_list
      ]
  | |- _ =>
      fail "The goal is not (res_list _ _)"
  end.

(* Import String.
Open Scope string_scope. *)

(* This is a preliminary implementation. It only tests verbatim paths. We use this tactic to
  test the rest tactics. *)
Ltac test_disjoint :=
  first [
    left; reflexivity
  | right; exact I
  ].

(* Goal result (disjoint ["a"] ["c"]).
  test_disjoint.
  Show Proof.
Abort.

Goal result (disjoint [] ["c"]).
  test_disjoint.
  Show Proof.
Abort. *)

Ltac test_ext_exclude :=
  res_list;
  apply Result.forallb;
  res_list;
  apply Result.forallb;
  res_list;
  test_disjoint.
