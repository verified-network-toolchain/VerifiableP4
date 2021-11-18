Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.

Section HoareSoundness.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).
Notation Locator := (@Locator tags_t).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Context `{@Target tags_t Expression}.

Variable ge : (@genv tags_t _).
Variable inst_m : (@inst_mem tags_t _).

(****************************** Soundness ***************************)
(* TODO prove them *)

Axiom deep_hoare_stmt_sound : forall p pre stmt post,
  deep_hoare_stmt ge inst_m p pre stmt post ->
  hoare_stmt ge inst_m p pre stmt post.

Axiom deep_hoare_block_sound : forall p pre block post,
  deep_hoare_block ge inst_m p pre block post ->
  hoare_block ge inst_m p pre block post.

Axiom deep_hoare_func_sound : forall p pre fd targs post,
  deep_hoare_func ge inst_m p pre fd targs post ->
  hoare_func ge inst_m p pre fd targs post.

Axiom deep_hoare_call_sound : forall p pre expr post,
  deep_hoare_call ge inst_m p pre expr post ->
  hoare_call ge inst_m p pre expr post.

End HoareSoundness.
