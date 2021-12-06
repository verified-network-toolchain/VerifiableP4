Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Open Scope type_scope.

Section AssertionNotations.

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

Definition EXT : ext_assertion -> ext_assertion :=
  id.

Definition MEM (a_mem : mem_assertion) (a_ext : ext_assertion) : Hoare.assertion :=
  fun '(m, es) => mem_denote a_mem m /\ ext_denote a_ext es.

Definition ARG (a_arg : list Sval) (a : Hoare.assertion) : Hoare.arg_assertion :=
  fun args st => arg_denote a_arg args /\ a st.

Definition RET (a_ret : Sval) (a : Hoare.assertion) : Hoare.ret_assertion :=
  fun retv st => (forall sv', val_to_sval retv sv' -> ret_denote a_ret sv') /\ a st.

Definition ARG_RET (a_arg : list Sval) (a_ret : Sval) (a : Hoare.assertion) : Hoare.arg_ret_assertion :=
  fun args retv st => arg_denote a_arg args
    /\ (forall sv', val_to_sval retv sv' -> ret_denote a_ret sv')
    /\ a st.

End AssertionNotations.
