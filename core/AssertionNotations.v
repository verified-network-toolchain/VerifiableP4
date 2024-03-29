Require Import Coq.Strings.String.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Syntax.Value.
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

Context {target : @Target tags_t (@Expression tags_t)}.

Definition EXT : ext_assertion -> extern_state -> Prop :=
  ext_denote.

Global Add Parametric Morphism : EXT with
  signature ext_assertion_equiv ==> eq as EXT_mor.
Proof. auto. Qed.

Definition MEM (a_mem : mem_assertion) (a_ext : extern_state -> Prop) : Hoare.assertion :=
  fun '(m, es) => mem_denote a_mem m /\ a_ext es.

Definition ARG (a_arg : list Sval) (a : Hoare.assertion) : Hoare.arg_assertion :=
  fun args st => arg_denote a_arg args /\ a st.

Definition RET (a_ret : Sval) (a : Hoare.assertion) : Hoare.ret_assertion :=
  fun retv st => ret_denote a_ret retv /\ a st.

Definition ARG_RET (a_arg : list Sval) (a_ret : Sval) (a : Hoare.assertion) : Hoare.arg_ret_assertion :=
  fun args retv st => arg_denote a_arg args
    /\ ret_denote a_ret retv
    /\ a st.

End AssertionNotations.

Declare Scope assr.
Delimit Scope assr with assr.
Notation "'EX' x .. y , P " :=
  (assr_exists (fun x => .. (assr_exists (fun y => P%assr)) ..)) (at level 65, x binder, y binder, right associativity) : assr.

Declare Scope ret_assr.
Delimit Scope ret_assr with ret_assr.
Notation "'EX' x .. y , P " :=
  (ret_exists (fun x => .. (ret_exists (fun y => P%ret_assr)) ..)) (at level 65, x binder, y binder, right associativity) : ret_assr.

Declare Scope arg_ret_assr.
Delimit Scope arg_ret_assr with arg_ret_assr.
Notation "'EX' x .. y , P " :=
  (arg_ret_exists (fun x => .. (arg_ret_exists (fun y => P%arg_ret_assr)) ..)) (at level 65, x binder, y binder, right associativity) : arg_ret_assr.
