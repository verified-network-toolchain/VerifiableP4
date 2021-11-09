Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Require Import Coq.Program.Basics.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.abstract.register.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.Tofino.

Instance target : @Target Info (@Expression Info) := Tofino.

Opaque (* IdentMap.empty IdentMap.set *) PathMap.empty PathMap.set.
Opaque new_register.
(* Opaque construct_extern. *)
Definition ge := Eval compute in gen_ge prog.
Definition init_es := Eval compute in snd (instantiate_prog ge prog).


