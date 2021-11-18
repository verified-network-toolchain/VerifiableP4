Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Require Import Coq.Program.Basics.
Require Import Poulet4.P4Arith.
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

Transparent PathMap.empty PathMap.set new_register.

Definition c : fundef := Eval compute in force (FExternal !"" !"") (PathMap.get !["c"] (ge_func ge)).

Definition foo : {st' & exec_func ge read_ndetbit !["main"; "ctrl"] (PathMap.empty, init_es) c nil
  [ValBaseBit (to_loptbool 16%N 0)] st' [ValBaseBit (to_loptbool 16%N 0)] SReturnNull}.
Proof.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. 
  econstructor. repeat econstructor. econstructor. econstructor. 
  simpl. econstructor. repeat econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. repeat econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  repeat econstructor. econstructor. repeat econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor. econstructor.
  repeat econstructor. econstructor. econstructor. econstructor. repeat econstructor.
  repeat econstructor.
  simpl. repeat econstructor. repeat econstructor.
  simpl. repeat econstructor.
  simpl. repeat econstructor.
  econstructor. repeat econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor. repeat econstructor. econstructor.
  econstructor. econstructor. econstructor. econstructor.
  simpl. econstructor. econstructor. econstructor. econstructor. econstructor.
  econstructor. econstructor. econstructor.
Defined.

Definition st := Eval simpl in projT1 foo.









