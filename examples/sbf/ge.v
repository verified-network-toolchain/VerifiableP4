Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf.UseTofino.
Require Import ProD3.examples.sbf.p4ast.

Definition am_ge : genv := Eval compute -[PathMap.empty PathMap.set] in gen_am_ge prog.
(* Finished transaction in 19.806 secs (18.765u,0.968s) (successful) *)
Definition ge : genv := Eval compute -[am_ge PathMap.empty PathMap.set] in gen_ge' am_ge prog.
