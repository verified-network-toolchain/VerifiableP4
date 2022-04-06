Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Architecture.Target.
Require Import Poulet4.P4light.Architecture.Tofino.

Instance target : @Target Info (@Expression Info) := Tofino.Tofino.
