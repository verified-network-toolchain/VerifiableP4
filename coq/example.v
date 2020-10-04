Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Inductive Expression :=
| ETrue
| EFalse
| EInt : Z -> Expression
| Name : string -> Expression
| ArrayAccess: Expression -> Expression -> Expression
| BitStringAccess: Expression -> Z -> Z -> Expression
| List: list Expression -> Expression
| ERecord: list KeyValue -> Expression
with KeyValue :=
| KV: string -> Expression -> KeyValue.

Check (KV "hello" ETrue).
