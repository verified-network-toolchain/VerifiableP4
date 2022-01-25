Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Notations.
Require Import Poulet4.P4Arith.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.Modifies.
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.AssertionNotations.
Require Import BinNat.
Require Import BinInt.
Open Scope Z_scope.
(* Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer. *)

Section V1ModelSpec.

Context [tags_t: Type] [tags_t_inhabitant : Inhabitant tags_t].
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := (@ValueLvalue tags_t).

Notation ident := string.
Notation path := (list ident).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Instance target : @Target tags_t Expression := V1Model.

Variable ge : genv.

Open Scope func_spec.

Definition register_read_spec (p : path) (reg_s : register_static) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (reg : register) (i : Z) (H : (0 <= i < snd reg_s)%Z),
      PRE
        (ARG [ValBaseBit (to_loptbool 32%N i)]
        (MEM []
        (EXT [(p, ObjRegister reg)])))
      POST
        (ARG_RET [eval_val_to_sval (Znth i reg)] ValBaseNull
        (MEM []
        (EXT []))).

Axiom register_read_body : forall (p : path) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  fundef_satisfies_spec ge (FExternal "register" "read") nil (register_read_spec p reg_s).

(* We need to say v is a definite value, right? *)
Definition register_write_spec (p : path) (reg_s : register_static) : func_spec :=
  WITH,
    PATH p
    MOD None [p]
    WITH (reg : register) (i : Z) (v : Val) (H : (0 <= i < snd reg_s)%Z),
      PRE
        (ARG [ValBaseBit (to_loptbool 32%N i); eval_val_to_sval v]
        (MEM []
        (EXT [(p, ObjRegister reg)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
        (EXT [(p, ObjRegister (upd_Znth i reg v))]))).

Axiom register_write_body : forall (p : path) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  fundef_satisfies_spec ge (FExternal "register" "write") nil (register_write_spec p reg_s).

End V1ModelSpec.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (refine (proj2 (register_read_body _ _ _ _))) : func_specs.
#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (refine (proj2 (register_write_body _ _ _ _))) : func_specs.

(*
Several issues:
- out of bounds for i
- to_lbool/to_loptbool is N-to-1 mapping, diffcult to automate
=> also a problem in semantics.v
- are v and i assumed to be bounded in post_condition?
*)

