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
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.AssertionNotations.
Require Import BinNat.
Require Import BinInt.
Open Scope Z_scope.
(* Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer. *)

Section V1ModelSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
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

(* Definition register_read_pre (p : path) reg i :=
  (0 <= i < reg_size reg)%Z
  ARG
  fun (args : list Sval) st =>
    (0 <= i < reg_size reg)%Z /\
    args = [ValBaseBit (to_loptbool 32%N i)]
    /\ PathMap.get p (get_external_state st) = Some (ObjRegister reg).

Definition register_read_post (p : path) reg i :=
  fun (args : list Sval) (retv : Val) st =>
    args = [eval_val_to_sval ge (Znth i (reg_content reg))]
    /\ PathMap.get p (get_external_state st) = Some (ObjRegister reg). *)

Axiom register_read_spec : forall (p : path) (reg : register) (i : Z) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  (0 <= i < snd reg_s)%Z ->
  hoare_func_spec ge p
    (ARG [ValBaseBit (to_loptbool 32%N i)]
    (MEM []
    (EXT [(p, ObjRegister reg)])))
    (FExternal "register" "read") nil
    (ARG_RET [eval_val_to_sval (Znth i reg)] ValBaseNull
    (MEM []
    (EXT [])))
    [] [].

(* Definition register_write_pre (p : path) reg i v :=
  fun (args : list Sval) st =>
    (0 <= i < reg_size reg)%Z /\
    args = [ValBaseBit (to_loptbool 32%N i); eval_val_to_sval ge v]
    /\ PathMap.get p (get_external_state st) = Some (ObjRegister reg).

Definition register_write_post (p : path) reg i v :=
  fun (args : list Sval) (retv : Val) st =>
    args = []
    /\ PathMap.get p (get_external_state st) =
        Some (ObjRegister {| reg_width := reg_width reg;
                             reg_size := reg_size reg;
                             reg_content := upd_Znth i (reg_content reg) v |}). *)

(* We need to say v is a definite value, right? *)
Axiom register_write_spec : forall (p : path) (reg : register) (i : Z) (v : Val) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  (0 <= i < snd reg_s)%Z ->
  hoare_func_spec ge p
    (ARG [ValBaseBit (to_loptbool 32%N i); eval_val_to_sval v]
    (MEM []
    (EXT [(p, ObjRegister reg)])))
    (FExternal "register" "write") nil
    (ARG_RET [] ValBaseNull
    (MEM []
    (EXT [(p, ObjRegister (upd_Znth i reg v))])))
    [] [p].

End V1ModelSpec.

(*
Several issues:
- out of bounds for i
- to_lbool/to_loptbool is N-to-1 mapping, diffcult to automate
=> also a problem in semantics.v
- are v and i assumed to be bounded in post_condition?
*)

