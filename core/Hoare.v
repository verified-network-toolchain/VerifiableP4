Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.

Section Hoare.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase tags_t).

Notation ident := (P4String.t tags_t).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation signal := (@signal tags_t).

Context `{@Target tags_t (@Expression tags_t)}.

Variable ge : (@genv tags_t).
Variable ge_typ : (@genv_typ tags_t).
Variable ge_senum : (@genv_senum tags_t).
Variable inst_m : (@inst_mem tags_t).

Definition assertion := state -> Prop.

Definition hoare_stmt (p : path) (pre : assertion) (stmt : Statement) (post : assertion) :=
  forall st st' sig,
    pre st ->
    exec_stmt ge ge_typ ge_senum p inst_m st stmt st' sig ->
    sig = SContinue /\ post st'.

Definition hoare_block (p : path) (pre : assertion) (block : Block) (post : assertion) :=
  forall st st' sig,
    pre st ->
    exec_block ge ge_typ ge_senum p inst_m st block st' sig ->
    sig = SContinue /\ post st'.

Definition hoare_call (p : path) (pre : assertion) (expr : Expression) (post : assertion) :=
  forall st st' sig,
    pre st ->
    exec_call ge ge_typ ge_senum p inst_m st expr st' sig ->
    sig = SContinue /\ post st'.

Definition arg_assertion := list Val -> state -> Prop.

Definition hoare_func (p : path) (pre : arg_assertion) (func : @fundef tags_t) (targs : list P4Type) (post : arg_assertion) :=
  forall st inargs st' outargs sig,
    pre inargs st ->
    exec_func ge ge_typ ge_senum p inst_m st func targs inargs st' outargs sig ->
    sig = SContinue /\ post outargs st'.

Section DeepEmbeddedHoare.

Definition implies (pre post : assertion) :=
  forall st, pre st -> post st.

Inductive deep_hoare_stmt : path -> assertion -> Statement -> assertion -> Prop :=
  | deep_hoare_stmt_intro : forall p pre stmt post,
      hoare_stmt p pre stmt post ->
      deep_hoare_stmt p pre stmt post.

Inductive deep_hoare_block : path -> assertion -> Block -> assertion -> Prop :=
  | deep_hoare_block_nil : forall p pre post,
      implies pre post ->
      deep_hoare_block p pre BlockNil post
  | deep_hoare_block_cons : forall p pre stmt mid block post,
      deep_hoare_stmt p pre stmt mid ->
      deep_hoare_block p mid block post ->
      deep_hoare_block p pre (BlockCons stmt block) post.

Definition hoare_eval_expr (p : path) (pre : assertion) (expr : Expression) (v : Val) : Prop :=
  forall st,
    pre st ->
    exec_expr ge_typ ge_senum p st expr v.

Definition hoare_eval_lvalue_expr (p : path) (pre : assertion) (expr : Expression) (lv : Lval) : Prop :=
  forall st,
    pre st ->
    exec_lvalue_expr ge_typ ge_senum p st expr lv SContinue.

Inductive deep_hoare_call : path -> assertion -> Expression -> assertion -> Prop :=
  | deep_hoare_call_intro : forall p pre expr post,
      hoare_call p pre expr post ->
      deep_hoare_call p pre expr post.

Fixpoint _in (x : ident) (al : list ident) : bool :=
  match al with
  | y :: al => P4String.equivb x y || _in x al
  | [] => false
  end.

Fixpoint no_dup (al : list ident) : bool :=
  match al with
  | x :: al => ~~(_in x al) && no_dup al
  | [] => true
  end.

Inductive deep_hoare_func : path -> arg_assertion -> @fundef tags_t -> list P4Type -> arg_assertion -> Prop :=
  | deep_hoare_func_internal : forall p pre func targs post,
      hoare_func p pre func targs post ->
      deep_hoare_func p pre func targs post.
(*   | deep_hoare_func_intro : forall p pre func targs post,
      hoare_func p pre func targs post ->
      deep_hoare_func p pre func targs post. *)

(* FInternal : list (P4String.t tags_t * direction) -> Block -> Block -> fundef *)

End DeepEmbeddedHoare.

End Hoare.



















