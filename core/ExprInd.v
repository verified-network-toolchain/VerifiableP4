Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Require Import Poulet4.Info.
Require Import Poulet4.Typed.
Require Poulet4.P4String.
Require Poulet4.P4Int.
Require Import Poulet4.Utils.
Require Import Poulet4.Syntax.

Inductive OptForall {A: Type} (P: A -> Prop): list (option A) -> Prop :=
| OptForall_nil: OptForall P nil
| OptForall_cons_None: forall (l: list (option A)),
    OptForall P l -> OptForall P (None :: l)
| OptForall_cons_Some: forall (x: A) (l: list (option A)),
    P x -> OptForall P l -> OptForall P (Some x :: l).

Section ExprInd.
  Context {tags_t: Type}.
  Notation P4String := (P4String.t tags_t).
  Notation P4Int := (P4Int.t tags_t).
  Notation Expression := (@Expression tags_t).

  Variable P: Expression -> Prop.

  Hypothesis HBool: forall t typ dir b, P (MkExpression t (ExpBool b) typ dir).
  Hypothesis HInt: forall t typ dir i, P (MkExpression t (ExpInt i) typ dir).
  Hypothesis HString: forall t typ dir s, P (MkExpression t (ExpString s) typ dir).
  Hypothesis HName: forall t typ dir n l, P (MkExpression t (ExpName n l) typ dir).
  Hypothesis HArrayAccess: forall t typ dir ary idx,
      P ary -> P idx -> P (MkExpression t (ExpArrayAccess ary idx) typ dir).
  Hypothesis HBitStringAccess: forall t typ dir bits lo hi,
      P bits -> P (MkExpression t (ExpBitStringAccess bits lo hi) typ dir).
  Hypothesis HList: forall t typ dir vs,
      Forall P vs -> P (MkExpression t (ExpList vs) typ dir).
  Hypothesis HRecord: forall t typ dir es,
      Forall (fun '(_,v) => P v) es -> P (MkExpression t (ExpRecord es) typ dir).
  Hypothesis HUnaryOp: forall t typ dir op arg,
      P arg -> P (MkExpression t (ExpUnaryOp op arg) typ dir).
  Hypothesis HBinaryOp: forall t typ dir op args,
      P (fst args) -> P (snd args) -> P (MkExpression t (ExpBinaryOp op args) typ dir).
  Hypothesis HCast: forall t typ1 dir typ expr,
      P expr -> P (MkExpression t (ExpCast typ expr) typ1 dir).
  Hypothesis HTypeMember: forall t typ1 dir typ name,
      P (MkExpression t (ExpTypeMember typ name) typ1 dir).
  Hypothesis HErrorMember: forall t typ dir n,
      P (MkExpression t (ExpErrorMember n) typ dir).
  Hypothesis HExpressionMember: forall t typ dir exp name,
      P exp -> P (MkExpression t (ExpExpressionMember exp name) typ dir).
  Hypothesis HTernary: forall t typ dir cond tru fls,
      P cond -> P tru -> P fls -> P (MkExpression t (ExpTernary cond tru fls) typ dir).
  Hypothesis HFunctionCall: forall t typ dir func type_args args,
      P func -> OptForall P args ->
      P (MkExpression t (ExpFunctionCall func type_args args) typ dir).
  Hypothesis HNamelessInstantiation: forall t typ1 dir typ args,
      Forall P args -> P (MkExpression t (ExpNamelessInstantiation typ args) typ1 dir).
  Hypothesis HDontCare: forall t typ dir, P (MkExpression t ExpDontCare typ dir).

  Fixpoint expr_ind (e: Expression): P e :=
    let fix lind (vs: list Expression): Forall P vs :=
      match vs with
      | nil => Forall_nil _
      | v :: rest => Forall_cons _ (expr_ind v) (lind rest)
      end in
    let fix alind (vs: P4String.AList tags_t Expression):
      Forall (fun '(_, v)=> P v) vs :=
      match vs with
      | nil => Forall_nil _
      | (_, v) as xv :: rest => Forall_cons xv (expr_ind v) (alind rest)
      end in
    let fix olind (vs: list (option Expression)): OptForall P vs :=
      match vs with
      | nil => OptForall_nil _
      | None :: rest => OptForall_cons_None _ _ (olind rest)
      | Some x :: rest => OptForall_cons_Some _ _ _ (expr_ind x) (olind rest)
      end in
    match e with
    | MkExpression t expr typ1 dir =>
        match expr with
        | ExpBool b => HBool t typ1 dir b
        | ExpInt i => HInt t typ1 dir i
        | ExpString s => HString t typ1 dir s
        | ExpName n l => HName t typ1 dir n l
        | ExpArrayAccess ary idx =>
            HArrayAccess t typ1 dir ary idx (expr_ind ary) (expr_ind idx)
        | ExpBitStringAccess bits lo hi =>
            HBitStringAccess t typ1 dir bits lo hi (expr_ind bits)
        | ExpList vs => HList t typ1 dir vs (lind vs)
        | ExpRecord es => HRecord t typ1 dir es (alind es)
        | ExpUnaryOp op e => HUnaryOp t typ1 dir op e (expr_ind e)
        | ExpBinaryOp op args =>
            HBinaryOp t typ1 dir op args (expr_ind (fst args)) (expr_ind (snd args))
        | ExpCast typ exp => HCast t typ1 dir typ exp (expr_ind exp)
        | ExpTypeMember s1 s2 => HTypeMember t typ1 dir s1 s2
        | ExpErrorMember s => HErrorMember t typ1 dir s
        | ExpExpressionMember exp s =>
            HExpressionMember t typ1 dir exp s (expr_ind exp)
        | ExpTernary cond tru fls =>
            HTernary t typ1 dir cond tru fls
                     (expr_ind cond) (expr_ind tru) (expr_ind fls)
        | ExpFunctionCall func type_args args =>
            HFunctionCall t typ1 dir func type_args args (expr_ind func) (olind args)
        | ExpNamelessInstantiation typ args =>
            HNamelessInstantiation t typ1 dir typ args (lind args)
        | ExpDontCare => HDontCare t typ1 dir
        end
    end.

End ExprInd.
