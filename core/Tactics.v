Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Value.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.Implies.
Require Import ProD3.core.ConcreteHoare.
Require Import ProD3.core.AssertionNotations.

(* solves hoare_call for built-in functions *)
Ltac forward_builtin :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      (eapply hoare_call_builtin';
        [ reflexivity (* is_no_dup *)
        | reflexivity (* eval_lexpr *)
        | reflexivity (* eval_args *)
        | reflexivity (* eval_builtin *)
        ])
      || fail "Not a built-in function"
  | _ =>
      fail "Not a hoare_call"
  end.

(* solves hoare_stmt *)
Ltac forward_stmt :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
      (* hoare_stmt_var_call' *)
      | MkStatement _
            (StatVariable _ _
                (Some (MkExpression _ (ExpFunctionCall ?func _ _) _ _))
                ?loc) _ =>
          lazymatch loc with
          | LInstance _ => idtac (* ok *)
          | LGlobal _ => fail "Cannot declacre a variable with LGlobal locator"
          | _ => fail "Unrecognized locator expression" loc
          end;
          eapply hoare_stmt_var_call';
            [ reflexivity (* is_call_expression *)
            | forward_builtin (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | forward_builtin (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_assign' *)
      | MkStatement _ (StatAssignment _ _) _ =>
          eapply hoare_stmt_assign';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_lexpr *)
            | reflexivity (* eval_expr *)
            | reflexivity (* eval_write *)
            ]
      | _ =>
          fail 0 stmt "is not supported"
      end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

(* forwards hoare_block *)
Ltac forward :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) ?block _ =>
      lazymatch block with
      | BlockEmpty _ => apply hoare_block_nil (* TODO *)
      | BlockCons _ _ =>
          eapply hoare_block_cons;
          only 1 : forward_stmt
      end
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) _ _)"
  end.

Ltac inv_func_copy_out :=
  lazymatch goal with
  | |- inv_func_copy_out _ _ _ =>
      repeat apply inv_func_copy_out_ex;
      apply inv_func_copy_out_base;
        [ reflexivity (* length (filter_out params) = length post_arg *)
        | reflexivity (* is_no_dup *)
        ]
  | _ => fail "The goal is not inv_func_copy_out"
  end.

Ltac inv_implicit_return :=
  lazymatch goal with
  | |- inv_implicit_return _ _ =>
      repeat apply inv_implicit_return_ex;
      first [
        apply inv_implicit_return_base1
      | apply inv_implicit_return_base2
      ]
  | _ => fail "The goal is not inv_implicit_return"
  end.

Ltac start_function :=
  lazymatch goal with
  | |- hoare_func _ _ _ _ _ ?post =>
      eapply hoare_func_internal';
        [ reflexivity (* length (filter_in params) = length pre_arg *)
        | reflexivity (* is_no_dup *)
        | reflexivity (* eval_write_vars *)
        | idtac (* hoare_block *)
        | inv_func_copy_out (* inv_func_copy_out *)
        | inv_implicit_return
        ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ (ARG _ (MEM _ (EXT _))) _ _"
    "(EX ... ARG_RET _ (MEM _ (EXT _)))"
  end.

Ltac entailer :=
  lazymatch goal with
  | |- implies _ _ =>
      first [
        eapply implies_simplify;
          [ reflexivity (* mem_implies_simplify *)
          | idtac
          | reflexivity (* ext_implies_simplify *)
          | idtac
          ]
      | eapply implies_simplify_ret;
          [ idtac (* retv *)
          | reflexivity (* mem_implies_simplify *)
          | idtac
          | reflexivity (* ext_implies_simplify *)
          | idtac
          ]
      ]
  | _ => fail "The goal is not an entailment"
  end.
