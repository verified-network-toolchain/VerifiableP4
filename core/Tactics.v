Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.Implies.
Require Import ProD3.core.ConcreteHoare.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Modifies.
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.DisjointTest.
Import ListNotations.

(* solves hoare_call for built-in functions *)
Ltac step_builtin :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      (eapply hoare_call_builtin';
        [ reflexivity (* is_no_dup *)
        | reflexivity (* eval_lexpr *)
        | reflexivity (* eval_args *)
        | reflexivity (* eval_builtin *)
        ])
      || fail "Not a built-in function. Use step_call instead"
  | _ =>
      fail "Not a hoare_call"
  end.

(* solves hoare_stmt *)
Ltac step_stmt :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
      (* Note that call expressions must be matched first. *)
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | step_builtin (* hoare_call *)
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
      (* hoare_stmt_method_call' *)
      | MkStatement _ (StatMethodCall ?func _ _) _ =>
          eapply hoare_stmt_method_call';
            step_builtin (* hoare_call *)
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
            | step_builtin (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_var' *)
      | MkStatement _ (StatVariable _ _ (Some _) ?loc) _ =>
          lazymatch loc with
          | LInstance _ => idtac (* ok *)
          | LGlobal _ => fail "Cannot declacre a variable with LGlobal locator"
          | _ => fail "Unrecognized locator expression" loc
          end;
          eapply hoare_stmt_var';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_expr *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_var_none' *)
      | MkStatement _ (StatVariable _ _ None ?loc) _ =>
          lazymatch loc with
          | LInstance _ => idtac (* ok *)
          | LGlobal _ => fail "Cannot declacre a variable with LGlobal locator"
          | _ => fail "Unrecognized locator expression" loc
          end;
          eapply hoare_stmt_var_none';
            [ reflexivity (* is_no_dup *)
            | reflexivity (* get_real_type *)
            | reflexivity (* uninit_sval_of_typ *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_direct_application' *)
      | MkStatement _ (StatDirectApplication _ _ _) _ =>
          fail "Use step_call instead"
      | MkStatement _ (StatBlock _) _ =>
          eapply hoare_stmt_block
      | _ =>
          fail 0 stmt "is not supported"
      end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

(* steps hoare_block *)
Ltac step :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) ?block _ =>
      lazymatch block with
      | BlockEmpty _ => apply hoare_block_nil
      | BlockCons _ _ =>
          eapply hoare_block_cons;
          only 1 : step_stmt
      end
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      step_stmt
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) (BlockCons _ _) _)"
              "or (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

Ltac step_stmt_if :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
        | MkStatement _ (StatConditional _ _ _) _ =>
            eapply hoare_stmt_if';
              [ reflexivity (* eval_expr *)
              | intro (* true branch *)
              | intro (* false branch *)
              ]
        | _ => fail "The next statement is not an if-statement"
        end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

Ltac step_if_post post :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) (BlockCons ?stmt _) _ =>
      lazymatch stmt with
      | MkStatement _ (StatConditional _ _ _) _ =>
          eapply hoare_block_cons with (mid := post);
          [ step_stmt_if
          | idtac
          ]
      | _ => fail "The next statement is not an if-statement"
      end
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) (BlockCons _ _) _)"
  end.

Tactic Notation "step_if" constr(post) := step_if_post post.

Ltac step_if_no_post :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) (BlockCons ?stmt (BlockEmpty _)) _ =>
      eapply hoare_block_cons;
      [ step_stmt_if
      | eapply hoare_block_nil, implies_refl
      ]
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      step_stmt_if
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) (BlockCons _ _) _)"
              "or (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

Tactic Notation "step_if" := step_if_no_post.

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

Create HintDb func_specs.

Ltac intros_fs_bind :=
  repeat lazymatch goal with
  | |- fundef_satisfies_spec _ _ _ (fs_bind (fun x => _)) =>
    let x := fresh x in intro x
  | |- fundef_satisfies_spec _ _ _ ?x =>
    unfold x
  end.

Ltac intros_fsh_bind :=
  repeat lazymatch goal with
  | |- fundef_satisfies_hoare _ _ _ _ (fsh_bind (fun x => _)) =>
    let x := fresh x in intro x
  | |- fundef_satisfies_hoare _ _ _ _ ?x =>
    unfold x
  end.

Ltac solve_modifies :=
  first [
    solve [eauto 100 with nocore modifies]
  | idtac "The modifies clause cannot be solved automatically."
  ].

Ltac init_function :=
  intros_fsh_bind;
  unfold fundef_satisfies_hoare;
  (* handle hoare_func *)
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

Ltac start_function :=
  lazymatch goal with
  | |- fundef_satisfies_spec _ _ _ ?spec =>
      intros_fs_bind;
      split; [init_function | solve_modifies]
  | _ => fail "The goal is not in the form of (fundef_satisfies_spec _ _ _)"
  end.

Ltac step_call_func func_spec :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      eapply hoare_call_func'_ex;
        [ reflexivity (* is_builtin_func *)
        | reflexivity (* eval_args *)
        | reflexivity (* lookup_func *)
        | (* func_spec *)
          eapply func_spec_combine';
            (* Issue: error message is hard to track when func_spec is not a func spec for the function. *)
            [ eapply func_spec
            | idtac
            | reflexivity (* exclude *)
              (* This is dangerous if there are other evars. *)
            | instantiate (2 := ltac:(test_ext_exclude)); reflexivity (* exclude_ext *)
            | solve [repeat constructor] (* func_post_combine *)
            ]
        | solve [repeat constructor] (* hoare_call_func_ex_layer *)
        ]
  | _ => fail "The goal is not in the form of (hoare_call _ _ _ _ _)"
  end.

Ltac step_stmt_call func_spec :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | step_call_func func_spec (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_method_call' *)
      | MkStatement _ (StatMethodCall ?func _ _) _ =>
          eapply hoare_stmt_method_call'_ex;
            [ step_call_func func_spec (* hoare_call *)
            | solve [repeat constructor] (* hoare_stmt_method_call_ex_layer *)
            ]
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
            | step_call_func func_spec (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_direct_application' *)
      | MkStatement _ (StatDirectApplication _ _ _) _ =>
          eapply hoare_stmt_direct_application';
            step_call_func func_spec (* hoare_call *)
      | _ => fail "This function call is not supported"
      end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _)"
  end.

Ltac step_call_tac func_spec :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) ?block _ =>
      lazymatch block with
      | BlockEmpty _ => apply hoare_block_nil
      | BlockCons _ _ =>
          eapply hoare_block_cons;
          only 1 : step_stmt_call func_spec
      end
  | |- hoare_stmt _ _ _ _ _ =>
      step_stmt_call func_spec
  | |- hoare_call _ _ _ _ _ =>
      eapply hoare_call_post;
      only 1 : step_call_func func_spec
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) _ _)"
  end.

(* We use a fancy hack here. The function body lemma has form
      forall x_1, ..., x_n,
        (forall y_1, ..., y_m,
          hoare_func ...)
        /\
        (func_modifies ...).
  The lemma func_spec_combine' expects a proof for
      (hoare_func ...)
      /\
      (func_modifies ...).
  The variables x_1, ..., x_n are epxected to be resolved automatically.
  But user might need to supply some of y_1, ..., y_m. So we generate a
  proof in the second form with from user supplied lemma and variables in
  the following tactics, and then call step_call_tac. *)

Ltac process_func_body func_spec callback1 callback2 :=
  let func_body := fresh "func_body" in
  pose proof (func_body := func_spec);
  let func_body1 := fresh "func_body1" in
  let func_body2 := fresh "func_body2" in
  edestruct func_body as [func_body1 func_body2];
  try clear func_body;
  [ .. |
    unshelve(
      callback1 func_body func_body1 func_body2;
      (* Examine the type of func_body *)
      lazymatch type of func_body with
      | hoare_func _ _ _ _ _ _ /\ func_modifies _ _ _ _ _ =>
          idtac
      | fundef_satisfies_hoare _ _ _ _ _ /\ func_modifies _ _ _ _ _ =>
          idtac
      end;
      callback2 func_body
    )];
  shelve_unifiable;
  try clear func_body;
  try clear func_body1;
  try clear func_body2.

Ltac step_call_wrapper func_spec callback1 :=
  process_func_body func_spec callback1 step_call_tac.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) uconstr(x6) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5 x6) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5) func_body2))
  || step_call func_spec x1 x2 x3 x4 x5 _.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4) func_body2))
  || step_call func_spec x1 x2 x3 x4 _.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3) func_body2))
  || step_call func_spec x1 x2 x3 _.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2) func_body2))
  || step_call func_spec x1 x2 _.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1) func_body2))
  || step_call func_spec x1 _.

Tactic Notation "step_call" uconstr(func_spec) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj func_body1 func_body2))
  || step_call func_spec _.

(* Tactics for step into a function call, instead of using a function spec.
  They may need some refactoring. *)

Ltac step_into_call_func :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      eapply hoare_call_func';
        [ reflexivity (* is_builtin_func *)
        | reflexivity (* eval_args *)
        | reflexivity (* lookup_func *)
        | (* step into function body *)
        | (* reflexivity *) (* is_no_dup *)
        | (* reflexivity *) (* eval_call_copy_out *)
        ]
  | _ => fail "The goal is not in the form of (hoare_call _ _ _ _ _)"
  end.

Ltac step_stmt_into_call :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | step_into_call_func (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_method_call' *)
      | MkStatement _ (StatMethodCall ?func _ _) _ =>
          eapply hoare_stmt_method_call';
            step_into_call_func (* hoare_call *)
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
            | step_into_call_func (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_write *)
            ]
      (* hoare_stmt_direct_application' *)
      | MkStatement _ (StatDirectApplication _ _ _) _ =>
          eapply hoare_stmt_direct_application';
            step_into_call_func (* hoare_call *)
      | _ => fail "This function call is not supported"
      end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _)"
  end.

Ltac step_into_call :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) (BlockCons ?stmt _) _ =>
      eapply hoare_block_cons;
      [ step_stmt_into_call
      | eapply hoare_block_nil
      ]
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      step_stmt_into_call
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) (BlockCons _ _) _)"
              "or (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

(* Handles table when we have a particular case. *)
Ltac hoare_func_table_case :=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_case'; (* hoare_table_match *)
        [ reflexivity (* eval_exprs *)
        | reflexivity (* lift_option (.. keysvals) *)
        | eapply hoare_table_entries_intros; (* hoare_table_entries *)
          repeat econstructor
        | reflexivity (* extern_match *)
        ]
      | reflexivity (* get_table_call *)
      | idtac
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end.

(* Handles table with constant entries. *)
Ltac hoare_func_table :=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_list_intro'; (* hoare_table_match_list *)
        [ reflexivity (* eval_exprs *)
        | reflexivity (* lift_option (.. keysvals) *)
        | eapply hoare_table_entries_intros; (* hoare_table_entries *)
          repeat econstructor
        | idtac (* hoare_extern_match_list *)
        ]
      | idtac (* Forall (hoare_table_match_case_valid' ...) *)
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end.

Ltac Forall2_sval_refine :=
  lazymatch goal with
  | |- Forall2 sval_refine _ _ =>
      first [
        apply Forall2_nil
      | apply Forall2_cons;
        [ try apply sval_refine_refl
        | Forall2_sval_refine
        ]
      ]
  | _ => fail "The goal is not in the form of (Forall2 sval_refine _ _)"
  end.

Ltac Forall_uncurry_sval_refine :=
  lazymatch goal with
  | |- Forall (uncurry sval_refine) _ =>
      first [
        apply Forall_nil
      | apply Forall_cons;
        [ try apply sval_refine_refl
        | Forall_uncurry_sval_refine
        ]
      ]
  | _ => fail "The goal is not in the form of (Forall (uncurry sval_refine) _)"
  end.

Ltac Forall_uncurry_eq :=
  lazymatch goal with
  | |- Forall (uncurry eq) _ =>
      first [
        apply Forall_nil
      | apply Forall_cons;
        [ try reflexivity
        | Forall_uncurry_eq
        ]
      ]
  | _ => fail "The goal is not in the form of (Forall (uncurry eq) _)"
  end.

Ltac entailer :=
  lazymatch goal with
  | |- implies _ _ =>
      first [
        eapply implies_simplify;
          [ reflexivity (* mem_implies_simplify *)
          | Forall_uncurry_sval_refine
          | simpl_ext_implies
          ]
      ]
  | |- arg_implies _ _ =>
      first [
        eapply arg_implies_simplify;
          [ Forall2_sval_refine
          | reflexivity (* mem_implies_simplify *)
          | Forall_uncurry_sval_refine
          | simpl_ext_implies
        ]
      ]
  | |- ret_implies _ _ =>
      first [
        eapply ret_implies_simplify;
          [ try apply sval_refine_refl
          | reflexivity (* mem_implies_simplify *)
          | Forall_uncurry_sval_refine
          | simpl_ext_implies
        ]
      ]
  | |- arg_ret_implies _ _ =>
      first [
        eapply arg_ret_implies_simplify;
          [ Forall2_sval_refine
          | try apply sval_refine_refl
          | reflexivity (* mem_implies_simplify *)
          | Forall_uncurry_sval_refine
          | simpl_ext_implies
        ]
      ]
  | |- ext_implies _ _ =>
      simpl_ext_implies
  | _ => fail "The goal is not an entailment"
  end.

Tactic Notation "Intros" simple_intropattern(x) :=
  lazymatch goal with
  | |- hoare_block _ _ (assr_exists _) _ _ =>
      eapply hoare_block_pre_ex;
      intros x
  | _ =>
      fail "There is nothing to Intro."
  end.

Ltac normalize_EXT :=
  repeat rewrite AssertionLang.ext_pred_and_cons;
  repeat rewrite AssertionLang.ext_pred_wrap_cons.

(* Term-generating tactics *)

(* We need to specify the type of ge to prevent target from being unfolded in the type of ge. *)
Ltac get_am_ge prog :=
  let ge := eval compute -[PathMap.empty PathMap.set] in (gen_am_ge prog) in
  exact (ge : (@genv _ ltac:(typeclasses eauto))).

Ltac get_ge am_ge prog :=
  let ge := eval compute -[am_ge PathMap.empty PathMap.set] in (gen_ge' am_ge prog) in
  exact (ge : (@genv _ ltac:(typeclasses eauto))).

Definition dummy_fundef {tags_t} : @fundef tags_t := FExternal "" "".
Opaque dummy_fundef.

Ltac get_fd p ge :=
  let fd := eval compute in (force dummy_fundef (PathMap.get p (ge_func ge))) in
  exact fd.
