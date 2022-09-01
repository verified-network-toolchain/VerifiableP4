Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.Implies.
Require Import ProD3.core.EvalExpr.
Require Import ProD3.core.ConcreteHoare.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Modifies.
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.DisjointTest.
Require Import ProD3.core.ExtExtract.
Import ListNotations.

Ltac simpl_eval_p4int_sval1 :=
  lazymatch goal with
  | |- context [eval_p4int_sval ?i] =>
      (* We want to make sure i does not contain (opaque) variables. *)
      let v := eval compute in (P4Int.value i) in
      let ws := eval compute in (P4Int.width_signed i) in
      lazymatch ws with
      | Some (?w, true) =>
          change (eval_p4int_sval i) with (P4Int w v)
      | Some (?w, false) =>
          change (eval_p4int_sval i) with (P4Bit w v)
      | None =>
          change (eval_p4int_sval i) with (ValBaseInteger v)
      end
  | H : context [eval_p4int_sval ?i] |- _ =>
      revert H;
      simpl_eval_p4int_sval1;
      intro H
  end.

Ltac simpl_eval_p4int_sval :=
  repeat simpl_eval_p4int_sval1.

(* Experimental: use cbn to simplify update, get, eval_write_vars, etc. *)
Ltac simpl_assertion :=
  cbn [
    (* First, most basic definitions for comparison. *)
    bool_rect bool_rec Bool.bool_dec Ascii.ascii_rect Ascii.ascii_rec Ascii.ascii_dec sumbool_rect
    sumbool_rec string_rect string_rec string_dec EquivUtil.StringEqDec EquivDec.equiv_dec EquivDec.list_eqdec

    is_some isSome

    P4String.str

    app find find

    fst snd force map lift_option

    lift_option_kv kv_map

    AList.set AList.set_some AList.get

    filter_in Semantics.is_in flat_map

    eval_write_vars fold_left eval_write_var AList.set_some combine

    Members.update Members.get].

Ltac simpl_abs_ops :=
  autorewrite with abs_ops.

Ltac simpl_eval_expr := simpl_eval_p4int_sval; simpl_assertion; simpl_abs_ops.

Ltac eval_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ = Some _ => idtac
  | |- eval_args _ _ _ _ _ = Some _ => idtac
  | _ => fail "eval_expr: unexpected goal"
  end;
  eapply eq_trans with (y := Some _);
  only 1 : (reflexivity || fail "Failed to evaluate an expression. It could be because a variable is missing in the assertion");
  simpl_eval_expr;
  reflexivity.

Ltac simpl_eval_write := simpl_assertion.

Ltac eval_write :=
  lazymatch goal with
  | |- eval_write _ _ _ = Some _ => idtac
  | _ => fail "eval_write: unexpected goal"
  end;
  eapply eq_trans with (y := Some _);
  only 1 : (reflexivity || fail "Failed to evaluate a writing. It could be because a variable is missing in the assertion");
  simpl_eval_expr;
  reflexivity.

(* solves hoare_call for built-in functions *)
Ltac step_builtin :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      (eapply hoare_call_builtin';
        [ reflexivity (* is_no_dup *)
        | reflexivity (* eval_lexpr *)
        | eval_expr (* eval_args *)
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
      | MkStatement _ StatEmpty _ =>
          apply hoare_stmt_empty
      | empty_statement =>
          apply hoare_stmt_empty
      (* Note that call expressions must be matched first. *)
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | step_builtin (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | eval_write (* eval_write *)
            ]
      (* hoare_stmt_assign' *)
      | MkStatement _ (StatAssignment _ _) _ =>
          eapply hoare_stmt_assign';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* is_no_dup *)
            | reflexivity (* eval_lexpr *)
            | eval_expr (* eval_expr *)
            | eval_write (* eval_write *)
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
            | eval_write (* eval_write *)
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
            | eval_expr (* eval_expr *)
            | eval_write (* eval_write *)
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
            | eval_write (* eval_write *)
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
              [ eval_expr (* eval_expr *)
              | intro (* true branch *)
              | intro; simpl (force empty_statement _) (* false branch *)
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
  (* Use H for nameless bindings. *)
  | |- func_sound _ _ _ (fs_bind (fun H => _)) =>
    let x := fresh H in intro x
  | |- func_sound _ _ _ ?x =>
    unfold x
  end.

Ltac intros_fsh_bind :=
  repeat lazymatch goal with
  (* Use H for nameless bindings. *)
  | |- fundef_satisfies_hoare _ _ _ _ (fsh_bind (fun H => _)) =>
    let x := fresh H in intro x
  | |- fundef_satisfies_hoare _ _ _ _ ?x =>
    unfold x
  end.

Ltac solve_modifies :=
  first [
    solve [eauto 100 with nocore modifies]
  | idtac "The modifies clause cannot be solved automatically."
  ].

(* This is quite special case handling. *)
Ltac simplify_lift_option_eval_sval_to_val :=
  simpl Members.get;
  cbn [map];
  repeat rewrite eval_sval_to_val_P4Bit.

(* Handles table when we have a particular case. *)
Ltac hoare_func_table_case :=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_case'; (* hoare_table_match *)
        [ reflexivity (* eval_exprs *)
        | simplify_lift_option_eval_sval_to_val; (* lift_option (.. keysvals) *)
          reflexivity
        | eapply hoare_table_entries_intros; (* hoare_table_entries *)
          repeat econstructor
        | reflexivity (* extern_match *)
        ]
      | reflexivity (* get_table_call *)
      | idtac
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end.

(* Provided by the target. *)
Ltac hoare_extern_match_list :=
  idtac.

(* Handles table with constant entries. *)
Ltac hoare_func_table :=
  lazymatch goal with
  | |- hoare_func _ _ _ (FTable _ _ _ _ _) _ _ =>
      eapply hoare_func_table';
      [ eapply hoare_table_match_list_intro'; (* hoare_table_match_list *)
        [ reflexivity (* eval_exprs *)
        | simplify_lift_option_eval_sval_to_val; (* lift_option (.. keysvals) *)
          reflexivity
        | eapply hoare_table_entries_intros; (* hoare_table_entries *)
          repeat first [
            simple apply sval_to_val_eval_p4int_sval
          | econstructor
          ]
        | hoare_extern_match_list (* hoare_extern_match_list *)
        ]
      | idtac (* hoare_table_action_cases' *)
      ]
  | _ => fail "The goal is not in the form of (hoare_func _ _ _ (FTable _ _ _ _ _) _ _)"
  end.

Ltac init_function :=
  intros_fsh_bind;
  unfold fundef_satisfies_hoare;
  (* handle hoare_func *)
  lazymatch goal with
  | |- hoare_func _ _ _ ?fd _ ?post =>
    try unfold fd;
    lazymatch goal with
    | |- hoare_func _ _ _ ?fd _ ?post =>
      lazymatch fd with
      | FInternal _ _ =>
          eapply hoare_func_internal';
          [ reflexivity (* length (filter_in params) = length pre_arg *)
          | reflexivity (* is_no_dup *)
          | reflexivity (* eval_write_vars *)
          | idtac (* hoare_block *)
          | inv_func_copy_out (* inv_func_copy_out *)
          | inv_implicit_return (* inv_implicit_return *)
          ]
      | FTable _ _ _ _ _ =>
          hoare_func_table
      end
    end
  | _ => fail "The goal is not in the form of (hoare_func _ _ (ARG _ (MEM _ (EXT _))) _ _"
           "(EX ... ARG_RET _ (MEM _ (EXT _)))"
  end.

Ltac start_function :=
  lazymatch goal with
  | |- func_sound _ _ _ ?spec =>
      intros_fs_bind;
      split; [init_function | solve_modifies]
  | _ => fail "The goal is not in the form of (func_sound _ _ _)"
  end.

(* This is very experimental. It gets the next case from hoare_table_action_cases'. *)
Ltac next_case :=
  lazymatch goal with
  | |- hoare_table_action_cases' _ _ _ _ _ _ _ =>
      first [
        apply hoare_table_action_cases'_nil
      | apply hoare_table_action_cases'_cons;
        let H := fresh in
        intro H; try solve [inv H]
      ]
  | _ =>
      fail "The goal is not in the form of (hoare_table_action_cases' _ _ _ _ _ _ _)"
  end.

Ltac step_call_func func_spec :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      eapply hoare_call_func'_ex;
        [ reflexivity (* is_builtin_func *)
        | eval_expr (* eval_args *)
        | reflexivity (* lookup_func *)
        | (* func_spec *)
          eapply func_spec_combine';
            (* Issue: error message is hard to track when func_spec is not a func spec for the function. *)
            [ eapply func_spec
            | simpl_assertion
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
            | eval_write (* eval_write *)
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
            | eval_write (* eval_write *)
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
            [step_stmt_call func_spec | simpl_assertion]
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
      try clear func_body1;
      try clear func_body2;
      (* Examine the type of func_body *)
      repeat lazymatch type of func_body with
      | hoare_func _ _ _ _ _ _ /\ func_modifies _ _ _ _ _ =>
          idtac
      | fundef_satisfies_hoare _ _ _ _ (fsh_base _ _) /\ func_modifies _ _ _ _ _ =>
          idtac
      | _ =>
          first [
            let func_body1 := fresh "func_body1" in
            let func_body2 := fresh "func_body2" in
            destruct func_body as [func_body1 func_body2];
            epose proof (func_body := conj (func_body1 _) func_body2);
            clear func_body1 func_body2
          | fail 2 "Cannot process the body proof"
          ]
      end;
      callback2 func_body;
      (* Put the entailment goal last *)
      cycle 1
    )];
  shelve_unifiable;
  (* Put the entailment goal first *)
  cycle -1;
  try clear func_body.

Ltac step_call_wrapper func_spec callback1 :=
  process_func_body func_spec callback1 step_call_tac.

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) uconstr(x9) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5 x6 x7 x8 x9) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5 x6 x7 x8) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) uconstr(x6) uconstr(x7) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5 x6 x7) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) uconstr(x6) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5 x6) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) uconstr(x5) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4 x5) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3 x4) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) uconstr(x3) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2 x3) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) uconstr(x2) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1 x2) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) uconstr(x1) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj (func_body1 x1) func_body2)).

Tactic Notation "step_call" uconstr(func_spec) :=
  step_call_wrapper func_spec
    ltac:(fun func_body func_body1 func_body2 =>
      epose proof (func_body := conj func_body1 func_body2)).

(* This is very experimental. It reduces hoare_table_action_case'. *)
Ltac table_action spec :=
  lazymatch goal with
  | |- hoare_table_action_case' _ _ _ _ _ _ _ =>
      econstructor;
      [ reflexivity (* get_table_call *)
      | step_call spec; (* hoare_call *)
        [ .. | apply ret_implies_refl]
      | repeat constructor (* hoare_table_action_ex_layer *)
      | (* arg_ret_implies *)
      ]
  | _ =>
      fail "The goal is not in the form of (hoare_table_action_case' _ _ _ _ _ _ _)"
  end.

(* Tactics for step into a function call, instead of using a function spec.
  They may need some refactoring. *)

Ltac step_call_into :=
  lazymatch goal with
  | |- hoare_call _ _ _ _ _ =>
      eapply hoare_call_func';
        [ reflexivity (* is_builtin_func *)
        | eval_expr (* eval_args *)
        | reflexivity (* lookup_func *)
        | (* step into function body *)
        | (* reflexivity *) (* is_no_dup *)
        | (* reflexivity *) (* eval_call_copy_out *)
        ]
  | _ => fail "The goal is not in the form of (hoare_call _ _ _ _ _)"
  end.

Ltac step_stmt_into :=
  lazymatch goal with
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      lazymatch stmt with
      (* hoare_stmt_assign_call' *)
      | MkStatement _ (StatAssignment _ (MkExpression _ (ExpFunctionCall ?func _ _) _ _)) _ =>
          eapply hoare_stmt_assign_call';
            [ reflexivity (* is_call_expression *)
            | reflexivity (* eval_lexpr *)
            | step_call_into (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | eval_write (* eval_write *)
            ]
      (* hoare_stmt_method_call' *)
      | MkStatement _ (StatMethodCall ?func _ _) _ =>
          eapply hoare_stmt_method_call';
            step_call_into (* hoare_call *)
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
            | step_call_into (* hoare_call *)
            | reflexivity (* is_no_dup *)
            | eval_write (* eval_write *)
            ]
      (* hoare_stmt_direct_application' *)
      | MkStatement _ (StatDirectApplication _ _ _) _ =>
          eapply hoare_stmt_direct_application';
            step_call_into (* hoare_call *)
      | _ => fail "This function call is not supported"
      end
  | _ => fail "The goal is not in the form of (hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _)"
  end.

Ltac step_into_no_post :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) (BlockCons ?stmt (BlockEmpty _)) _ =>
      eapply hoare_block_cons;
      [ step_stmt_into
      | eapply hoare_block_nil
      ]
  | |- hoare_stmt _ _ (MEM _ (EXT _)) ?stmt _ =>
      step_stmt_into
  | _ => fail "The goal is not in the form of (hoare_block _ _ (MEM _ (EXT _)) (BlockCons _ _) _)"
              "or (hoare_stmt _ _ (MEM _ (EXT _)) _ _)"
  end.

Tactic Notation "step_into" := step_into_no_post.

Tactic Notation "step_into" constr(post) := fail "unimplemented".

(* Refine function tactics. *)

Ltac refine_function_hoare func_spec :=
  intros_fsh_bind;
  eapply hoare_func_post;
  only 1 : (
    eapply hoare_func_pre;
    only 2 : apply func_spec
  ).

Ltac refine_function func_spec :=
  lazymatch goal with
  | |- func_sound _ _ _ ?spec =>
      intros_fs_bind;
      split;
        [ refine_function_hoare func_spec
        | apply func_spec ||
            (eapply func_modifies_frame;
            only 1 : apply func_spec;
            solve_modifies)
        ]
  | _ => fail "The goal is not in the form of (func_sound _ _ _)"
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
        repeat (apply arg_ret_implies_post_ex; eexists);
        [.. |
          eapply arg_ret_implies_simplify;
            [ Forall2_sval_refine
            | try apply sval_refine_refl
            | reflexivity (* mem_implies_simplify *)
            | Forall_uncurry_sval_refine
            | simpl_ext_implies
          ]
        ]
      ]
  | |- ext_implies _ _ =>
      simpl_ext_implies
  | _ => fail "The goal is not an entailment"
  end.

(* Assertion manipulation *)

(* Need to improve efficiency. *)
Ltac normalize_EXT :=
  repeat rewrite AssertionLang.ext_pred_and_cons;
  repeat rewrite AssertionLang.ext_pred_wrap_cons.

Ltac extract_ex_in_EXT a :=
  lazymatch a with
  | MEM _ (EXT ?a_ext) =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (extract_nth_ext_ex' n' _ a_ext A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Ltac extract_nth_ext_ex_ext_implies_pre a :=
  lazymatch a with
  | ?a_ext =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      apply (extract_nth_ext_ex_ext_implies_pre n' a_ext _ A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Tactic Notation "Intros" simple_intropattern(x) :=
  lazymatch goal with
  | |- hoare_block _ _ (assr_exists _) _ _ =>
      eapply hoare_block_pre_ex;
      intros x
  | |- hoare_block _ _ ?pre _ _ =>
      extract_ex_in_EXT pre;
      eapply hoare_block_pre_ex;
      intro x
  | |- ext_implies ?pre _ =>
      extract_nth_ext_ex_ext_implies_pre pre;
      intro x
  | _ =>
      fail "There is nothing to Intro"
  end.

Ltac extract_ex_in_EXT_ext_implies_post a :=
  lazymatch a with
  | ?a_ext =>
    lazymatch a_ext with context [(ExtPred.ex (A := ?A) ?S _ _) :: ?a_ext'] =>
      let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      apply (extract_nth_ext_ex_ext_implies_post n' _ a_ext A S _ _ eq_refl);
      unfold replace_nth at 1
    end
  end.

Ltac Exists x:=
  lazymatch goal with
  | |- ext_implies ?pre ?post =>
      extract_ex_in_EXT_ext_implies_post post;
      exists x
  end.

Ltac extract_prop_in_EXT a_ext :=
  lazymatch a_ext with context [(ExtPred.prop ?S) :: ?a_ext'] =>
    let n := constr:((length a_ext - Datatypes.S (length a_ext'))%nat) in
    let n' := eval lazy beta zeta iota delta in n in
    rewrite (extract_nth_ext_prop n' a_ext S eq_refl);
    unfold remove_nth at 1
  end.

Ltac Intros_prop :=
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT ?pre)) _ _ =>
      extract_prop_in_EXT pre;
      eapply hoare_block_pre_ext_prop;
      intros ?H
  | |- ext_implies ?pre _ =>
      extract_prop_in_EXT pre;
      eapply ext_implies_pre_prop;
      intros ?H
  end.

Ltac P4assert Q :=
  lazymatch type of Q with
  | Prop => idtac
  | _ => fail 0 Q "is not a Prop"
  end;
  lazymatch goal with
  | |- hoare_block _ _ (MEM _ (EXT _)) _ _ =>
      apply hoare_block_assert_Prop with (P := Q);
      only 2 : intros ?H
  | |- ext_implies _ _ =>
      apply ext_implies_assert_Prop with (P := Q);
      only 2 : intros ?H
  | _ => fail 0 "The goal is not supported"
  end.

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
