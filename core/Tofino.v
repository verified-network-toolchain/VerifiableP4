Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Core.
Require Export ProD3.core.TofinoSpec.

#[export] Instance target : @Target Info (@Expression Info) := Tofino.

(* It is a hack to make extern_match opauqe. But it should be fine. *)

Ltac get_am_ge prog ::=
  let ge := eval compute -[PathMap.empty PathMap.set extern_match] in (gen_am_ge prog) in
  exact (ge : (@genv _ target)).

Ltac get_ge am_ge prog ::=
  let ge := eval compute -[am_ge PathMap.empty PathMap.set extern_match] in (gen_ge' am_ge prog) in
  exact (ge : (@genv _ target)).

Ltac get_init_es am_ge prog :=
  let init_es := eval compute -[am_ge PathMap.empty PathMap.set extern_match] in (gen_init_es' am_ge prog) in
  exact (init_es : (@Target.extern_state _ _ (@extern_sem _ _ target))).

Ltac get_am_fd ge am_ge p :=
  let am_sem := eval compute -[am_ge extern_match] in
    (force dummy_env_object (PathMap.get p (ge_ext ge))) in
  lazymatch am_sem with
  | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
      exact fd
  end.

Ltac get_fd p ge ::=
  let fd := eval compute -[extern_match] in (force dummy_fundef (PathMap.get p (ge_func ge))) in
  exact fd.

Ltac get_ext_obj p ge :=
  let ext_obj := eval compute -[extern_match] in
    (force dummy_env_object (PathMap.get p (ge_ext ge))) in
  exact ext_obj.

Ltac auto_regact ge am_ge p :=
  (* get r *)
  let r := eval compute in (PathMap.get p (ge_ext ge)) in
  let r := lazymatch r with (Some (Tofino.EnvRegAction ?r)) => r end in
  (* get (index_w, typ, s) *)
  let s := eval compute in (PathMap.get r (ge_ext ge)) in
  let index_w := lazymatch s with (Some (Tofino.EnvRegister (?index_w, _, _))) => index_w end in
  let typ := lazymatch s with (Some (Tofino.EnvRegister (_, ?typ, _))) => typ end in
  let s := lazymatch s with (Some (Tofino.EnvRegister (_, _, ?s))) => s end in
  (* get w *)
  let w := lazymatch typ with TypBit ?w => w | _ => fail 0 typ "is unsupported" end in
  (* get apply_fd *)
  let am_sem := eval compute -[am_ge extern_match] in
    (force dummy_env_object (PathMap.get (p ++ ["apply"]) (ge_ext ge))) in
  let apply_fd :=
    lazymatch am_sem with Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) => fd end in
  (* pose the sigma type term H *)
  let H := fresh in
  unshelve epose (_ : sigT (fun f => (sig (fun retv =>
    func_sound am_ge apply_fd nil
      (RegisterAction_apply_spec p (fun i => ValBaseBit (P4Arith.to_lbool w i)) f retv))))) as H;
  (* build H *)
  only 1 : (
    do 2 eexists;
    start_function;
    lazymatch goal with
    | |- context [eval_val_to_sval (ValBaseBit (P4Arith.to_lbool w ?old_value))] =>
        change (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool w old_value)))
          with (P4Bit w old_value)
    end;
    repeat step;
    entailer
  );
  let body_H := eval unfold H in H in
  lazymatch body_H with
  | existT _ ?f (exist _ ?retv ?H') =>
      exact (H' : func_sound _ _ _
        (RegisterAction_apply_spec p (fun i => ValBaseBit (P4Arith.to_lbool w i)) f retv))
  end.

Ltac build_execute_body ge body :=
  (* get spec from body *)
  lazymatch type of body with
  | func_sound ?am_ge ?fd _ ?spec =>
    (* unfold spec *)
    let spec :=
      lazymatch spec with
      | RegisterAction_apply_spec _ _ _ _ =>
          spec
      | RegisterAction_apply_spec' _ _ _ _ _ =>
          spec
      | _ =>
          eval unfold spec in spec
      end in
    lazymatch spec with
    | RegisterAction_apply_spec' ?p ?valid ?repr ?f ?retv =>
        let r := eval compute in (PathMap.get p (ge_ext ge)) in
        let r := lazymatch r with (Some (Tofino.EnvRegAction ?r)) => r end in
        let s := eval compute in (PathMap.get r (ge_ext ge)) in
        let index_w := lazymatch s with (Some (Tofino.EnvRegister (?index_w, _, _))) => index_w end in
        let typ := lazymatch s with (Some (Tofino.EnvRegister (_, ?typ, _))) => typ end in
        let s := lazymatch s with (Some (Tofino.EnvRegister (_, _, ?s))) => s end in
        exact (RegisterAction_execute_body' ge am_ge _ p index_w typ s r eq_refl eq_refl ltac:(lia)
          fd valid repr f retv eq_refl body)
    | RegisterAction_apply_spec ?p ?repr ?f ?retv =>
        let r := eval compute in (PathMap.get p (ge_ext ge)) in
        let r := lazymatch r with (Some (Tofino.EnvRegAction ?r)) => r end in
        let s := eval compute in (PathMap.get r (ge_ext ge)) in
        let index_w := lazymatch s with (Some (Tofino.EnvRegister (?index_w, _, _))) => index_w end in
        let typ := lazymatch s with (Some (Tofino.EnvRegister (_, ?typ, _))) => typ end in
        let s := lazymatch s with (Some (Tofino.EnvRegister (_, _, ?s))) => s end in
        exact (RegisterAction_execute_body ge am_ge _ p index_w typ s r eq_refl eq_refl ltac:(lia)
          fd repr f retv eq_refl body)
    | _ => fail "body is not a body proof for apply"
    end
  | _ => fail "body is not a body proof"
  end.

Ltac hoare_extern_match_list ::=
  apply hoare_extern_match_list_intro.

Ltac solve_assert_int :=
  simpl; rewrite P4Arith.bit_from_to_bool;
  unfold P4Arith.BitArith.mod_bound;
  try rewrite Z.mod_small by (unfold P4Arith.BitArith.upper_bound; lia);
  reflexivity.

#[export] Hint Rewrite Bool.andb_true_l Bool.andb_true_r Bool.andb_false_l Bool.andb_false_r : simpl_andb.

(* simpl in H with a easy-to-check proof term. *)
Ltac simpl_in H :=
  let type_of_H := type of H in
  let type_of_H' := eval simpl in type_of_H in
  lazymatch goal with
  | |- ?Goal =>
      revert H;
      refine ((_ : type_of_H' -> Goal) : type_of_H -> Goal);
      intros H
  end.

Ltac simpl_match_cond cond :=
  simpl_in cond; unfold fold_andb, fold_left in cond; autorewrite with simpl_andb in cond;
  repeat lazymatch goal with
  | cond : context [Tofino.values_match_range ?x ?lo ?hi] |- _ =>
      erewrite (reduce_match_range _ x lo hi) in cond;
      [ idtac
      | solve_assert_int
      | compute; reflexivity
      | compute; reflexivity
      ]
  | cond : context [Tofino.values_match_singleton ?x ?y] |- _ =>
      erewrite (reduce_match_singleton _ x y) in cond;
      [ idtac
      | repeat constructor
      | solve_assert_int
      | compute; reflexivity
      ]
  | cond : context [Tofino.values_match_mask ?x ?v ?m] |- _ =>
      erewrite (reduce_match_mask _ x v m) in cond;
      [ idtac
      | solve_assert_int (* In this case, we only need the bit form,
                            so the simplification in the integer form is unnecessary and maybe inefficient. *)
      | compute; reflexivity
      | compute; reflexivity
      ];
      cbv - [Bool.eqb Z.odd Z.div] in cond
  end.

Ltac hoare_table_action_cases' ::=
  first [
    apply hoare_table_action_cases'_nil
  | refine (@id (hoare_table_action_cases' _ _ _ _ _ _ ((_, _) :: _)) _);
    lazymatch goal with
    | |- hoare_table_action_cases' _ _ _ _ _ _ ((?cond, _) :: _)  =>
      let H_cond := fresh in
      let cond_name := fresh "cond" in
      remember cond as cond_name eqn:H_cond;
      simpl_match_cond H_cond;
      subst cond_name;
      idtac
    end;
    apply hoare_table_action_cases'_cons;
    [ let H := fresh in intro H
    | let H := fresh in intro H;
      hoare_table_action_cases'
    ]
  ].
