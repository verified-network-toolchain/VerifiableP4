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
