Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Core.
Require Export ProD3.core.TofinoSpec.

Instance target : @Target Info (@Expression Info) := Tofino.

(* It is a hack to make extern_match opauqe. But it should be fine. *)

Ltac get_am_ge prog ::=
  let ge := eval compute -[PathMap.empty PathMap.set extern_match] in (gen_am_ge prog) in
  exact (ge : (@genv _ target)).

Ltac get_ge am_ge prog ::=
  let ge := eval compute -[am_ge PathMap.empty PathMap.set extern_match] in (gen_ge' am_ge prog) in
  exact (ge : (@genv _ target)).

Ltac get_am_fd ge am_ge p :=
  let am_sem := eval compute -[am_ge extern_match] in
    (force Tofino.EnvPin (PathMap.get p (ge_ext ge))) in
  lazymatch am_sem with
  | Tofino.EnvAbsMet (exec_abstract_method ?ge ?p ?fd) =>
      exact fd
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
      | _ =>
          eval unfold spec in spec
      end in
    lazymatch spec with
    | RegisterAction_apply_spec ?p ?w ?f ?retv =>
        let r := eval compute in (PathMap.get p (ge_ext ge)) in
        let r := lazymatch r with (Some (Tofino.EnvRegAction ?r)) => r end in
        let s := eval compute in (PathMap.get r (ge_ext ge)) in
        let index_w := lazymatch s with (Some (Tofino.EnvRegister (?index_w, _, _))) => index_w end in
        let s := lazymatch s with (Some (Tofino.EnvRegister (_, _, ?s))) => s end in
        exact (RegisterAction_execute_body ge am_ge p index_w w s r eq_refl eq_refl ltac:(lia)
          fd f retv eq_refl body)
    | _ => fail "body is not a body proof for apply"
    end
  | _ => fail "body is not a body proof"
  end.

Ltac hoare_extern_match_list ::=
  apply hoare_extern_match_list_intro.
