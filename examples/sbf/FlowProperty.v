Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.switch.
Require Import ProD3.examples.sbf.LightFilter.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Section FlowProperty.

Notation ident := string.
Notation path := (list ident).
Notation P4Type := (@P4Type Info).

Definition metadata_t : P4Type :=
  TypStruct [(!"bf2_key", TypBit 64); (!"bf2_api", TypBit 8); (!"solicited", TypBit 8)].

Definition force_extern_state (r: Monads.Result.result Target.Exn.t Target.extern_state) :=
  match r with
  | Result.Ok x => x
  | Result.Error _ => Maps.PathMap.empty
  end.

Definition init_es :=
  ltac:(let init_es := eval compute -[am_ge Maps.PathMap.empty Maps.PathMap.set
                                        Tofino.extern_match] in
        (force_extern_state (Semantics.gen_init_es' am_ge p4ast.prog)) in
          exact (init_es : (@Target.extern_state _ _ (@Target.extern_sem _ _ target)))).

Definition packet : Type := timestamp_t * ipv4_header * payload_t.
Definition result : Type := option (ipv4_header * payload_t).

Definition high_level_exec (h : list packet) (p : packet) (res : result) :=
  exists es h' es',
    process_packets ge metadata_t init_es h es h' /\
    process_packet ge metadata_t es p es' res.

Definition get_tstamp (p : packet) : Z := (fst (fst p)).

Definition get_src (p : packet) : Z := fst (snd (fst p)).

Definition get_dst (p : packet) : Z := snd (snd (fst p)).

(*
Definition valid_flow (f : list packet) :=
  forall i, 0 <= i < Zlength f - 1 ->
    0 <= get_tstamp (Znth (i + 1) f) - get_tstamp (Znth i f) < Tc.

Definition is_internal (ip_addr : Z) : bool.
Admitted.

Definition property (h : list packet) (p : packet) (res : result) : Prop :=
  ~~is_internal (get_src p) /\ is_internal (get_dst p) /\
    (exists i, 0 <= i < Zlength h /\ get_tstamp p - get_tstamp (Znth i h) < T /\
      get_src p = get_dst (Znth i h) /\ get_dst p = get_src (Znth i h)) ->
  isSome res.

Lemma flow_level_property : forall (h : list packet) (p : packet) (res : result),
  high_level_exec h p res ->
  valid_flow (h ++ [p]) ->
  property h p res.
Admitted.
*)
End FlowProperty.
