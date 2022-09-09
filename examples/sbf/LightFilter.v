Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.AbsFilter.
Require Import ProD3.core.Coqlib.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Open Scope program_scope.

Section LightFilter.

Context {header_type : Set}.

Axiom filter_base : Type.
Definition filter := option filter_base.

(* The time of guaranteed query, e.g. 60s. *)
Axiom T : Z.
(* The maximum time interval between consecutive packets, e.g. 100us. *)
Axiom Tc : Z.

Axiom filter_insert : filter -> (Z * header_type) -> filter.
Axiom filter_query : filter -> (Z * header_type) -> option bool.
Axiom filter_clear : filter -> Z -> filter.
Axiom filter_empty : filter.

Lemma filter_query_clear : forall f t t' h b,
  isSome (filter_clear f t) ->
  filter_query f (t', h) = Some b ->
  filter_query (filter_clear f t) (t', h) = Some b.
Admitted.

Lemma filter_query_insert_same : forall f t t' h,
  0 <= t' - t < T ->
  isSome f ->
  filter_query (filter_insert f (t, h)) (t', h) = Some true.
Admitted.

Lemma filter_query_insert_other : forall f t t' h h',
  filter_query f (t', h') = Some true ->
  filter_query (filter_insert f (t, h)) (t', h') = Some true.
Admitted.

Lemma filter_query_empty : forall t h,
  filter_query filter_empty (t, h) = Some false.
Admitted.

Lemma isSome_filter_insert : forall f t h,
  isSome f ->
  isSome (filter_insert f (t, h)).
Admitted.

Lemma isSome_filter_clear_insert : forall f t t' h,
  isSome (filter_clear f t') ->
  isSome (filter_clear (filter_insert f (t, h)) t').
Admitted.

(* This is only true if we force f to be None as soon as Tc interval is voilated. *)
Lemma isSome_filter_clear_clear : forall f t t',
  0 <= t'-t < Tc ->
  isSome (filter_clear f t) ->
  isSome (filter_clear (filter_clear f t) t').
Admitted.

Lemma isSome_filter_clear_empty : forall t,
  isSome (filter_clear filter_empty t).
Admitted.

End LightFilter.
