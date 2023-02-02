Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.AbsModel.
Require Import ProD3.examples.cms.LightModel.
Require Import ProD3.examples.cms.ModelRepr.
Import ListNotations.
Open Scope list_scope.

Section LightRepr.

Notation ident := string.
Notation path := (list ident).

Context {num_frames num_rows num_slots frame_time : Z}.
Hypothesis H_num_slots : 0 < num_slots.
Hypothesis H_num_rows : 0 < num_rows.
Context {header_type : Set}.
Context (hashes : list (header_type -> Z)).
Hypothesis H_Zlength_hashes : Zlength hashes = num_rows.
Hypothesis H_hashes : Forall (fun hash => forall h, 0 <= hash h < num_slots) hashes.
Context (tick_time : Z).
Hypothesis (H_tick_time : 0 < tick_time).
Context {w : N} {panes : list string} {rows : list string}.

Definition cms_sim (f : @cms header_type) (cf : @ConModel.cms num_frames num_rows num_slots) : Prop :=
  match f with
  | Some f =>
      @AbsModel.cms_sim header_type num_frames num_rows num_slots frame_time
          H_num_slots H_num_rows hashes tick_time f cf
  | None => True
  end.

Program Definition cms_repr (p : path) (f : cms) : ext_pred :=
  ExtPred.ex (fun (cf : @ConModel.cms num_frames num_rows num_slots) =>
    ExtPred.and
      (@ModelRepr.cms_repr num_frames num_rows num_slots (AbsModel.frame_tick_tocks frame_time tick_time)
          p w panes rows cf)
      (ExtPred.prop (cms_sim f cf)))
    [p] _.
Next Obligation.
  unfold in_scope.
  rewrite is_prefix_refl.
  auto.
Qed.

End LightRepr.
