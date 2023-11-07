Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.String.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Import ListNotations.
Open Scope list_scope.

Notation ident := string.
Notation path := (list ident).

Definition Z_to_val (i: Z): ValueBase := ValBaseBit (P4Arith.to_lbool 32 i).

Definition counter_reg_repr (p : path) (counter : Z) : ext_pred :=
  ExtPred.and
    (ExtPred.singleton (p ++ ["reg_count"])
       (Tofino.ObjRegister [Z_to_val counter]))
    (ExtPred.prop (0 <= counter)).

Program Definition counter_repr (p : path) (counter : Z) : ext_pred :=
  ExtPred.wrap [p] [counter_reg_repr p counter] _.
Next Obligation.
  unfold in_scope.
  rewrite <- (app_nil_r p) at 1.
  rewrite is_prefix_cancel. auto.
Qed.

Definition bridge_repr (data: Z): ValueBase :=
  ValBaseHeader [("contains_sample", P4Bit 8 data)] (Some true).

Definition bridge_repr_val (has_sample: Z): ValueBase :=
  ValBaseHeader [("contains_sample", P4BitV 8 has_sample)] true.

Definition COLLECTOR_MAC: Z := 2.
Definition MY_MAC: Z := 1.
Definition SAMPLE_ETYPE := 0x1234.

Definition sample_repr srcip dstip (num_pkts: Z): ValueBase :=
  ValBaseHeader
    [("dmac", P4Bit 48 COLLECTOR_MAC);
     ("smac", P4Bit 48 MY_MAC);
     ("etype", P4Bit 16 SAMPLE_ETYPE);
     ("srcip", srcip);
     ("dstip", dstip);
     ("num_pkts", P4Bit 32 num_pkts)] (Some true).

Definition sample_reprv srcip dstip (num_pkts: Z): ValueBase :=
  ValBaseHeader
    [("dmac", P4BitV 48 COLLECTOR_MAC);
     ("smac", P4BitV 48 MY_MAC);
     ("etype", P4BitV 16 SAMPLE_ETYPE);
     ("srcip", srcip);
     ("dstip", dstip);
     ("num_pkts", P4BitV 32 num_pkts)] true.
