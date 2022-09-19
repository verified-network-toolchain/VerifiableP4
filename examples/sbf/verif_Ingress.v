Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.Utils.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.P4_types.
Require Import ProD3.examples.sbf.LightFilter.
Require Import ProD3.examples.sbf.LightRepr.
Require Import ProD3.examples.sbf.verif_Filter_all.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Import ListNotations.

Definition ipv4_header : Type := Z * Z.

Definition is_internal (ip_addr : Z) : bool.
Admitted.

(* The bool in the return value means the packet is allowed. *)
Definition process (f : filter) '((timestamp, ipv4) : Z * ipv4_header) : filter * option bool :=
  if is_internal (fst ipv4) then
    (filter_insert f (timestamp, ipv4), Some true)
  else
    (filter_clear f timestamp,
      filter_query (filter_clear f timestamp) (timestamp, (snd ipv4, fst ipv4))).

Definition p := ["pipe"; "ingress"].

Definition ipv4_addr_w := 32%N.

Definition Ingress_fd :=
  ltac:(get_fd ["SwitchIngress"; "apply"] ge).

Definition Ingress_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : ipv4_header) (tstamp : Z) (f : filter),
      PRE
        (ARG [update "ipv4"
                (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                  (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                    (force ValBaseNull (uninit_sval_of_typ None ipv4_h))))
                (force ValBaseNull (uninit_sval_of_typ None header_t));
              force ValBaseNull (uninit_sval_of_typ None metadata_t);
              force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_t);
              force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_from_parser_t);
              force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t);
              force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_tm_t)
             ]
        (MEM []
        (EXT [filter_repr (p ++ ["bf2_ds"]) f])))
      POST
        (ARG_RET [update "ipv4"
                    (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                      (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                        (force ValBaseNull (uninit_sval_of_typ None ipv4_h))))
                    (force ValBaseNull (uninit_sval_of_typ None header_t));
                  force ValBaseNull (uninit_sval_of_typ None metadata_t);
                  update "drop_ctl" (P4Bit_option 3 (option_map Z.b2z (snd (process f (tstamp, h)))))
                    (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t));
                  force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_tm_t)
                 ] ValBaseNull
        (MEM []
        (EXT [filter_repr (p ++ ["bf2_ds"]) (fst (process f (tstamp, h)))]))).

Lemma Ingress_body :
  func_sound ge Ingress_fd nil Ingress_spec.
Proof.
  start_function.
Admitted.
