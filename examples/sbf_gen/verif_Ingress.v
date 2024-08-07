Require Import Coq.ZArith.BinInt.
Require Import Coq.Program.Program.
Require Poulet4.Utils.Utils.
Require Import Coq.NArith.BinNat.
Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf_gen.Utils.
Require Import ProD3.examples.sbf_gen.common.
Require Import ProD3.examples.sbf_gen.P4_types.
Require Import ProD3.examples.sbf_gen.LightFilter.
Require Import ProD3.examples.sbf_gen.LightRepr.
Require Import ProD3.examples.sbf_gen.verif_Filter_all.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.
Open Scope Z_scope.
Import ListNotations.

Definition ipv4_header : Type := Z * Z.

Definition ipv4_addr_w := 32%N.

(* This is kind of cheating. :) *)
Definition is_internal (ip_addr : Z) : bool :=
  (Tofino.values_match_mask
         (ValBaseBit (P4Arith.to_lbool ipv4_addr_w ip_addr))
         (eval_p4int_val
            {| tags := NoInfo; value := 2154823680; width_signed := None |})
         (eval_p4int_val
            {| tags := NoInfo; value := 4294901760; width_signed := None |})).

(* The bool in the return value means the packet is dropped. *)
Definition process (f : filter) '((timestamp, ipv4, port) : Z * ipv4_header * Z) : filter * option bool :=
  if is_gen port then
    (filter_clear f timestamp, Some true)
  else if is_internal (fst ipv4) then
    (filter_insert f (timestamp, ipv4), Some false)
  else
    (filter_clear f timestamp,
      option_map negb (filter_query (filter_clear f timestamp) (timestamp, (snd ipv4, fst ipv4)))).

Definition p := ["pipe"; "ingress"].

Definition act_for_tbl_1_action_0_fd :=
  ltac:(get_fd ["SwitchIngress"; "act_for_tbl_1_action_0"] ge).

Definition act_for_tbl_1_action_0_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) []
    WITH ,
      PRE
        (ARG []
        (MEM [(["ig_md"], force ValBaseNull (uninit_sval_of_typ None metadata_t))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], update "solicited" (P4Bit 8 1)
          (force ValBaseNull (uninit_sval_of_typ None metadata_t)))]
        (EXT []))).

Lemma act_for_tbl_1_action_0_body :
  func_sound ge act_for_tbl_1_action_0_fd nil act_for_tbl_1_action_0_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Qed.

Definition tbl_for_stmt_1_fd :=
  ltac:(get_fd ["SwitchIngress"; "tbl_for_stmt_1"; "apply"] ge).

Definition tbl_for_stmt_1_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) []
    WITH ,
      PRE
        (ARG []
        (MEM [(["ig_md"], force ValBaseNull (uninit_sval_of_typ None metadata_t))]
        (EXT [])))
      POST
      (EX retv,
        (ARG_RET [] retv
        (MEM [(["ig_md"], update "solicited" (P4Bit 8 1)
          (force ValBaseNull (uninit_sval_of_typ None metadata_t)))]
        (EXT []))))%arg_ret_assr.

Lemma tbl_for_stmt_1_body :
  func_sound ge tbl_for_stmt_1_fd nil tbl_for_stmt_1_spec.
Proof.
  start_function.
  table_action act_for_tbl_1_action_0_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_for_stmt_1_body) : func_specs.

Definition bf2_act_set_insert_key_fd :=
  ltac:(get_fd ["SwitchIngress"; "bf2_act_set_insert_key"] ge).

Definition bf2_act_set_insert_key_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]; ["bf2_act_set_insert_key"; "api"]]) []
    WITH h,
      PRE
        (ARG [P4Bit 8 INSERT]
        (MEM [(["hdr"], update "ipv4"
                (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                  (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                    (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
                (force ValBaseNull (uninit_sval_of_typ None header_t)));
              (["ig_md"], update "solicited" (P4Bit 8 1)
                (force ValBaseNull (uninit_sval_of_typ None metadata_t)))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], update "bf2_key" (eval_val_to_sval (ValBaseBit
                (P4Arith.to_lbool ipv4_addr_w (snd h) ++ P4Arith.to_lbool ipv4_addr_w (fst h))))
          (update "bf2_api" (P4Bit 8 INSERT)
            (update "solicited" (P4Bit 8 1)
              (force ValBaseNull (uninit_sval_of_typ None metadata_t)))))]
        (EXT []))).

Lemma bf2_act_set_insert_key_body :
  func_sound ge bf2_act_set_insert_key_fd nil bf2_act_set_insert_key_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply bf2_act_set_insert_key_body) : func_specs.

Definition bf2_act_set_query_key_fd :=
  ltac:(get_fd ["SwitchIngress"; "bf2_act_set_query_key"] ge).

Definition bf2_act_set_query_key_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]; ["bf2_act_set_query_key"; "api"]]) []
    WITH h,
      PRE
        (ARG [P4Bit 8 QUERY]
        (MEM [(["hdr"], update "ipv4"
                (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                  (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                    (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
                (force ValBaseNull (uninit_sval_of_typ None header_t)));
              (["ig_md"], update "solicited" (P4Bit 8 1)
                (force ValBaseNull (uninit_sval_of_typ None metadata_t)))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], update "bf2_key" (eval_val_to_sval (ValBaseBit
                (P4Arith.to_lbool ipv4_addr_w (fst h) ++ P4Arith.to_lbool ipv4_addr_w (snd h))))
          (update "bf2_api" (P4Bit 8 QUERY)
            (update "solicited" (P4Bit 8 1)
              (force ValBaseNull (uninit_sval_of_typ None metadata_t)))))]
        (EXT []))).

Lemma bf2_act_set_query_key_body :
  func_sound ge bf2_act_set_query_key_fd nil bf2_act_set_query_key_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply bf2_act_set_query_key_body) : func_specs.

Definition bf2_act_set_clear_key_fd :=
  ltac:(get_fd ["SwitchIngress"; "bf2_act_set_clear_key"] ge).

Definition bf2_act_set_clear_key_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]; ["bf2_act_set_clear_key"]]) []
    WITH ,
      PRE
        (ARG []
        (MEM [(["ig_md"], update "solicited" (P4Bit 8 1)
                (force ValBaseNull (uninit_sval_of_typ None metadata_t)))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
           (MEM [(["ig_md"],
                   update "bf2_key" (P4Bit 64 0)
                     (update "bf2_api" (P4Bit 8 CLEAR)
                        (update "solicited" (P4Bit 8 1)
                           (force ValBaseNull (uninit_sval_of_typ None metadata_t)))))]
        (EXT []))).

Lemma bf2_act_set_clear_key_body :
  func_sound ge bf2_act_set_clear_key_fd nil bf2_act_set_clear_key_spec.
Proof.
  start_function.
  step.
  step.
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply bf2_act_set_clear_key_body) : func_specs.

Definition bf2_tbl_set_key_fd :=
  ltac:(get_fd ["SwitchIngress"; "bf2_tbl_set_key"; "apply"] ge).

Definition bf2_tbl_set_key_spec :=
  WITH (* p *),
    PATH p
      MOD (Some [["ig_md"]; ["bf2_act_set_insert_key"; "api"];
                 ["bf2_act_set_query_key"; "api"];
                 ["bf2_act_set_clear_key"]]) []
    WITH h port,
      PRE
        (ARG []
        (MEM [(["hdr"], update "ipv4"
                (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                  (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                    (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
                (force ValBaseNull (uninit_sval_of_typ None header_t)));
              (["ig_md"], update "solicited" (P4Bit 8 1)
                            (force ValBaseNull (uninit_sval_of_typ None metadata_t)));
              (["ig_intr_md"], update "ingress_port" (P4Bit 9 port)
                                 (force ValBaseNull
                                    (uninit_sval_of_typ (Some true)
                                       ingress_intrinsic_metadata_t)))]
        (EXT [])))
      POST
      (EX retv,
        (ARG_RET [] retv
        (MEM [(["ig_md"],
                update "bf2_key"
                    (eval_val_to_sval
                       (ValBaseBit
                          (if is_gen port then P4Arith.to_lbool 64 0 else
                             if is_internal (fst h) then
                               P4Arith.to_lbool ipv4_addr_w (snd h) ++
                                 P4Arith.to_lbool ipv4_addr_w (fst h)
                             else
                               P4Arith.to_lbool ipv4_addr_w (fst h) ++
                                 P4Arith.to_lbool ipv4_addr_w (snd h))))
                    (update "bf2_api"
                       (P4Bit 8 (if is_gen port then
                                   CLEAR else if is_internal (fst h)
                                              then INSERT else QUERY))
                       (update "solicited" (P4Bit 8 1)
                          (force ValBaseNull (uninit_sval_of_typ None metadata_t)))))]
        (EXT []))))%arg_ret_assr.

Lemma is_gen_port_mod: forall port,
    is_gen port = (port mod P4Arith.BitArith.upper_bound 9 =? 196).
Proof.
  intros. unfold is_gen, P4BitV. remember (P4Arith.to_lbool 9 port) as v1.
  remember (P4Arith.to_lbool 9 GENERATOR_PORT) as v2. destruct (Val_eqb _ _) eqn:?H.
  - rewrite Val_eqb_eq_iff in H. inversion H. clear H. rewrite Heqv1, Heqv2 in H1.
    pose proof (f_equal P4Arith.BitArith.from_lbool H1). clear H1 Heqv1 Heqv2.
    rewrite !P4Arith.bit_from_to_bool in H. inversion H.
    unfold P4Arith.BitArith.mod_bound in H1 at 1. rewrite H1. now vm_compute.
  - rewrite Val_eqb_neq_iff in H. symmetry. apply Bool.not_true_is_false. intro.
    apply H. clear H. f_equal. subst. rewrite Z.eqb_eq in H0.
    rewrite <- P4Arith.to_lbool_bit_mod at 1. unfold P4Arith.BitArith.mod_bound.
    rewrite H0. reflexivity.
Qed.

Lemma bf2_tbl_set_key_body :
  func_sound ge bf2_tbl_set_key_fd nil bf2_tbl_set_key_spec.
Proof.
  start_function.
  - rewrite <- is_gen_port_mod in H. rewrite !H. simpl fst. simpl snd.
    table_action bf2_act_set_clear_key_body. entailer. entailer.
  - rewrite <- is_gen_port_mod in H. hnf in H. rewrite Bool.negb_true_iff in H. rewrite !H.
    change (is_true (is_internal (fst h))) in H0.
    replace (is_internal (fst h)) with true by auto.
    table_action bf2_act_set_insert_key_body.
    { entailer. }
    { entailer. }
  - rewrite <- is_gen_port_mod in H. hnf in H. rewrite Bool.negb_true_iff in H. rewrite !H.
    change (is_true (~~is_internal (fst h))) in H0.
    replace (is_internal (fst h)) with false. 2 : {
      destruct (is_internal (fst h)); auto.
    }
    table_action bf2_act_set_query_key_body.
    { entailer. }
    { entailer. }
  - elim_trivial_cases.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply bf2_tbl_set_key_body) : func_specs.

Definition act_for_tbl_3_action_0_fd :=
  ltac:(get_fd ["SwitchIngress"; "act_for_tbl_3_action_0"] ge).

Definition act_for_tbl_3_action_0_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_intr_dprsr_md"]]) []
    WITH ,
      PRE
        (ARG []
        (MEM [(["ig_intr_dprsr_md"],
                (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_intr_dprsr_md"], update "drop_ctl" (P4Bit 3 1)
                (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT []))).

Lemma act_for_tbl_3_action_0_body :
  func_sound ge act_for_tbl_3_action_0_fd nil act_for_tbl_3_action_0_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Qed.

Definition act_for_tbl_3_action_1_fd :=
  ltac:(get_fd ["SwitchIngress"; "act_for_tbl_3_action_1"] ge).

Definition act_for_tbl_3_action_1_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_intr_dprsr_md"]]) []
    WITH ,
      PRE
        (ARG []
        (MEM [(["ig_intr_dprsr_md"],
                (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_intr_dprsr_md"], update "drop_ctl" (P4Bit 3 0)
                (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT []))).

Lemma act_for_tbl_3_action_1_body :
  func_sound ge act_for_tbl_3_action_1_fd nil act_for_tbl_3_action_1_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Qed.

Definition tbl_for_stmt_3_fd :=
  ltac:(get_fd ["SwitchIngress"; "tbl_for_stmt_3"; "apply"] ge).

Definition tbl_for_stmt_3_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_intr_dprsr_md"]]) []
    WITH solicited port,
      PRE
        (ARG []
        (MEM [(["ig_md"], update "solicited" (P4Bit_option 8 (option_map Z.b2z solicited))
                            (force ValBaseNull (uninit_sval_of_typ None metadata_t)));
              (["ig_intr_md"], update "ingress_port" (P4Bit 9 port)
                                 (force ValBaseNull
                                    (uninit_sval_of_typ (Some true)
                                       ingress_intrinsic_metadata_t)));
              (["ig_intr_dprsr_md"],
                (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT [])))
      POST
      (EX retv,
        (ARG_RET [] retv
           (MEM [(["ig_intr_dprsr_md"],
                   update "drop_ctl"
                     (if is_gen port then P4Bit 3 1 else
                        P4Bit_option 3 (option_map Z.b2z (option_map negb solicited)))
                     (force ValBaseNull (uninit_sval_of_typ None
                                           ingress_intrinsic_metadata_for_deparser_t)))]
        (EXT []))))%arg_ret_assr.

Lemma tbl_for_stmt_3_body :
  func_sound ge tbl_for_stmt_3_fd nil tbl_for_stmt_3_spec.
Proof.
  start_function.
  - rewrite <- is_gen_port_mod in H. rewrite H.
    table_action act_for_tbl_3_action_0_body.
    entailer. entailer.
  - rewrite <- is_gen_port_mod in H. hnf in H. rewrite Bool.negb_true_iff in H. rewrite H.
    table_action act_for_tbl_3_action_0_body.
    { entailer. }
    { entailer.
      destruct solicited as [[] | ].
      - simpl in H1.
        revert H0.
        simpl_sval_to_val.
        intro Hs.
        simpl_match_cond Hs.
        inv Hs.
      - repeat constructor.
      - repeat constructor.
    }
  - rewrite <- is_gen_port_mod in H. hnf in H. rewrite Bool.negb_true_iff in H. rewrite H.
    table_action act_for_tbl_3_action_1_body.
    { entailer. }
    { entailer.
      destruct solicited as [[] | ].
      - repeat constructor.
      - simpl in H1.
        revert H0.
        simpl_sval_to_val.
        intro Hs.
        simpl_match_cond Hs.
        inv Hs.
      - repeat constructor.
    }
  - elim_trivial_cases.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_for_stmt_3_body) : func_specs.

Definition Ingress_fd :=
  ltac:(get_fd ["SwitchIngress"; "apply"] ge).

Definition Ingress_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (h : ipv4_header) (tstamp : Z) (f : filter) (port: Z),
      PRE
        (ARG [update "ipv4"
                (update "src_addr" (P4Bit ipv4_addr_w (fst h))
                  (update "dst_addr" (P4Bit ipv4_addr_w (snd h))
                    (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
                (force ValBaseNull (uninit_sval_of_typ None header_t));
              force ValBaseNull (uninit_sval_of_typ None metadata_t);
              update "ingress_port" (P4Bit 9 port) (
                  update "ingress_mac_tstamp" (P4Bit 48 tstamp)
                    (force ValBaseNull (uninit_sval_of_typ (Some true) ingress_intrinsic_metadata_t)));
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
                        (force ValBaseNull (uninit_sval_of_typ (Some true) ipv4_h))))
                    (force ValBaseNull (uninit_sval_of_typ None header_t));
                  force ValBaseNull (uninit_sval_of_typ None metadata_t);
                  update "drop_ctl" (P4Bit_option 3 (option_map Z.b2z (snd (process f (tstamp, h, port)))))
                        (force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_deparser_t));
                  force ValBaseNull (uninit_sval_of_typ None ingress_intrinsic_metadata_for_tm_t)
                 ] ValBaseNull
        (MEM []
        (EXT [filter_repr (p ++ ["bf2_ds"]) (fst (process f (tstamp, h, port)))]))).

Lemma Ingress_body :
  func_sound ge Ingress_fd nil Ingress_spec.
Proof.
  start_function.
  step_call tbl_for_stmt_1_body.
  { entailer. }
  Intros _.
  step_call bf2_tbl_set_key_body.
  { entailer. Unshelve. 2: exact port. repeat constructor. }
  Intros _.
  destruct (is_gen port) eqn: H_is_gen.
  - step_call Filter_clear_body (0, 0) tstamp.
    { entailer. }
    step_call tbl_for_stmt_3_body (Some true).
    { entailer.
      repeat constructor.
      repeat constructor.
    }
    Intros _.
    step.
    unfold process.
    rewrite H_is_gen.
    destruct h.
    entailer.
    repeat constructor.
  - destruct (is_internal (fst h)) eqn:H_is_internal.
    + step_call Filter_insert_body (fst h, snd h) tstamp.
      { entailer. }
      step_call tbl_for_stmt_3_body (Some true).
      { entailer.
        repeat constructor.
        repeat constructor.
      }
      Intros _.
      step.
      unfold process.
      rewrite H_is_gen.
      rewrite H_is_internal.
      destruct h.
      entailer.
      repeat constructor.
    + step_call Filter_query_body (snd h, fst h) tstamp.
      { entailer.
        repeat constructor.
      }
      step_call tbl_for_stmt_3_body (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))).
      { entailer.
        repeat constructor.
        apply sval_refine_refl.
        repeat constructor.
      }
      Intros _.
      step.
      unfold process.
      rewrite H_is_gen, H_is_internal.
      destruct h.
      entailer.
      destruct (filter_query (filter_clear f tstamp) (tstamp, _));
        repeat constructor.
Qed.
