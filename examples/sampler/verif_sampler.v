Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sampler.common.
Require Import ProD3.examples.sampler.ModelRepr.
Require Import ProD3.core.ProgNotations.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"].

Open Scope func_spec.

Definition regact_count_apply_body :=
  ltac:(auto_regact ge am_ge (p ++ ["regact_count"])).

Definition regact_count_execute_body :=
  ltac:(build_execute_body ge regact_count_apply_body).

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply regact_count_execute_body) : func_specs.

Definition act_count_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_count"] ge).

Definition act_count_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["ig_md"]]) [p]
    WITH (counter : Z),
      PRE
        (ARG []
        (MEM [(["ig_md"], ValBaseStruct [("num_pkts", P4Bit_ 32)])]
        (EXT [counter_repr p counter])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["ig_md"], ValBaseStruct [("num_pkts", P4Bit 32 (counter + 1))])]
        (EXT [counter_repr p (counter + 1)]))).

Lemma act_count_body:
  func_sound ge act_count_fundef nil act_count_spec.
Proof.
  start_function.
  unfold counter_repr, counter_reg_repr.
  normalize_EXT.
  Intros_prop. simpl.
  step_call regact_count_execute_body;
    [entailer | list_solve | lia | reflexivity |].
  step.
  entailer.
  repeat intro. hnf. simpl. lia.
Qed.

Definition act_sample_fundef :=
  ltac:(get_fd ["SwitchIngress"; "act_sample"] ge).

Definition header_sample_t: P4Type := ltac:(get_type "header_sample_t" ge).
Definition metadata_t: P4Type := ltac:(get_type "metadata_t" ge).
Definition ingress_intrinsic_metadata_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_t" ge).
Definition ingress_intrinsic_metadata_from_parser_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_from_parser_t" ge).
Definition ingress_intrinsic_metadata_for_deparser_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_for_deparser_t" ge).
Definition ingress_intrinsic_metadata_for_tm_t: P4Type :=
  ltac:(get_type "ingress_intrinsic_metadata_for_tm_t" ge).

Definition set_field_valid (h: Sval) (fld: ident): Sval :=
  (update fld (EvalBuiltin.setValid (get fld h)) h).

Record ipv4_rec := {
    ipv4_version: Sval;
    ipv4_ihl: Sval;
    ipv4_diffserv: Sval;
    ipv4_total_len: Sval;
    ipv4_identification: Sval;
    ipv4_flags: Sval;
    ipv4_frag_offset: Sval;
    ipv4_ttl: Sval;
    ipv4_protocol: Sval;
    ipv4_hdr_checksum: Sval;
    ipv4_src_addr: Sval;
    ipv4_dst_addr: Sval;
  }.

Definition hdr (ethernet tcp udp: Sval) (ipv4: ipv4_rec): Sval :=
  ValBaseStruct
    [("bridge",
       ValBaseHeader
         [("contains_sample", P4Bit_ 8)] (Some true));
     ("sample",
       ValBaseHeader
         [("dmac", P4Bit_ 48);
          ("smac", P4Bit_ 48);
          ("etype", P4Bit_ 16);
          ("srcip", P4Bit_ 32);
          ("dstip", P4Bit_ 32);
          ("num_pkts", P4Bit_ 32)] None);
     ("ethernet", ethernet);
     ("ipv4",
       ValBaseHeader
         [("version", ipv4_version ipv4);
          ("ihl", ipv4_ihl ipv4);
          ("diffserv", ipv4_diffserv ipv4);
          ("total_len", ipv4_total_len ipv4);
          ("identification", ipv4_identification ipv4);
          ("flags", ipv4_flags ipv4);
          ("frag_offset", ipv4_frag_offset ipv4);
          ("ttl", ipv4_ttl ipv4);
          ("protocol", ipv4_protocol ipv4);
          ("hdr_checksum", ipv4_hdr_checksum ipv4);
          ("src_addr", ipv4_src_addr ipv4);
          ("dst_addr", ipv4_dst_addr ipv4)] (Some true));
     ("tcp", tcp);
     ("udp", udp)].

Definition ig_md (num_pkts: Z) := ValBaseStruct [("num_pkts", P4Bit 32 num_pkts)].

Definition update_hdr ethernet tcp udp ipv4 num_pkts :=
  update "sample"
    (sample_repr (ipv4_src_addr ipv4) (ipv4_dst_addr ipv4) num_pkts)
    (update "bridge" (bridge_repr 1) (hdr ethernet tcp udp ipv4)).

Definition act_sample_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_tm_md"]]) [p]
    WITH ethernet tcp udp ipv4 ig_intr_tm_md num_pkts,
      PRE
        (ARG []
        (MEM [(["hdr"], hdr ethernet tcp udp ipv4);
              (["ig_md"], ig_md num_pkts);
              (["ig_intr_tm_md"], ig_intr_tm_md)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["hdr"], update_hdr ethernet tcp udp ipv4 num_pkts);
              (* (["ig_md"], ig_md num_pkts); *)
              (["ig_intr_tm_md"], update "mcast_grp_a" (P4Bit 16 1) ig_intr_tm_md)]
        (EXT []))).

Lemma act_sample_body:
  func_sound ge act_sample_fundef nil act_sample_spec.
Proof.
  start_function.
  unfold hdr.
  simpl.
  do 10 step.
  entailer.
Qed.

Definition tbl_sample_fd :=
  ltac:(get_fd ["SwitchIngress"; "tbl_sample"; "apply"] ge).

Definition tbl_sample_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["hdr"]; ["ig_intr_tm_md"]]) [p]
    WITH ethernet tcp udp ipv4 ig_intr_tm_md num_pkts,
      PRE
        (ARG []
        (MEM [(["hdr"], hdr ethernet tcp udp ipv4);
              (["ig_md"], ig_md num_pkts);
              (["ig_intr_tm_md"], ig_intr_tm_md)]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["hdr"], if (num_pkts mod 1024 =? 1) then
                             update_hdr ethernet tcp udp ipv4 num_pkts
                           else hdr ethernet tcp udp ipv4);
              (* (["ig_md"], ig_md num_pkts); *)
              (["ig_intr_tm_md"], if (num_pkts mod 1024 =? 1) then
                                    update "mcast_grp_a" (P4Bit 16 1) ig_intr_tm_md
                                  else ig_intr_tm_md)]
        (EXT []))))%arg_ret_assr.

Lemma mod_2_pow_1_less: forall v n m,
    0 < m -> m < n -> v mod 2 ^ n = 1 ->  Z.odd (v / 2 ^ m) = false.
Proof.
  intros v n m Hg0 Hl Hm.
  pose proof (Z_div_mod_eq_full v (2 ^ n)) as Hveq.
  rewrite Hm in Hveq. clear Hm.
  assert (n = m + (n - m)) as HE by lia. rewrite HE in Hveq at 1. clear HE.
  rewrite Z.pow_add_r in Hveq by lia.
  rewrite <- Z.mul_assoc, Z.mul_comm in Hveq.
  rewrite Hveq, Z.div_add_l by lia.
  rewrite Z.div_1_l.
  - rewrite Z.add_0_r, Z.odd_mul, Z.odd_pow by lia. reflexivity.
  - rewrite <- (Z.pow_0_r 2). apply Z.pow_lt_mono_r; lia.
Qed.

Lemma mod_2_pow_0_less_iff: forall v n,
    0 <= n ->
    v mod 2 ^ n = 0 <-> (forall m, 0 <= m < n -> Z.odd (v / 2 ^ m) = false).
Proof.
  intros v n Hg. split.
  - intros Hvm m Hmlt.
    pose proof (Z_div_mod_eq_full v (2 ^ n)) as Hveq.
    rewrite Hvm, Z.add_0_r in Hveq.
    assert (n = m + (n - m)) as HE by lia. rewrite HE in Hveq at 1. clear HE.
    rewrite Z.pow_add_r in Hveq by lia.
    rewrite <- Z.mul_assoc, Z.mul_comm in Hveq.
    rewrite Hveq, Z_div_mult by lia.
    rewrite Z.odd_mul, Z.odd_pow by lia. simpl. reflexivity.
  - rewrite Z.le_lteq in Hg. destruct Hg as [Hg | Hg].
    + assert (n = Z.of_nat (S (Z.to_nat n - 1))) as Heq by lia.
      rewrite Heq. revert v. clear Hg Heq. generalize (Z.to_nat n - 1)%nat. clear n.
      induction n; intros v Hm.
      * simpl Z.of_nat in *. rewrite Z.pow_1_r. specialize (Hm 0 ltac:(lia)).
        rewrite Z.pow_0_r, Z.div_1_r in Hm. rewrite Zmod_odd, Hm. reflexivity.
      * rewrite Nat2Z.inj_succ, <- Z.add_1_l, Z.pow_add_r by lia.
        rewrite Z.pow_1_r, <- P4Arith.div_2_mod_2_pow by lia.
        generalize (Hm 0 ltac:(lia)). rewrite Z.pow_0_r, Z.div_1_r.
        intro H0; rewrite H0. clear H0. rewrite IHn. 1: lia. intros m' Hm'.
        rewrite Z.div_div by lia. replace 2 with (2 ^ 1) at 1 by lia.
        rewrite <- Z.pow_add_r by lia. apply Hm. lia.
    + intros. rewrite <- Hg. rewrite Z.pow_0_r, Z.mod_1_r. reflexivity.
Qed.

Lemma mod_2_pow_1_less_iff: forall v n,
    0 < n ->
    v mod 2 ^ n = 1 <-> (forall m, 0 < m < n -> Z.odd (v / 2 ^ m) = false) /\
                        Z.odd v = true.
Proof.
  intros v n Hg. split.
  - intros Hm. split.
    + intros. eapply mod_2_pow_1_less; eauto; lia.
    + assert (n = Z.of_nat (S (Z.to_nat n - 1))) as Heq by lia.
      rewrite Heq in Hm. erewrite <- P4Arith.Z_odd_pow_2_S.
      rewrite Hm. reflexivity.
  - intros [Hm Hv].
    assert (n = 1 + (n - 1)) as Heq by lia.
    rewrite Heq. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    rewrite <- P4Arith.div_2_mod_2_pow by lia. rewrite Hv.
    cut ((v / 2) mod 2 ^ (n - 1) = 0).
    + intros Hmv. rewrite Hmv. lia.
    + rewrite mod_2_pow_0_less_iff by lia. intros m' Hm'.
      rewrite Z.div_div by lia. replace 2 with (2 ^ 1) at 1 by lia.
      rewrite <- Z.pow_add_r by lia. apply Hm. lia.
Qed.

Lemma table_match_helper: forall v,
    values_match_mask
      (ValBaseBit (P4Arith.to_lbool 32 v))
      (ValBaseBit (P4Arith.to_lbool 32 0x001))
      (ValBaseBit (P4Arith.to_lbool 32 0x3FF)) <->
      v mod 1024 = 1.
Proof.
  intros. unfold values_match_mask. simpl.
  (* cbv - [Bool.eqb Z.odd Z.div Z.modulo]. *)
  rewrite !Z.div_div by lia. simpl.
  unfold is_true. rewrite !Bool.andb_true_iff, !Bool.eqb_true_iff.
  change 2 with (2 ^ 1). change 4 with (2 ^ 2). change 8 with (2 ^ 3).
  change 16 with (2 ^ 4). change 32 with (2 ^ 5). change 64 with (2 ^ 6).
  change 128 with (2 ^ 7). change 256 with (2 ^ 8). change 512 with (2 ^ 9).
  change 1024 with (2 ^ 10). rewrite mod_2_pow_1_less_iff by lia. split; intros.
  - repeat match goal with | [H: _ /\ _ |- _] => destruct H end.
    rewrite H8. split. 2: reflexivity. intros. destruct H10 as [Hlo Hhi].
    do 9 (apply Ztac.Zlt_le_add_1 in Hlo; simpl in Hlo; rewrite Z.le_lteq in Hlo;
          destruct Hlo as [Hlo | Hlo]; [| now rewrite <- Hlo]). lia.
  - destruct H. rewrite H0.
    repeat (rewrite H; only 2: lia). tauto.
Qed.

Lemma tbl_sample_body:
  func_sound ge tbl_sample_fd nil tbl_sample_spec.
Proof.
  start_function; elim_trivial_cases; simpl fst; simpl snd.
  - assert (num_pkts mod 1024 = 1) as Hm. {
      rewrite <- table_match_helper.
      unfold values_match_mask. simpl.
      cbv - [Bool.eqb Z.odd Z.div Z.modulo]. easy. } clear H. simpl.
    rewrite <- Z.eqb_eq in Hm. rewrite Hm.
    table_action act_sample_body.
    + entailer.
    + entailer.
  - assert (num_pkts mod 1024 <> 1) as Hm. {
      intro. rewrite <- table_match_helper in H1.
      unfold values_match_mask in H1. simpl in H1.
      cbv - [Bool.eqb Z.odd Z.div Z.modulo] in H1. rewrite H1 in H. easy. }
    rewrite <- Z.eqb_neq in Hm. rewrite Hm.
    table_action (@NoAction_body Info).
    + entailer.
    + entailer.
Qed.
