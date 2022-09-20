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
Require Import ProD3.examples.sbf.verif_Filter_all.
Require Import ProD3.examples.sbf.verif_Ingress.
Require Import ProD3.examples.sbf.flow_proof.
Require Import ProD3.examples.sbf.switch.
Require Import Hammer.Plugin.Hammer.

Notation filter_repr := (filter_repr ["pipe"; "ingress"; "bf2_ds"]).

Lemma inv_Forall2 : forall A B (P : A -> B -> Prop) a al b bl,
  Forall2 P (a :: al) (b :: bl) ->
  P a b /\ Forall2 P al bl.
Proof.
  inversion 1; auto.
Qed.

Lemma sval_refine_P4Bit_eq : forall w v v',
  sval_refine (P4Bit w v) v' ->
  (P4Bit w v) = v'.
Proof.
  intros.
  symmetry.
  apply sval_refine_bit_to_loptbool; auto.
Qed.

Lemma eq_P4Bit_eq : forall (w : N) (n1 n2 : Z),
  0 <= n1 < 2 ^ Z.of_N w ->
  0 <= n2 < 2 ^ Z.of_N w ->
  P4Bit w n1 = P4Bit w n2 ->
  n1 = n2.
Proof.
  intros.
  eapply sval_refine_to_loptbool_eq; eauto.
  apply sval_refine_refl'; auto.
Qed.

Lemma process_packet_fw_process_packet : forall es f p es' r,
  0 <=  fst (snd (fst p)) < Z.pow 2 32 ->
  0 <=  snd (snd (fst p)) < Z.pow 2 32 ->
  filter_repr f es ->
  process_packet ge P4_types.metadata_t es p es' r ->
  exists f',
    filter_repr f' es' /\ fw_process_packet f p f' r.
Proof.
  intros * ?H ?H H_filter_repr H_process_packet.
  destruct p as [[tstamp h] payload].
  exists (fst (process f (tstamp, h))).
  inversion H_process_packet.
  (* deal with function lookup *)
  inv H4. inv H5. inv H6.
  eapply (proj1 Ingress_body h) in H7.
  2 : {
    split.
    { (* ARG *)
      constructor.
      { apply sval_refine_refl. }
      constructor.
      { apply sval_refine_refl. }
      constructor.
      { apply sval_refine_refl. }
      constructor.
      { apply sval_refine_refl. }
      constructor.
      { apply sval_refine_refl. }
      constructor.
      { apply sval_refine_refl. }
      constructor.
    }
    split.
    { (* MEM *)
      constructor.
    }
    { (* EXT *)
      constructor.
      { apply H_filter_repr. }
      constructor.
    }
  }
  destruct H7 as [H_ARG [H_RET [H_MEM H_EXT]]].
  split.
  { inv H_EXT.
    assumption.
  }
  apply inv_Forall2 in H_ARG.
  destruct H_ARG as [H_hdr H_ARG].
  apply inv_Forall2 in H_ARG.
  destruct H_ARG as [H_ig_md H_ARG].
  apply inv_Forall2 in H_ARG.
  destruct H_ARG as [H_ig_intr_dprsr_md _].
  replace (get "src_addr" (get "ipv4" hdr')) with (P4Bit ipv4_addr_w (fst h)) in *. 2 : {
    clear -H_hdr.
    pose proof (sval_refine_get _ _ "ipv4" H_hdr).
    pose proof (sval_refine_get _ _ "src_addr" H).
    rewrite get_update_same in H0 by auto.
    rewrite get_update_same in H0 by auto.
    apply sval_refine_P4Bit_eq in H0.
    auto.
  }
  replace (get "dst_addr" (get "ipv4" hdr')) with (P4Bit ipv4_addr_w (snd h)) in *. 2 : {
    clear -H_hdr.
    pose proof (sval_refine_get _ _ "ipv4" H_hdr).
    pose proof (sval_refine_get _ _ "dst_addr" H).
    rewrite get_update_same in H0 by auto.
    rewrite get_update_diff in H0 by (auto; congruence).
    rewrite get_update_same in H0 by auto.
    apply sval_refine_P4Bit_eq in H0.
    auto.
  }
  replace ipv4' with h in *. 2 : {
    clear - H H0 H8 H10 H13 H14.
    assert (fst h = fst ipv4'). {
      eapply eq_P4Bit_eq; eauto; auto.
    }
    assert (snd h = snd ipv4'). {
      eapply eq_P4Bit_eq; eauto; auto.
    }
    destruct h; destruct ipv4'; f_equal; auto.
  }
  assert (H_drop_ctl : bit_refine (snd (process f (tstamp, h))) (Some drop_ctl)). {
    clear -H_ig_intr_dprsr_md.
    pose proof (sval_refine_get _ _ "drop_ctl" H_ig_intr_dprsr_md).
    rewrite get_update_same in H by auto.
    change (snd (process f (tstamp, h))) with (snd (process f (tstamp, h))) in *.
    destruct (snd (process f (tstamp, h))) as [[] | ].
    - apply sval_refine_P4Bit_eq in H.
      subst drop_ctl. rewrite <- H. constructor.
    - apply sval_refine_P4Bit_eq in H.
      subst drop_ctl. rewrite <- H. constructor.
    - constructor.
  }
  unfold process in H_drop_ctl |- *.
  destruct (is_internal (fst h)) eqn:H_is_internal.
  - inv H_drop_ctl.
    (* This is not provable, because the P4 program drops outgoing packets. *)
    admit.
  - change (option_map ~~
      (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))))
    with (option_map ~~
      (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h)))) in *.
    destruct (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))) as [[] | ] eqn:H_filter_query.
    3 : destruct drop_ctl.
    + inv H_drop_ctl.
      constructor.
      { assumption. }
      { change (query (clear f tstamp) (tstamp, Build_Header (DstAddr h) (SrcAddr h)))
          with (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))).
        rewrite H_filter_query. solve [repeat constructor].
      }
    + inv H_drop_ctl.
      constructor.
      { assumption. }
      { change (query (clear f tstamp) (tstamp, Build_Header (DstAddr h) (SrcAddr h)))
          with (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))).
        rewrite H_filter_query. solve [repeat constructor].
      }
    + constructor.
      { assumption. }
      { change (query (clear f tstamp) (tstamp, Build_Header (DstAddr h) (SrcAddr h)))
          with (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))).
        rewrite H_filter_query. solve [repeat constructor].
      }
    + constructor.
      { assumption. }
      { change (query (clear f tstamp) (tstamp, Build_Header (DstAddr h) (SrcAddr h)))
          with (filter_query (filter_clear f tstamp) (tstamp, (snd h, fst h))).
        rewrite H_filter_query. solve [repeat constructor].
      }
Admitted.
