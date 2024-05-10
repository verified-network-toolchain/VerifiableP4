Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.Queue.
Require Import Poulet4.P4light.Semantics.Typing.ValueTyping.
Require Import ProD3.core.Tofino.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation P4Type := (@P4Type Info).
Notation packet := (list bool).
Notation fundef := (@fundef Info).

Inductive programmable_block (ge : (@genv _ target)):
  path -> ident -> fundef -> Prop :=
| programmable_block_intro:
  forall name fd pipe_class_name pipe_inst_path pipe_targs class_name inst_path targs,
    PathMap.get ["main"; "pipe0"] (ge_inst ge) =
      Some {|iclass:=pipe_class_name;
             ipath:=pipe_inst_path; itargs:=pipe_targs|} ->
    PathMap.get (pipe_inst_path ++ [name]) (ge_inst ge) =
      Some {|iclass:=class_name; ipath:=inst_path; itargs:=targs|} ->
    PathMap.get ([class_name; "apply"]) (ge_func ge) = Some fd ->
    programmable_block ge inst_path name fd.

Definition programmable_block_sem :=
  extern_state -> list Sval -> extern_state -> list Sval -> signal -> Prop.

Record pipeline_state := mkPipeSt {
    parser_state: extern_state;
    control_state: extern_state;
    deparser_state: extern_state;
  }.

Inductive ingress_pipeline (inprsr ingress indeprsr: programmable_block_sem)
  (parser_ingress_cond ingress_deprsr_cond: list Sval -> list Sval -> Prop)
  (ingress_tm_cond: list Sval -> Sval -> Prop):
  pipeline_state -> packet -> pipeline_state -> packet -> Sval -> Prop :=
| ingress_pipeline_intro:
  forall pin pout s1 s2 s3 s4 s5 s6 hdr1 hdr2 hdr3 ig_md1 ig_md2 payload
    rest1 rest2 rest3 rest4 for_tm,
    inprsr (PathMap.set ["packet_in"] (ObjPin pin) s1) []
      s2 (hdr1 :: ig_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_ingress_cond rest1 rest2 ->
    ingress s3 (hdr1 :: ig_md1 :: rest2) s4 (hdr2 :: ig_md2 :: rest3) SReturnNull ->
    ingress_deprsr_cond rest3 rest4 ->
    indeprsr (PathMap.set ["packet_out"] (ObjPout []) s5)
      (hdr2 :: ig_md2 :: rest4) s6 [hdr3] SReturnNull ->
    PathMap.get ["packet_out"] s6 = Some (ObjPout pout) ->
    ingress_tm_cond rest3 for_tm ->
    ingress_pipeline inprsr ingress indeprsr parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond (mkPipeSt s1 s3 s5) pin
      (mkPipeSt s2 s4 s6) (pout ++ payload) for_tm.

Inductive egress_pipeline (eprsr egress edeprsr: programmable_block_sem)
  (parser_egress_cond egress_deprsr_cond: list Sval -> list Sval -> Prop) :
  pipeline_state -> packet -> pipeline_state -> packet -> Prop :=
| egress_pipeline_intro:
  forall pin pout s1 s2 s3 s4 s5 s6 hdr1 hdr2 hdr3 eg_md1 eg_md2 payload
    rest1 rest2 rest3 rest4,
    eprsr (PathMap.set ["packet_in"] (ObjPin pin) s1) [] s2
      (hdr1 :: eg_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_egress_cond rest1 rest2 ->
    egress s3 (hdr1 :: eg_md1 :: rest2) s4 (hdr2 :: eg_md2 :: rest3) SReturnNull ->
    egress_deprsr_cond rest3 rest4 ->
    edeprsr (PathMap.set ["packet_out"] (ObjPout []) s5)
      (hdr2 :: eg_md2 :: rest4) s6 [hdr3] SReturnNull ->
    PathMap.get ["packet_out"] s6 = Some (ObjPout pout) ->
    egress_pipeline eprsr egress edeprsr parser_egress_cond egress_deprsr_cond
      (mkPipeSt s1 s3 s5) pin (mkPipeSt s2 s4 s6) (pout ++ payload).

Section SWITCH.

  Variable ingress_pipe: pipeline_state -> packet -> pipeline_state -> packet -> Sval -> Prop.
  Variable egress_pipe: pipeline_state -> packet -> pipeline_state -> packet -> Prop.
  Variable traffic_manager: Sval -> packet -> queue packet.

  Inductive process_ingress_packets :
    pipeline_state -> queue packet -> pipeline_state -> queue packet -> Prop :=
  | pip_nil: forall st, process_ingress_packets st empty_queue st empty_queue
  | pip_enque: forall st1 ps ps' md st2 p p' st3,
      process_ingress_packets st1 ps st2 ps' ->
      ingress_pipe st2 p st3 p' md ->
      process_ingress_packets st1 (enque p ps) st3 (concat_queue ps' (traffic_manager md p')).

  Inductive process_egress_packets :
    pipeline_state -> queue packet -> pipeline_state -> queue packet -> Prop :=
  | pep_nil: forall st, process_egress_packets st empty_queue st empty_queue
  | pep_enque: forall st1 ps ps' st2 p p' st3,
      process_egress_packets st1 ps st2 ps' ->
      egress_pipe st2 p st3 p' ->
      process_egress_packets st1 (enque p ps) st3 (enque p' ps').

  Definition process_queue_form {A: Type} (q: queue A) : Prop :=
    match q with
    | empty_queue => True
    | nonempty_queue front _ _ => front = []
    end.

  Lemma process_ingress_packets_input_form: forall st1 qin st2 qout,
      process_ingress_packets st1 qin st2 qout -> process_queue_form qin.
  Proof.
    intros. induction H; simpl; auto. rename IHprocess_ingress_packets into IH.
    destruct ps; simpl in *; auto.
  Qed.

  Lemma process_egress_packets_input_form: forall st1 qin st2 qout,
      process_egress_packets st1 qin st2 qout -> process_queue_form qin.
  Proof.
    intros. induction H; simpl; auto. rename IHprocess_egress_packets into IH.
    destruct ps; simpl in *; auto.
  Qed.

  Lemma process_queue_form_enque: forall {A: Type} (a: A) q,
      process_queue_form q -> process_queue_form (enque a q).
  Proof. intros. destruct q; simpl in *; auto. Qed.

  Lemma process_queue_form_enque_inv: forall {A: Type} (a: A) q,
        process_queue_form (enque a q) -> process_queue_form q.
  Proof. intros. destruct q; simpl in *; auto. Qed.

  Lemma process_queue_form_split: forall {A: Type} (q: queue A),
      process_queue_form q ->
      forall i, 0 <= i <= qlength q ->
           exists q1 q2, qlength q1 = i /\ q = concat_queue q1 q2 /\
                      process_queue_form q1 /\ process_queue_form q2.
  Proof.
    intros. rewrite qlength_eq, Zlength_correct in H0. remember (length (list_rep q)) as n.
    revert dependent q. revert dependent n. induction n; intros.
    - assert (i = 0) by lia. subst i. destruct q.
      2: simpl in Heqn; rewrite app_length in Heqn; simpl in Heqn; lia.
      exists empty_queue, empty_queue. simpl. auto.
    - destruct q. 1: simpl in Heqn; discriminate. simpl in H. subst. simpl in Heqn.
      rewrite rev'_eq, rev_length in Heqn. inversion Heqn. clear Heqn. destruct l0.
      + simpl in H1. subst n. assert (i = 0 \/ i = 1) by lia. destruct H; subst i.
        * exists empty_queue, (nonempty_queue [] a []). simpl. auto.
        * exists (nonempty_queue [] a []), empty_queue. simpl. auto.
      + rename l0 into l. rename a0 into b. destruct (Z_le_lt_dec i (Z.of_nat n)).
        * specialize (IHn ltac:(lia) (nonempty_queue [] a l) ltac:(reflexivity)).
          simpl in H1, IHn. rewrite rev'_eq, rev_length in IHn. specialize (IHn H1).
          destruct IHn as (q1 & q2 & ? & ? & ? & ?). exists q1, (enque b q2).
          split; [|split; [|split]]; auto. 2: apply process_queue_form_enque; assumption.
          destruct q1, q2; simpl in *; subst; try discriminate;
            inversion H2; try reflexivity.
          -- unfold concat_queue in *. simpl in *. unfold Basics.flip in *.
             rewrite rev'_eq in *. simpl in *. rewrite list_enque_app. rewrite <- H1.
             simpl. unfold Basics.flip. simpl. reflexivity.
          -- unfold concat_queue in *. simpl in *. unfold Basics.flip in *.
             rewrite rev'_eq in *. simpl in *. rewrite list_enque_app. rewrite <- H1.
             simpl. unfold Basics.flip. simpl. reflexivity.
        * assert (i = Z.of_nat (S n)) by lia. subst i. simpl in H1.
          exists (nonempty_queue [] a (b :: l)), empty_queue. split; [|simpl; auto].
          simpl qlength. rewrite Zlength_correct. simpl length. lia.
  Qed.

  Lemma enque_eq_concat_form: forall {A: Type} (p: A) ps q1 q2,
      enque p ps = concat_queue q1 q2 -> q2 <> empty_queue -> process_queue_form q2 ->
      exists q3, ps = concat_queue q1 q3 /\ process_queue_form q3 /\ q2 = enque p q3.
  Proof.
    intros. destruct q2. 1: contradiction. simpl in H1. subst. clear H0.
    unfold concat_queue in *. simpl in *. unfold Basics.flip in H.
    rewrite rev'_eq in H. destruct q1, ps; simpl in H;
      rewrite list_enque_nonempty, rev_involutive, ?app_nil_r in H; inv H.
    - exists empty_queue. simpl. auto.
    - exists (nonempty_queue [] a l1). simpl. unfold Basics.flip. simpl.
      rewrite rev'_eq, list_enque_nonempty, rev_involutive, app_nil_r. auto.
    - assert (length (l0 ++ a :: l1) = length (l0 ++ a :: l1)) by reflexivity.
      rewrite <- H3 in H at 1. rewrite app_length in H. simpl in H. lia.
    - destruct l0.
      + simpl in H3. inv H3. exists empty_queue. simpl. auto.
      + rewrite <- app_comm_cons in H3. inv H3. exists (nonempty_queue [] a l0). simpl.
        unfold Basics.flip. simpl.
        rewrite rev'_eq, list_enque_nonempty, rev_involutive. auto.
  Qed.

  Lemma process_ingress_packets_split: forall st1 qin st2 qout,
      process_ingress_packets st1 qin st2 qout ->
      forall len, 0 <= len <= qlength qin ->
             exists q1 q2 q3 q4 st3,
               qlength q1 = len /\
                 qin = concat_queue q1 q2 /\
                 qout = concat_queue q3 q4 /\
                 process_ingress_packets st1 q1 st3 q3 /\
                 process_ingress_packets st3 q2 st2 q4.
  Proof.
    intros. pose proof (process_ingress_packets_input_form _ _ _ _ H).
    destruct (process_queue_form_split _ H1 _ H0) as [q1 [q2 [? [? [? ?]]]]].
    exists q1, q2. revert dependent q2. revert dependent q1. induction H; intros.
    - exists empty_queue, empty_queue, st. symmetry in H3. apply concat_queue_eq_empty in H3.
      destruct H3. subst. do 4 (split; auto); constructor.
    - rename IHprocess_ingress_packets into IH. destruct (Z_le_gt_dec len (qlength ps)).
      + specialize (IH ltac:(lia) (process_queue_form_enque_inv _ _ H1) _ H3 H4).
        destruct (empty_queue_dec q2).
        1: subst; rewrite concat_queue_empty in H5; subst q1; rewrite qlength_enque in l; lia.
        destruct (enque_eq_concat_form _ _ _ _ H5 n H6) as [q3 [? [? ?]]]. specialize (IH _ H7 H8).
        destruct IH as (q4 & q5 & st4 & ? & ? & ? & ? & ?).
        exists q4, (concat_queue q5 (traffic_manager md p')), st4. subst ps'.
        rewrite concat_queue_assoc. do 4 (split; auto). subst q2. econstructor; eauto.
      + rewrite qlength_enque in H0. assert (len = qlength ps + 1) by lia. clear g H0 IH.
        pose proof (@eq_refl _ (qlength (enque p ps))). rewrite H5 in H0 at 1.
        rewrite qlength_concat, qlength_enque in H0. assert (qlength q2 = 0) by lia.
        rewrite qlength_0_iff in H8. subst q2. rewrite concat_queue_empty in *.
        exists (concat_queue ps' (traffic_manager md p')), empty_queue, st3.
        rewrite concat_queue_empty. subst q1. do 4 (split; auto).
        * econstructor; eauto.
        * constructor.
  Qed.

  Lemma process_egress_packets_split: forall st1 qin st2 qout,
      process_egress_packets st1 qin st2 qout ->
      forall len, 0 <= len <= qlength qin ->
             exists q1 q2 q3 q4 st3,
               qlength q1 = len /\
                 qin = concat_queue q1 q2 /\
                 qout = concat_queue q3 q4 /\
                 process_egress_packets st1 q1 st3 q3 /\
                 process_egress_packets st3 q2 st2 q4.
  Proof.
    intros. pose proof (process_egress_packets_input_form _ _ _ _ H).
    destruct (process_queue_form_split _ H1 _ H0) as [q1 [q2 [? [? [? ?]]]]].
    exists q1, q2. revert dependent q2. revert dependent q1. induction H; intros.
    - exists empty_queue, empty_queue, st. symmetry in H3. apply concat_queue_eq_empty in H3.
      destruct H3. subst. do 4 (split; auto); constructor.
    - rename IHprocess_egress_packets into IH. destruct (Z_le_gt_dec len (qlength ps)).
      + specialize (IH ltac:(lia) (process_queue_form_enque_inv _ _ H1) _ H3 H4).
        destruct (empty_queue_dec q2).
        1: subst; rewrite concat_queue_empty in H5; subst q1; rewrite qlength_enque in l; lia.
        destruct (enque_eq_concat_form _ _ _ _ H5 n H6) as [q3 [? [? ?]]]. specialize (IH _ H7 H8).
        destruct IH as (q4 & q5 & st4 & ? & ? & ? & ? & ?).
        exists q4, (enque p' q5), st4. subst ps'.
        rewrite enque_concat_queue. do 4 (split; auto). subst q2. econstructor; eauto.
      + rewrite qlength_enque in H0. assert (len = qlength ps + 1) by lia. clear g H0 IH.
        pose proof (@eq_refl _ (qlength (enque p ps))). rewrite H5 in H0 at 1.
        rewrite qlength_concat, qlength_enque in H0. assert (qlength q2 = 0) by lia.
        rewrite qlength_0_iff in H8. subst q2. rewrite concat_queue_empty in *.
        exists (enque p' ps'), empty_queue, st3.
        rewrite concat_queue_empty. subst q1. do 4 (split; auto).
        * econstructor; eauto.
        * constructor.
  Qed.

End SWITCH.
