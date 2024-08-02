Require Import VST.floyd.proofauto.
Require Import ProD3.examples.sbf_gen.common.
Require Import ProD3.examples.sbf_gen.LightFilter.
Require Import ProD3.examples.sbf_gen.verif_Filter_all.
Require Import ProD3.examples.sbf_gen.verif_Ingress.
Definition Time:= Z.

Definition ip_addr := Z.
(* Parameter ip_addrDummy: Inhabitant ip_addr. *)
(* Parameter T Tc:Time. *)
Notation T := (T num_frames frame_time).
Notation Tc := (Tc num_slots frame_time tick_time).
(* Parameter is_internal: ip_addr -> bool. *)

(* Parameter filter_base : Type. *)

(* Record Header := { SrcAddr: ip_addr; DstAddr : ip_addr }. *)
Definition Header : Type := Z * Z.
Definition Build_Header : Z -> Z -> Header := pair.
Definition SrcAddr : Header -> Z := fst.
Definition DstAddr : Header -> Z := snd.

(* Definition DefaultHeader:Inhabitant Header. split. apply ip_addrDummy.  apply ip_addrDummy. Defined. *)

Definition insert : filter -> Time * Header -> filter :=
  filter_insert.

Definition query : filter -> Time * Header -> option bool :=
  filter_query.

Definition clear : filter -> Time -> filter :=
  filter_clear.

Definition empty : Time -> filter := filter_empty num_frames num_slots frame_time tick_time.

Definition ok_until : filter -> Time -> Prop :=
  ok_until num_frames num_slots frame_time tick_time.

Lemma H_frame_time : 0 < frame_time.
Proof. constructor. Qed.

Lemma H_tick_time_div : (tick_time * 2 | frame_time).
  exists frame_tick_tocks.
  auto.
Qed.

Ltac resolve_parameter_conditions :=
  auto using H_hashes, H_tick_time_div;
  reflexivity.

Lemma query_clear: forall f t t' h,
  t <= t' ->
  ok_until f t ->
  query f (t', h) = query (clear f t) (t', h).
Proof.
  apply query_clear with (num_rows := num_rows);
    resolve_parameter_conditions.
Qed.

Lemma query_insert_same : forall f t t' h,
  t <= t' <= t+T ->
  ok_until f t ->
  query (insert f (t, h)) (t', h) = Some true.
Proof.
  apply query_insert_same;
    resolve_parameter_conditions.
Qed.

Lemma query_insert_other : forall f t t' h h',
  t <= t' ->
  ok_until f t ->
  query f (t', h') = Some true ->
  query (insert f (t, h)) (t', h') = Some true.
Proof.
  apply query_insert_other with (num_rows := num_rows);
    resolve_parameter_conditions.
Qed.

Lemma ok_insert: forall f t t' h, t <= t' <= t+Tc -> ok_until f t ->
             ok_until (insert f (t,h)) t'.
Proof.
  apply ok_insert;
    resolve_parameter_conditions.
Qed.

Lemma ok_clear: forall f t t', t <= t' <= t+Tc -> ok_until f t ->
            ok_until (clear f t) t'.
Proof.
  apply ok_clear;
    resolve_parameter_conditions.
Qed.

Lemma ok_empty: forall t, ok_until (empty t) t.
Proof.
  apply ok_empty;
    resolve_parameter_conditions.
Qed.

Opaque insert query clear empty ok_until.

Definition Payload := list bool.
(* Definition DummyData: Inhabitant Payload.
  typeclasses eauto.
  unfold Payload.  *)

Definition Packet:Type := ((Time * Header) * Payload) * Z.
Definition Result:Type := option (Header * Payload).

Definition FirewallState:Type := filter.

Inductive fw_process_packet: FirewallState -> Packet -> FirewallState -> Result -> Prop :=
| fw_clear: forall f t h data port,
    is_gen port = true ->
    fw_process_packet f (((t,h),data), port) (clear f t) None
| fw_outgoing: forall f t h data port,
    is_gen port = false -> is_internal (SrcAddr h) = true ->
    fw_process_packet f (((t,h),data), port) (insert f (t, h)) (Some (h, data))
(*Incoming packet is permitted by the firewall*)
| fw_incomingPermit: forall f t h data port,
    is_gen port = false -> is_internal (SrcAddr h) = false ->
    In (query (clear f t) (t, Build_Header (DstAddr h) (SrcAddr h))) [None; Some true] ->
    fw_process_packet f (((t,h),data), port) (clear f t) (Some (h, data))
(*this is the case where packets are dropped, ie DOS is detected*)
| fw_incomingDrop: forall f t h data port,
    is_gen port = false -> is_internal (SrcAddr h) = false ->
    In (query (clear f t)  (t, Build_Header (DstAddr h) (SrcAddr h))) [ None; Some false] ->
    fw_process_packet f (((t,h),data), port) (clear f t) None.

Inductive trans_fw: FirewallState -> list Packet -> FirewallState -> list Result -> Prop :=
  trans_nil: forall f, trans_fw f [] f []
|
  trans_step: forall f h k u, trans_fw f h k u -> forall p g r,
                fw_process_packet k p g r -> trans_fw f (h++[p]) g (u++[r]).

Lemma trans_single: forall f p g r, fw_process_packet f p g r -> trans_fw f [p] g [r].
Proof. intros. simpl. eapply (trans_step f [] f []). constructor. trivial. Qed.

Lemma trans_cons: forall f p g r, fw_process_packet f p g r ->
                  forall h k u, trans_fw g h k u ->
                trans_fw f (p::h) k (r::u).
Proof. intros. induction H0; simpl; intros.
+ eapply trans_single. trivial.
+ replace (p :: h ++ [p0]) with ((p :: h) ++ [p0]) by reflexivity.
  replace (r :: u ++ [r0]) with ((r :: u) ++ [r0]) by reflexivity.
  eapply trans_step; eauto.
Qed.

Lemma trans_app_inv: forall l2 {l f g r}, trans_fw f l g r ->
      forall l1, l=l1++l2 ->
      exists k r1 r2,
       trans_fw f l1 k r1  /\ trans_fw k l2 g r2 /\ r=r1++r2.
Proof. induction l2; simpl; intros.
+ rewrite app_nil_r in H0; subst l1.
  do 3 eexists; split3. eauto. apply trans_nil. rewrite app_nil_r; trivial.
+ specialize (IHl2 _ _ _ _ H (l1 ++ [a])). rewrite <- app_assoc in IHl2.
  destruct (IHl2 H0) as [k [r1 [r2 [T1 [T2 R]]]]]; clear IHl2 H. subst.
  inv T1. 1: symmetry in H1; apply app_eq_nil in H1; destruct H1; congruence.
  apply app_inj_tail in H. destruct H; subst h p.
  do 3 eexists; split3.
  - eassumption.
  - eapply trans_cons. apply H2. apply T2.
  - rewrite <- app_assoc; trivial.
Qed.

Lemma trans_cons_inv: forall h l f g r, trans_fw f l g r ->
      forall p, l=p::h ->
      exists k r1 r2,
       fw_process_packet f p k r1 /\ trans_fw k h g r2 /\ r=r1::r2.
Proof. intros.
  destruct (trans_app_inv h H [p] H0) as [k [r1 [r2 [P [HH R]]]]].
  clear H; inv P. destruct h0; inv H; [ | apply app_eq_nil in H4; destruct H4; congruence].
  inv H1; simpl.
  + do 3 eexists; split3; eauto.
  + apply app_eq_nil in H; destruct H; congruence.
Qed.

Definition get_port (p: Packet): Z := snd p.

Definition get_tstamp (p : Packet) : Time := (fst (fst (fst p))).

Definition get_src (p : Packet) : ip_addr := SrcAddr (snd (fst (fst p))).

Definition get_dst (p : Packet) : ip_addr := DstAddr (snd (fst (fst p))).

Lemma fw_packet_preserves_okUntil {f p g r}:
      fw_process_packet f p g r -> let t:= get_tstamp p in
      ok_until f t -> forall t', t <= t' <= t+Tc -> ok_until g t'.
Proof.
  induction 1; unfold get_tstamp; simpl; intros.
  - apply ok_clear; trivial.
  - (*fw_outgoingSuccess*) apply ok_insert; trivial.
  - (*fw_incomingPermit*) apply ok_clear; trivial.
  - (*fw_incomingDrop*) apply ok_clear; trivial.
Qed.

(* #[global] Instance d:Inhabitant Packet. split. split. apply 0. apply DefaultHeader.  Defined. *)

Definition recent p q T := 0 <= get_tstamp p - get_tstamp q < T. (*NEW: I require that difference always be nonneg. Maybe that's not necessary*)

Definition valid_flow (f : list Packet) :=
  forall i, 0 <= i < Zlength f - 1 -> recent (Znth  (i + 1) f) (Znth i f) Tc.

Lemma valid_flow_cons_inv {l p}: valid_flow (p::l) -> valid_flow l.
Proof. unfold valid_flow; intros. rewrite Zlength_cons in H.
  exploit (H (i+1)); clear H; intros. lia. rewrite 2 Znth_pos_cons in H by lia.
  replace (i + 1 + 1 - 1) with (i + 1) in H by lia.
  replace (i + 1 - 1) with i in H by lia. apply H.
Qed.
Lemma valid_flow_app_inv {l}: forall {m}, valid_flow (l++m) -> valid_flow l /\ valid_flow m.
Proof.
  induction l; simpl; intros.
+ split; trivial. red. list_solve.
+ destruct (IHl _ (@valid_flow_cons_inv (l++m) a H)); clear IHl. split; trivial.
  clear - H. red; intros. exploit (H i); clear H; list_solve.
Qed.

Lemma trans_preserves_okUntil {h}: valid_flow h -> h <> nil ->
      forall f k u,
      trans_fw f h k u ->
      let t0 := get_tstamp (Znth 0 h) in
      ok_until f t0 -> forall t', 0 <= t' - get_tstamp (Znth (Zlength h-1) h) < Tc ->
      ok_until k t'.
Proof. intros ? ? ? ? ? ?. induction H1; intros. elim H0; trivial.
destruct (valid_flow_app_inv H) as [ Hvalid _].
specialize (IHtrans_fw Hvalid).
destruct h as [| [hh ht]].
+ clear IHtrans_fw. inv H1; [ | list_solve].
  apply (fw_packet_preserves_okUntil H2); subst t0; list_solve.
+ assert (X: (hh, ht) :: h <> []) by (clear; intros N; list_solve).
  specialize (IHtrans_fw X H3).
  apply (fw_packet_preserves_okUntil H2); clear H2.
  - apply IHtrans_fw; clear IHtrans_fw. clear H4; subst t0.
    clear H3. clear - H.
    exploit (H (Zlength h)); clear H.
     * list_solve.
     * unfold Packet in *.
       replace ((@Zlength (Time * Header * Payload * Z) h + 1
                - @Zlength (Time * Header * Payload * Z)  ((hh, ht) :: h)))
       with 0 by list_solve.
       replace (@Zlength (Time * Header * Payload * Z)
            ((hh, ht) :: h) - 1)
       with (@Zlength (Time * Header * Payload * Z) h) by list_solve.
       intros X; red in X; list_solve.
   - clear- H4; unfold Packet in *.
     replace (Zlength (((hh, ht) :: h) ++ [p]) - 1) with
             (Zlength ((hh, ht) :: h)) in H4 by list_solve.
      rewrite Znth_app2, Zminus_diag in H4 by list_solve.
      rewrite Znth_0_cons in H4; lia.
Qed.

Lemma valid_flow_trans_wf: forall f (Hf: valid_flow f) s
      (Hs: match f with nil => True | hd::tl => ok_until s (get_tstamp hd) end),
      exists t r, trans_fw s f t r.
Proof. induction f; simpl; intros.
+ do 2 eexists. apply trans_nil.
+ assert (Ha: exists u r1, fw_process_packet s a u r1).
  { clear IHf. destruct a as [[[ta h] data] port].
    remember (is_gen port) as ifgen; symmetry in Heqifgen; destruct ifgen.
    - do 2 eexists. apply fw_clear. trivial.
    - remember (is_internal (SrcAddr h)) as dir; symmetry in Heqdir; destruct dir.
      + do 2 eexists. apply fw_outgoing; trivial.
      + remember (query (clear s ta) (ta, Build_Header (DstAddr h) (SrcAddr h))) as q; destruct q.
        * destruct b.
          { specialize (fw_incomingPermit s ta h data port Heqifgen Heqdir).
            rewrite <- Heqq. intros X. do 2 eexists.
            apply X. right; left; trivial. }
          { specialize (fw_incomingDrop s ta h data port Heqifgen Heqdir).
            rewrite <- Heqq. intros X. do 2 eexists.
            apply X. right; left; trivial. }
        * specialize (fw_incomingDrop s ta h data port Heqifgen Heqdir).
          rewrite <- Heqq. intros X. do 2 eexists.
          apply X. left; trivial. }
  destruct Ha as [u [r1 HHa]].
  destruct (IHf (valid_flow_cons_inv Hf) u) as [t [r2 HHf]].
  - clear IHf. destruct f; trivial. apply trans_single in HHa.
    assert (Va: valid_flow [a]) by (red; intros; list_solve).
    assert (Xa: [a] <> []) by congruence.
    apply (@trans_preserves_okUntil [a] Va Xa _ _ _ HHa Hs).
    exploit (Hf 0); clear Hf. list_solve. simpl.
    intros R; apply R.
  - exists t, (r1::r2). eapply trans_cons; eassumption.
Qed.

Definition high_level_exec (h : list Packet) (p : Packet) (res : Result) :=
  exists h' f g,
    trans_fw (empty (get_tstamp (Znth 0 (h++[p])))) h f h' /\
    fw_process_packet f p g res.

Definition property (h : list Packet) (p : Packet) (res : Result) : Prop :=
  is_gen (get_port p) = false /\ is_internal (get_src p) = false /\
    is_internal (get_dst p) = true /\
    (exists i, 0 <= i < Zlength h /\ recent p (Znth i h) T /\
            get_port p = get_port (Znth i h) /\
            get_src p = get_dst (Znth i h) /\ get_dst p = get_src (Znth i h)) ->
  isSome res.

Lemma list_nil_or_snoc {A}: forall (l:list A),
       l=[] \/ exists l1 a, l=l1++[a].
Proof.
  induction l; simpl; intros. left; trivial.
  right. destruct IHl.
+ subst. exists [], a; trivial.
+ destruct H as [l1 [aa Hl]]; subst.
  exists (a::l1), aa. trivial.
Qed.

Lemma flow_level_property : forall (h : list Packet) (p : Packet) (res : Result),
  high_level_exec h p res ->
  valid_flow (h ++ [p]) ->
  property h p res.
Proof. intros. red. intros [Hgen [Hsrc [Hdst [i [Hi [iRecent [iPort [iSrc iDst]]]]]]]].
destruct H as [result [f [g [Trans Step]]]].
destruct p as [[[tp header] data] port].

inv Step; simpl; trivial. 1: simpl in Hgen; rewrite Hgen in H7; discriminate.
(*Interesting case: DROP*)
unfold get_src, get_dst, get_port in *. simpl in *. clear H7 H8.
destruct header as [sH dH]; simpl in *.
assert (OK_f: ok_until f tp).
{ destruct (valid_flow_app_inv H0).
  eapply (trans_preserves_okUntil H).
     + intros N; subst; list_solve.
     + apply Trans.
     + rewrite Znth_app1 by list_solve. apply ok_empty.
     + clear - Hi H0. exploit (H0 (Zlength h -1)). list_solve.
        replace (Zlength h - 1 + 1) with (Zlength h) by list_solve.
        intros R; red in R. unfold get_tstamp in *.
        rewrite Znth_app2, Zminus_diag, Znth_0_cons in R by lia. simpl in R.
        rewrite Znth_app1 in R by list_solve; trivial. }
assert (query (clear f tp)
              (tp, Build_Header dH sH) = Some true);
[
|rewrite H in H9; destruct H9 as [Q | [ Q | Q]]; congruence; contradiction].
clear H9.
erewrite <- query_clear; trivial. 2:lia. unfold Packet in *.
remember ((h ++
                    [(tp, ((sH, dH) : Header),
                     data, port)])) as l in *.

exploit (split3_full_length_list 0 i (Zlength h) h Hi). lia.
rewrite Zminus_0_r; intros Hh.
assert (exists state1 res1 state2 resI res2,
  trans_fw (empty (get_tstamp (Znth 0 l)))  (firstn (Z.to_nat i) h) state1 res1 /\
  fw_process_packet state1 (Znth i h) state2 resI /\
  trans_fw state2 (skipn (Z.to_nat (i + 1)) h) f res2 /\
  result = res1++resI::res2 /\ state2 = insert state1 (fst (fst (Znth i h)))).
{ clear- Hh Trans iPort iDst iSrc Hdst Hsrc Hgen. rewrite app_assoc in Hh.
  destruct (trans_app_inv _ Trans _ Hh)
  as [ state1 [res1 [res2 [Trans1 [Trans2 R]]]]]. subst.
  inv Trans1. { symmetry in H1. apply app_eq_nil in H1; destruct H1; congruence. }
  apply app_inj_tail in H. destruct H; subst h0 p.
  do 5 eexists; split3. eassumption. eassumption.
  split3. eassumption. rewrite <- app_assoc. trivial.
  inv H2.
  - rewrite <- H in *;  simpl in *. congruence.
  - trivial.
  - rewrite <- H in *;  simpl in *. congruence.
  - rewrite <- H in *;  simpl in *. congruence. }

destruct H as [state1 [res1 [state2 [resI [res2 [Front [StepI [Tail [R HState2]]]]]]]]].
clear Trans.

assert(ValidFrontI: valid_flow ((firstn (Z.to_nat i) h) ++ [Znth i h])).
{ subst l. destruct (valid_flow_app_inv H0). clear - H Hh.
  rewrite Hh, app_assoc in H. apply (valid_flow_app_inv H). }
assert(ValidFront: valid_flow (firstn (Z.to_nat i) h)) by
  apply (valid_flow_app_inv ValidFrontI).
assert(ValidITail: valid_flow ([Znth i h] ++ skipn (Z.to_nat (i + 1)) h)).
{ subst l. destruct (valid_flow_app_inv H0). clear - H Hh.
  rewrite Hh in H. apply (valid_flow_app_inv H). }
assert (ValidTail: valid_flow (skipn (Z.to_nat (i + 1)) h)) by apply (valid_flow_app_inv ValidITail).
forget (skipn (Z.to_nat (i + 1)) h) as tail.

assert (Hstate2: state2 = insert state1 (fst (fst (Znth i h)))).
{ clear Front. inv StepI; rewrite <- H in *; trivial. }

assert (State1OK: ok_until state1 (get_tstamp (Znth i h))).
{ clear - ValidFrontI Front ValidFront Hi Heql.
  remember (firstn (Z.to_nat i) h) as front; destruct front.
  + inv Front.
    - destruct h. list_solve. simpl in *.
      remember (Z.to_nat i) as n; destruct n; simpl in Heqfront; [ | discriminate].
      assert (i=0) by lia; subst i. clear. (* clear H1 Hi Heqn; simpl in *.*)
      rewrite ! Znth_0_cons. apply ok_empty.
    - apply app_eq_nil in H; destruct H; congruence.
  + assert (HF: (p::front) <> []) by congruence. (* (rewrite <- H; intros N; apply app_eq_nil in N; destruct N; congruence).*)
    specialize (trans_preserves_okUntil ValidFront HF _ _ _ Front). subst l. simpl. rewrite ! Znth_0_cons. intros H.
    apply H; clear H Front.
    * destruct h; simpl.
      - destruct (Z.to_nat i); simpl in Heqfront; congruence.
      - rewrite Znth_0_cons; simpl.
        remember (Z.to_nat i) as n; destruct n; simpl in *; inv Heqfront.
        apply ok_empty.
    * red in ValidFrontI.
      exploit (ValidFrontI (Zlength front)).
      - unfold Packet in *; list_solve.
      - clear - HF. replace (Znth (Zlength front + 1) ((p :: front) ++ [Znth i h])) with (Znth i h) by list_solve.
        replace (Znth (Zlength front) ((p :: front) ++ [Znth i h]))
        with (Znth (Zlength (p :: front) - 1) (p :: front)) by list_solve.
        trivial. }

assert (State2OK: forall t', 0 <= t' - get_tstamp (Znth i h) < Tc ->
      ok_until state2 t').
1: intros; apply (fw_packet_preserves_okUntil StepI); [ trivial | lia].

clear Front.
forget (firstn (Z.to_nat i) h) as front.
clear ValidFront StepI.
assert (ValidTailTp: valid_flow (tail++[(tp, ((sH, dH) : Header), data, port)])).
{ clear - Hh Heql H0. subst l.  rewrite Hh in H0.
  rewrite <- app_assoc in H0.
  apply valid_flow_app_inv in H0. destruct H0 as [_ HH].
  rewrite <- app_assoc in HH.
  apply (valid_flow_app_inv HH). }
assert (QI: query (insert state1 (fst (fst (Znth i h))))
   (tp, ((dH, sH) : Header)) = Some true).
{ subst sH dH. destruct (Znth i h). simpl in *.
  destruct p; simpl in *. destruct p. simpl in *. destruct h0. simpl in *.
  apply query_insert_same.
  + simpl in *.
    clear - iRecent. red in iRecent. unfold get_tstamp in *. simpl in *. lia.
  + apply State1OK. }
rewrite <- Hstate2 in *.
clear - ValidITail State2OK ValidTailTp Tail QI iRecent.
forget (Znth i h) as packetI.
(*rewrite <- H2; clear H2.*)
unfold Build_Header in *.
forget (dH, sH) as headerP.
forget (sH, dH) as headerI.
clear sH dH h.
generalize dependent packetI.

 (*generalize dependent tp.*) generalize dependent res2. generalize dependent f.
generalize dependent state2.
induction tail; intros.
+ inv Tail. trivial. apply app_eq_nil in H; destruct H; congruence.
+ destruct (@trans_cons_inv tail (a :: tail) _ _ _ Tail _ (eq_refl _))
  as [k [resA [resB [FwA [TransB RES]]]]]; clear Tail.
  assert (VF: valid_flow
           (tail ++ [(tp, headerI, data, port)])).
  { replace (a :: tail) with ([a]++tail) in ValidTailTp by reflexivity.
    rewrite <- app_assoc in ValidTailTp. apply (valid_flow_app_inv ValidTailTp). }
  assert (Ht_packetI: 0 <= get_tstamp a - get_tstamp packetI < Tc).
  { exploit (ValidITail 0). unfold Packet in *; list_solve.
    simpl. rewrite Znth_pos_cons, Zminus_diag, ! Znth_0_cons by list_solve.
    intros H; apply H. }
  assert(OK_g_a: ok_until state2 (get_tstamp a)).
  { apply State2OK; trivial. }
  assert (H_a_tp: (get_tstamp a) <= tp).
  { clear - ValidTailTp. generalize dependent a. induction tail; simpl; intros.
    ** exploit (ValidTailTp 0); clear ValidTailTp. unfold Packet in *; list_solve.
       simpl. unfold recent; intros. unfold get_tstamp in *.
       rewrite Znth_pos_cons, Zminus_diag, ! Znth_0_cons in H. simpl in H. lia. lia.
    ** unfold Header in *.
       replace (a0 :: a :: tail ++ [(tp, headerI, data, port)]) with ([a0] ++ ( a :: tail ++ [(tp, headerI, data, port)])) in ValidTailTp by reflexivity.
       destruct (valid_flow_app_inv ValidTailTp).
       apply IHtail in H0; clear IHtail.
       replace ([a0] ++ a :: tail ++ [(tp, headerI, data, port)])
           with (([a0;a] ++ (tail ++ [(tp, headerI, data, port)]))) in ValidTailTp by reflexivity.
       destruct (valid_flow_app_inv ValidTailTp).
       exploit (H1 0); clear - H0. unfold Packet, Header in *; list_solve.
       simpl. rewrite Znth_pos_cons, Zminus_diag, ! Znth_0_cons by list_solve. intros.
       red in H.  unfold get_tstamp in *. lia. }
  assert (Hk: query k (tp, headerP) = Some true).
  { clear IHtail TransB.
    inv FwA.
    + rewrite <- query_clear; trivial.
    + apply query_insert_other; trivial.
    + rewrite <- query_clear; trivial.
    + rewrite <- query_clear; trivial. }
  apply (IHtail VF _ Hk  _ _ TransB a); clear IHtail.
  - clear - iRecent ValidITail ValidTailTp H_a_tp. red.
    red in iRecent. exploit (ValidITail 0); clear ValidITail; simpl. unfold Packet in *; list_solve.
    intros. rewrite Znth_pos_cons,Zminus_diag, ! Znth_0_cons in H by list_solve.
    red in H. unfold get_tstamp in *. simpl in *; lia.
  - apply (valid_flow_app_inv ValidITail).
  - specialize (fw_packet_preserves_okUntil FwA). intros. apply H; clear H.
    * trivial.
    * lia.
Qed.

Lemma full_property h p (Vp: valid_flow (h ++ [p])):
  (exists res, high_level_exec h p res) /\
  (forall res, high_level_exec h p res -> property h p res).
Proof. destruct (valid_flow_trans_wf _ Vp (empty (get_tstamp (Znth 0 (h++[p]))))) as [t [r Hr]].
  + destruct h; simpl; apply ok_empty.
  + split.
    - unfold high_level_exec. inv Hr.
      * symmetry in H1; apply app_eq_nil in H1; destruct H1; congruence.
      * apply app_inj_tail in H. destruct H; subst p0 h0.
        do 4 eexists. split; eassumption.
    - intros. eapply flow_level_property; trivial.
Qed.
