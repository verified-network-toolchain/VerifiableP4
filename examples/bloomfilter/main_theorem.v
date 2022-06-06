Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Coq.Program.Program.
Require Import Poulet4.Utils.Maps.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.general_bf.
Require Import ProD3.examples.bloomfilter.switch.
Require Import ProD3.examples.bloomfilter.verif.

Require Import VST.zlist.Zlist.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Require Import ProD3.core.Coqlib.

Definition process' (bf : bloomfilter_state) (p : Z * port) :=
  let (data, pt) := p in
  match pt with
  | port_int =>
      (general_bf.add CRC_pads bf data, (Some (data, port_ext)))
  | port_ext =>
      if general_bf.query (`CRC_pads) bf data then
        (bf, Some (data, port_int))
      else
        (bf, None)
  end.

Definition bf_encode (es : V1Model.extern_state) (bf : bloomfilter_state) :=
  PathMap.get ["bloom0"] es = Some (reg_encode (Znth 0 (` (blooms bf))))
  /\ PathMap.get ["bloom1"] es = Some (reg_encode (Znth 1 (` (blooms bf))))
  /\ PathMap.get ["bloom2"] es = Some (reg_encode (Znth 2 (` (blooms bf)))).

Open Scope Z_scope.

Lemma process_packet_prop : forall es bf p es' p',
  process_packet ge custom_metadata_t es p es' p' ->
  bf_encode es bf ->
  exists bf',
    process' bf p = (bf', p') /\ bf_encode es' bf'.
Proof.
  intros.
  inv H.
  inv H1. inv H2.
  apply (proj1 bloomfilter_body (port_to_Z in_port) data bf) in H6; auto.
  2 : {
    destruct in_port; simpl; lia.
  }
  2 : {
    clear H5.
    split. {
      simpl. unfold AssertionLang.arg_denote, AssertionLang.arg_satisfies.
      destruct in_port; Tactics.Forall2_sval_refine.
    }
    split. {
      repeat constructor.
    }
    destruct H0 as [? []].
    repeat constructor.
    - red; simpl; destruct (PathMap.get ["bloom0"] es); inv H; auto.
    - red; simpl; destruct (PathMap.get ["bloom1"] es); inv H0; auto.
    - red; simpl; destruct (PathMap.get ["bloom2"] es); inv H1; auto.
  }
  destruct H6 as  [? [? []]].
  exists (fst (process (port_to_Z in_port) data bf)).
  split.
  2 : {
    unfold encode_bloomfilter_state, AssertionNotations.EXT, id in H6.
    destruct H6 as [[? [? ?]] []]. unfold blooms. simpl.
    repeat constructor.
    - red in H6; simpl in H6; destruct (PathMap.get ["bloom0"] es'); inv H6; auto.
    - red in H7; simpl in H7; destruct (PathMap.get ["bloom1"] es'); inv H7; auto.
    - red in H8; simpl in H8; destruct (PathMap.get ["bloom2"] es'); inv H8; auto.
  }
  assert (data' = data
    /\ out_port_to_Z out_port = snd (process (port_to_Z in_port) data bf)).
  {
    inv H.
    split.
    - clear -H3 H4 H10.
      subst hdr'.
      inv H10. inv H1. destruct H5.
      clear -H3 H4 H0. inv H0. inv H7. destruct H2.
      clear -H3 H4 H0.
      apply Members.sval_refine_to_loptbool_eq in H0; eauto.
    - inv H12. inv H13.
      clear -H5 H11.
      apply Members.sval_refine_get with (f := "egress_spec") in H11.
      simpl in H11.
      rewrite H5 in H11.
      apply Members.sval_refine_to_loptbool_eq in H11; eauto.
      + destruct in_port; simpl.
        2 : destruct (query [CRC_pad0; CRC_pad1; CRC_pad2] bf data); simpl.
        all : lia.
      + destruct out_port as [[] | ]; simpl.
        all : lia.
  }
  clear -H7.
  destruct H7; subst.
  unfold process, process' in *.
  destruct in_port; destruct out_port as [[] | ];
    simpl in *; try solve [inv H0]; auto;
    destruct (query [CRC_pad0; CRC_pad1; CRC_pad2] bf data);
    try solve [inv H0]; auto.
Qed.

Definition packet1: BinNums.Z * port := (Z0, port_int).
Definition packet2: BinNums.Z * port := (1%Z, port_ext).

Program Definition test_row: row NUM_ENTRY := Zrepeat false NUM_ENTRY.

Program Definition test_frame: frame 3 NUM_ENTRY := Zrepeat test_row 3.

Lemma Test1: forall st' output,
     @process_packets _ _ ge custom_metadata_t  init_es  [packet1;packet2] st' output ->
     bf_encode st' (add CRC_pads test_frame 0) /\
    output = [Some (0, port_ext); None].
Proof.
intros. inv H.
assert (Bf: bf_encode init_es test_frame).
{ split. reflexivity. split; reflexivity. }
eapply process_packet_prop in H3;
  [clear Bf; destruct H3 as [bf1 [Proc1 Bf1]] | eassumption].
inv Proc1. inv H6.
eapply process_packet_prop in H2; [ clear Bf1; destruct H2 as [bf2 [Proc2 Bf2]] | eassumption]. inv H5. unfold packet2 in Proc2. cbn [process'] in Proc2.
cut (query (`CRC_pads) (add CRC_pads test_frame 0) 1 = false).
- intros. rewrite H in Proc2. inv Proc2. split; auto.
- unfold query, frame_query, add, frame_insert, row_insert, Utils.map2, row_query.
  simpl. rewrite !Znth_upd_Znth_diff; [|vm_compute; lia..].
  rewrite !Znth_Zrepeat; [| apply CRC_range..].
  now simpl.
Qed.

Definition packet1': BinNums.Z * port := (Z0, port_int).
Definition packet2': BinNums.Z * port := (Z0, port_ext).

Lemma Test2: forall es' output,
     @process_packets _ _ ge custom_metadata_t  init_es  [packet1';packet2'] es' output ->
     bf_encode es' (add CRC_pads test_frame 0) /\
     output = [Some (0, port_ext); Some (0, port_int)].
Proof.
intros. inv H.
assert (Bf: bf_encode init_es test_frame).
{ split. reflexivity. split; reflexivity. }
eapply process_packet_prop in H3;
  [ clear Bf; destruct H3 as [bf1 [Proc1 Bf1]] |eassumption].
inv Proc1. inv H6.
eapply process_packet_prop in H2;
  [ clear Bf1; destruct H2 as [bf2 [Proc2 Bf2]] | eassumption]. inv H5.
unfold packet2' in Proc2. cbn [process'] in Proc2.
cut (query (`CRC_pads) (add CRC_pads test_frame 0) 0 = true).
- intros. rewrite H in Proc2. inv Proc2. split; auto.
- apply bf_add_query_true. simpl.
  do 3 (constructor; [intro; apply CRC_range |]). constructor.
Qed.

Fixpoint multi_process (bf : bloomfilter_state) (l :list (Z * port)): bloomfilter_state * list (option (Z * port)) :=
  match l with
     nil => (bf, nil)
  | h::t => match process' bf h with
            (bf1, out) => match multi_process bf1 t with
                           (bf2, out2) => (bf2, out::out2)
                          end
            end
  end.

Lemma multi_process_length: forall l bf bf2 out, multi_process bf l = (bf2, out) -> length out = length l.
Proof. induction l; simpl; intros. inv H; trivial.
destruct (process' bf a). remember (multi_process f l) as x; symmetry in Heqx; destruct x. inv H.
apply IHl in Heqx. simpl; rewrite Heqx; trivial.
Qed.

Lemma multi_process_app_inv: forall l1 l2 bf bf2 out, multi_process bf (l1++l2) = (bf2, out) ->
      exists bf1 out1 out2, multi_process bf l1 = (bf1, out1) /\ multi_process bf1 l2 = (bf2, out2) /\ out=out1++out2.
Proof.
  induction l1; simpl; intros.
+ do 3 eexists; split. reflexivity. split; eauto.
+ destruct (process' bf a) as [bf0 out0].
  specialize (IHl1 l2 bf0).
  remember ( multi_process bf0 (l1 ++ l2)) as mp; symmetry in Heqmp; destruct mp. inv H.
  specialize (IHl1 _ _ (eq_refl _)). destruct IHl1 as [bf1 [out1 [out2 [MP1 [MP2 L]]]]]. subst.
  rewrite MP1. do 3 eexists; split. reflexivity. rewrite MP2. split; eauto.
Qed.

Lemma multi_process_prop : forall es bf p es' p',
  process_packets ge custom_metadata_t es p es' p' ->
  bf_encode es bf ->
  exists bf',
    multi_process bf p = (bf', p') /\ bf_encode es' bf'.
Proof. intros. generalize dependent bf. induction H; simpl; intros.
- exists bf; split; auto.
- eapply process_packet_prop in H. 2: eassumption.
  destruct H as [bf2 [K1 BF2]]; rewrite K1; clear K1.
  destruct (IHprocess_packets _ BF2) as [bf3 [K2 BF3]]. rewrite K2; clear K2.
  eexists; split. reflexivity. auto.
Qed.

Lemma process_packets_app_inv: forall l1 l2 es es2 output,
     @process_packets _ _ ge custom_metadata_t es (l1++l2) es2 output ->
      exists es1 output1 output2, output = output1 ++ output2 /\
     @process_packets _ _ ge custom_metadata_t es l1 es1 output1 /\
     @process_packets _ _ ge custom_metadata_t es1 l2 es2 output2.
Proof.
 intros l1. induction l1; simpl; intros.
+ do 3 eexists. split. 2:{ split. apply process_packets_nil. eassumption. }
  reflexivity.
+ inv H. apply IHl1 in H6; clear IHl1. destruct H6 as [es1 [out1 [out2 [X [PP1 PP2]]]]]; subst.
  do 3 eexists; split.
  2:{ split. eapply process_packets_cons; eassumption. eassumption. }
  reflexivity.
Qed.

Lemma process_packets_app_inv_encode: forall l1 l2 es es2 output bf,
    @process_packets _ _ ge custom_metadata_t es (l1++l2) es2 output ->
    bf_encode es bf ->
      exists es1 output1 output2 bf1 bf2, output = output1 ++ output2 /\
     @process_packets _ _ ge custom_metadata_t es l1 es1 output1 /\ multi_process bf l1 = (bf1, output1) /\ bf_encode es1 bf1 /\
     @process_packets _ _ ge custom_metadata_t es1 l2 es2 output2 /\ multi_process bf1 l2 = (bf2, output2) /\ bf_encode es2 bf2.
Proof.
  intros. apply process_packets_app_inv in H.
  destruct H as [es1 [out1 [out2 [Hout [P1 P2]]]]].
  destruct (multi_process_prop _ _ _ _ _  P1 H0) as [bf1 [PR1 BF1]].
  destruct (multi_process_prop _ _ _ _ _  P2 BF1) as [bf2 [PR2 BF2]].
  do 5 eexists; split. apply Hout.
  split. eassumption.
  split. eassumption.
  split. eassumption.
  split. eassumption.
  split. eassumption. eassumption.
Qed.

Lemma process_packets_length: forall l es1 es2 output,
     @process_packets _ _ ge custom_metadata_t es1 l es2 output ->
      length output = length l.
Proof. intros. induction H; simpl. trivial. f_equal; trivial. Qed.

Lemma CRC_pads_in_range:
  Forall (hash_in_range NUM_ENTRY) (`CRC_pads).
Proof.
  unfold CRC_pads. simpl. do 3 (constructor; [intro; apply CRC_range |]). constructor.
Qed.

Lemma multi_process_firewall_aux: forall {l bf z bf1 bf' a out2 out1},
process' (add CRC_pads bf z) a = (bf1, out1) ->
multi_process bf1 l = (bf', out2) ->
query (`CRC_pads) bf' z = true.
Proof.
induction l; simpl; intros.
- inv H0. destruct a. destruct p; simpl in H.
  + inv H. rewrite add_comm. apply bf_add_query_true. apply CRC_pads_in_range.
  + destruct (query [CRC_pad0; CRC_pad1; CRC_pad2]
                (add CRC_pads bf z) z0);
      inv H; apply bf_add_query_true; apply CRC_pads_in_range.
- remember (process' bf1 a) as x; symmetry in Heqx; destruct x as [bf3 out3].
  remember (multi_process bf3 l) as y; symmetry in Heqy; destruct y as [bf4 out4].
  inv H0. destruct a0 as [zz q]. destruct q.
  + simpl in H. rewrite add_comm in H. inv H. eapply IHl; eauto.
  + simpl in H.
    remember (query [CRC_pad0; CRC_pad1; CRC_pad2]
                (add CRC_pads bf z) zz) as u;
      symmetry in Hequ; destruct u; inv H; eauto.
Qed.

Lemma multi_process_firewall_endpoints z: forall l bf bf' out,
multi_process bf ((z, port_int)::l++[(z, port_ext)]) = (bf', out) ->
exists m, out = (Some (z, port_ext)::m++[Some (z, port_int)]).
Proof.
  induction l; simpl; intros.
  - change [CRC_pad0; CRC_pad1; CRC_pad2] with (`CRC_pads) in H.
    rewrite bf_add_query_true in H by (apply CRC_pads_in_range).
    inv H. exists (@nil(option (Z * port))). reflexivity.
  - remember (process' (add CRC_pads bf z) a) as x; symmetry in Heqx; destruct x as [bf1 out1].
  remember (multi_process bf1 (l ++ [(z, port_ext)])) as y; symmetry in Heqy; destruct y. inv H.
  apply multi_process_app_inv in Heqy. destruct Heqy as [bf2 [out2 [out3 [MP1 [MP2 X]]]]]. subst l0.
  simpl in MP2.
  remember (query [CRC_pad0; CRC_pad1; CRC_pad2] bf2 z). destruct b.
  + inv MP2. exists (out1::out2). simpl; trivial.
  + change [CRC_pad0; CRC_pad1; CRC_pad2] with (`CRC_pads) in Heqb.
    rewrite (multi_process_firewall_aux Heqx MP1) in Heqb. discriminate.
Qed.

Lemma multi_process_firewall {l1 l2 l3 bf bf' out z}:
  multi_process bf (l1++(z, port_int)::l2++[(z, port_ext)]++l3) = (bf', out) ->
exists m1 m2 m3, out = m1++(Some (z, port_ext))::m2++[Some (z, port_int)]++m3 /\
      length m1=length l1 /\ length m2 = length l2 /\ length m3=length l3.
Proof.
  intros.
  destruct (multi_process_app_inv _ _ _ _ _  H) as [bf1 [m1 [out1 [P1 [Ptail1 X]]]]]; subst out; clear H.
  specialize (multi_process_app_inv ((z, port_int) :: l2 ++ [(z, port_ext)]) l3 bf1 bf' out1). intros.
simpl in H. simpl in Ptail1. rewrite <- app_assoc in H. specialize (H Ptail1); clear Ptail1.
destruct H as [bf3 [out2 [out3 [ST [P3 Hout]]]]]; subst out1.
remember (multi_process (add CRC_pads bf1 z) (l2 ++ [(z, port_ext)]) ) as x; symmetry in Heqx; destruct x.
inv ST.
specialize (multi_process_firewall_endpoints z l2 bf1). simpl; intros.
rewrite Heqx in H. destruct (H _ _ (eq_refl _)) as [m2 M2]; clear H.
inv M2. exists m1, m2, out3. rewrite <- app_assoc. simpl. split. trivial.
apply multi_process_length in P1. split; trivial.
apply multi_process_length in P3. split; trivial.
apply multi_process_length in Heqx. rewrite 2 app_length in Heqx. simpl in Heqx. lia.
Qed.

Lemma process_packets_firewall {l1 l2 l3 es es' out z bf}:
      process_packets ge custom_metadata_t es (l1++(z, port_int)::l2++[(z, port_ext)]++l3) es' out -> bf_encode es bf ->
  exists bf', bf_encode es' bf' /\
  exists m1 m2 m3, out = m1++(Some (z, port_ext))::m2++[Some (z, port_int)]++m3 /\
      length m1=length l1 /\ length m2 = length l2 /\ length m3=length l3.
Proof.
  intros.
  destruct (multi_process_prop _ _ _ _ _ H H0) as [bf' [MP BF']].
  exists bf'; split; [trivial.. |].
  apply (multi_process_firewall MP).
Qed.

(*
(*intermediate property, likely to be deleted eventally*)
Lemma Firewall': forall l1 l2 l3 es es' output bf,
     @process_packets _ _ ge custom_metadata_t es (l1++packet1'::l2++packet2'::l3) es' output -> bf_encode es bf ->
     exists out1 out2 out3 act1 act2,
     output = out1++act1::out2++act2::out3 /\
     length out1 = length l1 /\ length out2 = length l2 /\ length out3 = length l3.
Proof. intros.
  destruct (process_packets_app_inv_encode _ _ _ _ _ _ H H0) as [es1 [out1 [tail1 [bf1 [bftail [Hout [P1 [MP1 [BF1 [Tail1 [MTail1 BFtail1]]]]]]]]]]]; subst.
  clear H.
  apply process_packets_length in P1. clear MTail1 MP1. (*for now*)
  exists out1; rewrite P1.
  inv Tail1.
  destruct (process_packet_prop _ _ _ _ _ H3 BF1) as [bf2 [PR2 BF2]]. clear H3.
  destruct (process_packets_app_inv_encode _ _ _ _ _ _ H6 BF2) as [es3 [out2 [tail2 [bf3 [bftail3 [Hout [P2 [MP3 [BF3 [Tail3 [MTail3 BFtail3]]]]]]]]]]]; subst.
  clear H6.
  apply process_packets_length in P2. clear MTail3 MP3. (*for now*)
  exists out2; rewrite P2.
  inv Tail3.
  destruct (process_packet_prop _ _ _ _ _ H3 BF3) as [bf4 [PR4 BF4]]. clear H3.
  specialize (process_packets_length _ _ _ _ H6); intros.
  exists ps'; rewrite H.
  do 2 eexists. split. reflexivity. split; eauto.
Qed.
Require Import VST.zlist.Zlist.

Lemma app_inv {A}: forall (l1 l2 m1 m2:list A), l1++l2 = m1++m2 -> length l1=length m1 -> l1=m1 /\  l2=m2.
Proof.
induction l1; simpl; intros.
+ destruct m1; inv H0. split; trivial.
+ destruct m1; inv H0. inv H. destruct (IHl1 _ _ _ H3 H2); subst. split; trivial.
Qed.

Lemma multi_process_firewall_nth n m l bf bf' out z (H: (n<m<length l)%nat):
      multi_process bf l = (bf', out) ->
      nth_error l n = Some (z, port_int) -> nth_error l m = Some (z, port_ext) ->
      nth_error l n = Some (z, port_ext) /\ nth_error l m = Some (z, port_int).
Proof. intros.
destruct (@multi_process_firewall (firstn n l) (firstn m (skipn (S n) l)) (skipn (S (S (m+n))) l) bf bf' out z)
  as [m1 [m2 [m3 [M [M1 [M2 M3]]]]]].
+ assert (L: l = (firstn n l ++ (z, port_int) :: (firstn m (skipn (S n) l)) ++ [(z, port_ext)] ++ skipn (S (S (m + n))) l)).
  { clear H0. apply nth_error_split in H1. destruct H1 as [l1 [l2 [Hl Len1]]].
    specialize (firstn_skipn n l); intros X. rewrite <- X at 1. f_equal. symmetry in X.
    assert (Datatypes.length l1 = Datatypes.length (firstn n (l1 ++ (z, port_int) :: l2))).
    {  rewrite firstn_length, app_length; simpl. rewrite Nat.min_l; trivial. lia. }
    rewrite Hl in X. destruct (app_inv  _ _ _ _ X H0). clear X.
    erewrite (skipn_cons (S n)). intros.
Search app length.

 subst.  Search nth_error app. rewrite <-(firstn_skipn n l) at 1. f_equal.
    intros L.  rewrite <- L at 1. firstn_skipnSearch firstn app skipn.
  rewrite <- L; trivial.


 Search nth_error.
 ++m3 /\

Definition DummyEntry: (Z * port) := (0, port_int).

Lemma multi_process_firewall_nth n m l bf bf' out z (H: (n<m<length l)%nat):
      multi_process bf l = (bf', out) ->
      nth n l DummyEntry = (z, port_int) ->
      nth m l DummyEntry = (z, port_ext) ->
      nth n l DummyEntry = (z, port_ext) /\ nth m l DummyEntry = (z, port_int).
Proof. Search nth_error.
 ++m3 /\
      length m1=length l1 /\ length m2 = length l2 /\ length m3=length l3.
Search length.
Check nth.
multi_process bf (l1++(z, port_int)::l2++[(z, port_ext)]++l3) = (bf', out)
   X].

Search process_packets.
 destruct (multi_process_app_inv _ _ _ _ _  H) as [bf1 [m1 [out1 [P1 [Ptail1 X]]]]]; subst out; clear H.
Proof. intros. specialize (multi_process_app_inv ((z, port_int) :: l2 ++ [(z, port_ext)]) l3 bf1 bf' out1). intros.
simpl in H. simpl in Ptail1. rewrite <- app_assoc in H. specialize (H Ptail1); clear Ptail1.
destruct H as [bf3 [out2 [out3 [ST [P3 Hout]]]]]; subst out1.
remember (multi_process (add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf1 z) (l2 ++ [(z, port_ext)]) ) as x; symmetry in Heqx; destruct x.
inv ST.
specialize (multi_process_query_endpoints z l2 bf1). simpl; intros.
rewrite Heqx in H. destruct (H _ _ (eq_refl _)) as [m2 M2]; clear H.
inv M2. exists m1, m2, out3. rewrite <- app_assoc. simpl. split. trivial.
apply multi_process_length in P1. split; trivial.
apply multi_process_length in P3. split; trivial.
apply multi_process_length in Heqx. rewrite 2 app_length in Heqx. simpl in Heqx. lia.
Qed.

Require Import VST.zlist.Zlist.


Lemma multi_process_query' n m l bf bf' out z (H: n<m):
      multi_process bf l = (bf', out) ->
      Znth n l = (z, port_int) ->
      Znth m l = (z, port_ext) ->
      Znth n l = (z, port_ext) /\ Znth m l = (z, port_int). ++m3 /\
      length m1=length l1 /\ length m2 = length l2 /\ length m3=length l3.
Search Datatypes.length app. split; trivial.

*)
