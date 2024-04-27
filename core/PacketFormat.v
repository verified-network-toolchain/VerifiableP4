Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.Monads.Packet.
Require Import Poulet4.P4light.Semantics.Extract.
Require Export Poulet4.P4light.Semantics.Typing.ValueTyping.

Notation packet := (list bool).

Section PacketFormat.

  Context {tags_t: Type}.
  Notation Val := (@ValueBase bool).
  Notation P4Type := (@P4Type tags_t).

  Fixpoint encode (val: Val): packet :=
    match val with
    | ValBaseBool b => [b]
    | ValBaseBit bit => bit
    | ValBaseInt bit => bit
    | ValBaseTuple l => concat (map encode l)
    | ValBaseStruct vs => concat (map (fun '(_, v) => encode v) vs)
    | ValBaseHeader fields true => concat (map (fun '(_, v) => encode v) fields)
    | _ => []
    end.

  Fixpoint is_packet_typ (typ: P4Type) : bool :=
    match typ with
    | TypBool
    | TypBit _
    | TypInt _ => true
    | TypTuple l => forallb is_packet_typ l
    | TypHeader flds
    | TypStruct flds => AList.key_unique flds &&
                         forallb (is_packet_typ ∘ snd) flds
    | _ => false
    end.

  Fixpoint header_rec_valid (val: Val) : bool :=
    match val with
    | ValBaseHeader _ false => false
    | ValBaseStruct fields
    | ValBaseHeader fields true => forallb (header_rec_valid ∘ snd) fields
    | ValBaseTuple l => forallb header_rec_valid l
    | _ => true
    end.

  Ltac auto_unfold :=
    repeat match goal with
    | [ |- context [Packet.packet_bind]] => unfold Packet.packet_bind
    | [ |- context [Packet.packet_ret]] => unfold Packet.packet_ret
    | [ |- context [ExceptionState.state_bind]] => unfold ExceptionState.state_bind
    | [ |- context [ExceptionState.get_state]] => unfold ExceptionState.get_state
    | [ |- context [ExceptionState.state_return]] =>
        unfold ExceptionState.state_return
      end.

  Ltac simpl_more :=
    repeat match goal with
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H; destruct H
      | H: forallb header_rec_valid (_ :: _) = true |- _ => simpl in H
      | H: is_packet_typ (TypTuple (_ :: _)) = true |- _ => simpl in H
      | H: is_packet_typ (TypStruct _) = true |- _ => simpl in H
      | H: is_packet_typ (TypHeader _) = true |- _ => simpl in H
      | H1: ?P, H2: ?P -> _ |- _ => specialize (H2 H1); clear H1
      | H: _ /\ _ |- _ => destruct H
      | H: (if ?b then _ else false) = true |- _ => destruct b; [|discriminate]
      end.

  Lemma extract_bits_app: forall bits pkt,
      Packet.extract_bits (length bits) (bits ++ pkt) = (inl bits, pkt).
  Proof.
    intros. unfold Packet.extract_bits. simpl.
    auto_unfold. unfold Packet.verify, Packet.pkt_min_size.
    cut ((length bits <=? length (bits ++ pkt))%nat = true).
    - intros. rewrite H. simpl. rewrite firstn_app2, skipn_app2 by lia.
      rewrite Nat.sub_diag, app_nil_r. reflexivity.
    - rewrite Nat.leb_le, app_length. lia.
  Qed.

  Definition ext_val_typ (val: Val) (typ: P4Type): Prop :=
    ⊢ᵥ val \: typ /\ header_rec_valid val = true.

  Lemma extract_encode_raw: forall (typ: P4Type) (val: Val) pkt,
      ext_val_typ val typ  ->
      is_packet_typ typ = true ->
      Extract.extract typ (encode val ++ pkt) = (inl val, pkt).
  Proof.
    intros ? ? ? [] ?. revert pkt.
    induction H using custom_val_typ_ind; simpl in H0;
      try discriminate; intros; simpl; rewrite ?Nat2N.id; auto_unfold;
      rewrite ?extract_bits_app; try reflexivity.
    - induction H; simpl; auto. auto_unfold. inv H2. simpl_more.
      rewrite <- app_assoc, H7.
      remember (sequence (map Extract.extract l') (concat (map encode l) ++ pkt)).
      destruct p, s; inversion IHForall2. reflexivity.
    - simpl_more. clear H H1. remember (clear_AList_tags ts) as cs.
      revert dependent ts.
      induction H2; intros; destruct ts as [|[k v] ts]; try discriminate; auto.
      simpl in *. auto_unfold. inv Heqcs. inv H3. simpl_more.
      destruct x. simpl in *. subst s. clear H4. rewrite <- app_assoc, H5.
      specialize (IHForall2 ts ltac:(reflexivity) H3). clear H3 H5.
      remember (asequence (map (fun '(k, v) => (str k, Extract.extract v)) ts)
                  (concat (map (fun '(_, v) => encode v) l) ++ pkt)).
      destruct p, s; inversion IHForall2. reflexivity.
    - simpl_more. clear H H1. remember (clear_AList_tags ts) as cs.
      revert dependent ts.
      induction H2; intros; destruct ts as [|[k v] ts];
        try discriminate; simpl_more; auto.
      simpl in *. auto_unfold. inv Heqcs. inv H3. simpl_more.
      destruct x. simpl in *. subst s. clear H5. rewrite <- app_assoc, H6.
      specialize (IHForall2 ts ltac:(reflexivity) H4). clear H4 H6.
      remember (asequence (map (fun '(k, v) => (str k, Extract.extract v)) ts)
                  (concat (map (fun '(_, v) => encode v) l) ++ pkt)).
      destruct p, s; inversion IHForall2. reflexivity.
  Qed.

  Lemma emit_encode_raw: forall (typ: P4Type) (val: Val) pkt,
      ⊢ᵥ val \: typ  ->
      is_packet_typ typ = true ->
      Extract.emit val pkt = (inl tt, pkt ++ encode val).
  Proof.
    intros ? ? ? ? ?. revert pkt.
    induction H using custom_val_typ_ind;
      try discriminate; intros; simpl; rewrite ?Nat2N.id; auto_unfold;
      try reflexivity.
    - revert pkt. induction H; intros; simpl. 1: now rewrite app_nil_r.
      auto_unfold. inv H1. simpl_more. rewrite H6.
      specialize (IHForall2 (pkt ++ encode x)).
      remember (sequence (map Extract.emit l) (pkt ++ encode x)).
      destruct p, s; inversion IHForall2. rewrite app_assoc. reflexivity.
    - simpl_more. clear H H0. remember (clear_AList_tags ts) as cs.
      revert pkt. revert dependent ts.
      induction H1; intros; destruct ts as [|[k v] ts]; try discriminate.
      1: simpl; rewrite app_nil_r; reflexivity.
      simpl in *. auto_unfold. inv Heqcs. inv H2. simpl_more.
      destruct x. simpl in *. subst s. clear H3. rewrite H4.
      specialize (IHForall2 ts ltac:(reflexivity) H2 (pkt ++ encode v0)).
      remember (asequence (map (fun '(k0, v1) => (k0, Extract.emit v1)) l)
                  (pkt ++ encode v0)).
      destruct p, s; inversion IHForall2. rewrite app_assoc. reflexivity.
    - simpl_more. clear H H0. remember (clear_AList_tags ts) as cs.
      revert pkt. revert dependent ts.
      induction H1; intros; destruct ts as [|[k v] ts];
        try discriminate; simpl_more; destruct b; simpl;
        rewrite ?app_nil_r; try reflexivity.
      simpl in *. auto_unfold. inv Heqcs. inv H2. simpl_more.
      destruct x. simpl in *. subst s. clear H4. rewrite H5.
      specialize (IHForall2 ts ltac:(reflexivity) H3 (pkt ++ encode v0)).
      remember (asequence (map (fun '(k0, v1) => (k0, Extract.emit v1)) l)
                  (pkt ++ encode v0)).
      destruct p, s; inversion IHForall2. rewrite app_assoc. reflexivity.
  Qed.

  Ltac make_it_clear :=
    repeat lazymatch goal with
      | H: _ /\ _ |- _ => destruct H
      | H: _ && _ = true |- _ => rewrite andb_true_iff in H
      | H: S _ = S _ |- _ => inversion H; clear H
      | H: Forall2 _ (_ :: _) (_ :: _) |- _ => inversion H as [| x l y l' ?]; subst x l y l'; clear H
      | H: AList.all_values _ (_ :: _) (_ :: _) |- _ => inversion H as [| x l y l' ?]; subst x l y l'; clear H
      | H: context [fst (_, _)] |- _ => simpl fst in H
      | H: context [snd (_, _)] |- _ => simpl snd in H
      | H: context [(_ ∘ snd) (_, _)] |- _ => unfold Basics.compose in H
      end.

  Lemma encode_same_type_same_length: forall (typ: P4Type) (val1 val2: Val),
      ext_val_typ val1 typ -> ext_val_typ val2 typ ->
      length (encode val1) = length (encode val2).
  Proof.
    intros. destruct H as [? ?]. destruct H0 as [? ?].
    revert dependent val2.
    induction H using custom_val_typ_ind; intros val2 Hs ?; inv Hs; simpl; try reflexivity.
    1,2: rewrite <- Nat2N.id, H3, Nat2N.id; reflexivity.
    - simpl in H1, H2. remember (length ts) as n. pose proof (Forall2_length _ _ _ H).
      pose proof (Forall2_length _ _ _ H5). rewrite <- Heqn in H3, H4. symmetry in Heqn.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in H4, H3. subst. simpl. reflexivity.
      + destruct vs0 as [|v2 vs2]; [simpl in H4; discriminate|].
        destruct vs as [|v1 vs1]; [simpl in H3; discriminate|].
        destruct ts as [|t ts]; [simpl in Heqn; discriminate|]. simpl in *.
        make_it_clear. specialize (H5 H1 _ H3 H2). rewrite !app_length, H5. f_equal. eapply IHn; eauto.
    - simpl in H1, H3. clear H H5. rename ts into ts0.
      remember (clear_AList_tags ts0) as ts. clear Heqts. clear ts0.
      remember (length ts) as n. pose proof (Forall2_length _ _ _ H0).
      pose proof (Forall2_length _ _ _ H7). rewrite <- Heqn in H, H4. symmetry in Heqn.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in *. subst. simpl. reflexivity.
      + destruct vs0 as [|[f2 v2] vs2]; [simpl in H4; discriminate|].
        destruct vs as [|[f1 v1] vs1]; [simpl in H3; discriminate|].
        destruct ts as [|t ts]; [simpl in Heqn; discriminate|]. simpl in *.
        make_it_clear. specialize (H11 H1 _ H7 H3). rewrite !app_length, H11. f_equal. eapply IHn; eauto.
    - simpl in H1, H3. destruct b, b0; try discriminate.
      clear H H5. rename ts into ts0.
      remember (clear_AList_tags ts0) as ts. clear Heqts. clear ts0.
      remember (length ts) as n. pose proof (Forall2_length _ _ _ H0).
      pose proof (Forall2_length _ _ _ H7). rewrite <- Heqn in H, H4. symmetry in Heqn.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in H, H4. subst. simpl. reflexivity.
      + destruct vs0 as [|[f2 v2] vs2]; [simpl in H4; discriminate|].
        destruct vs as [|[f1 v1] vs1]; [simpl in H3; discriminate|].
        destruct ts as [|t ts]; [simpl in Heqn; discriminate|]. simpl in *.
        make_it_clear. specialize (H11 H1 _ H7 H3). rewrite !app_length, H11. f_equal. eapply IHn; eauto.
  Qed.

  Lemma encode_same_type_same_val: forall (typ: P4Type) (val1 val2: Val),
      ext_val_typ val1 typ -> ext_val_typ val2 typ -> is_packet_typ typ = true ->
      encode val1 = encode val2 -> val1 = val2.
  Proof.
    intros. destruct H, H0. revert dependent val2. revert H3 H1.
    induction H using custom_val_typ_ind; intros; simpl in H1; try discriminate.
    - inv H0. simpl in H2. inv H2. reflexivity.
    - inv H0. simpl in H2. subst. reflexivity.
    - inv H0. simpl in H2. subst. reflexivity.
    - inv H2. f_equal. simpl in H3, H4, H5. remember (length ts) as n.
      pose proof (Forall2_length _ _ _ H). pose proof (Forall2_length _ _ _ H8).
      symmetry in Heqn. rewrite Heqn in H2, H6.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in *. subst. reflexivity.
      + destruct vs0 as [|v2 vs2]; [simpl in *; discriminate|].
        destruct vs as [|v1 vs1]; [simpl in *; discriminate|].
        destruct ts as [|t ts]; [simpl in *; discriminate|]. simpl in *. make_it_clear.
        assert (length (encode v1) = length (encode v2)) by (eapply encode_same_type_same_length; split; eauto).
        eapply app_eq_len_eq in H; eauto. destruct H. specialize (H8 H3 H1 _ H2 H4 H). rewrite H8.
        f_equal. eapply IHn; eauto.
    - inv H4. f_equal. simpl in *. make_it_clear. clear H H2 H8. rewrite clear_AList_tags_forallb_snd in H4.
      rename ts into ts0. remember (clear_AList_tags ts0) as ts. clear ts0 Heqts. remember (length ts) as n.
      pose proof (Forall2_length _ _ _ H0). pose proof (Forall2_length _ _ _ H10).
      symmetry in Heqn. rewrite Heqn in H, H2.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in *. subst. reflexivity.
      + destruct vs0 as [|[f2 v2] vs2]; [simpl in *; discriminate|].
        destruct vs as [|[f1 v1] vs1]; [simpl in *; discriminate|].
        destruct ts as [|t ts]; [simpl in *; discriminate|]. simpl in *. make_it_clear.
        assert (length (encode v1) = length (encode v2)) by (eapply encode_same_type_same_length; split; eauto).
        eapply app_eq_len_eq in H18; eauto. destruct H18. unfold Basics.compose in H4. specialize (H14 H3 H4 _ H10 H5 H18).
        rewrite H14, H0, H. f_equal. eapply IHn; eauto.
    - simpl in H3. destruct b; try discriminate. inv H4. simpl in H5. destruct b; try discriminate.
      f_equal. simpl in *. make_it_clear. clear H H2 H8. rewrite clear_AList_tags_forallb_snd in H4.
      rename ts into ts0. remember (clear_AList_tags ts0) as ts. clear ts0 Heqts. remember (length ts) as n.
      pose proof (Forall2_length _ _ _ H0). pose proof (Forall2_length _ _ _ H10).
      symmetry in Heqn. rewrite Heqn in H, H2.
      revert dependent ts. revert dependent vs. revert dependent vs0. induction n; intros.
      + rewrite length_zero_iff_nil in *. subst. reflexivity.
      + destruct vs0 as [|[f2 v2] vs2]; [simpl in *; discriminate|].
        destruct vs as [|[f1 v1] vs1]; [simpl in *; discriminate|].
        destruct ts as [|t ts]; [simpl in *; discriminate|]. simpl in *. make_it_clear.
        assert (length (encode v1) = length (encode v2)) by (eapply encode_same_type_same_length; split; eauto).
        eapply app_eq_len_eq in H18; eauto. destruct H18. unfold Basics.compose in H4. specialize (H14 H3 H4 _ H10 H5 H18).
        rewrite H14, H0, H. f_equal. eapply IHn; eauto.
  Qed.

  Lemma encode_same_type_same_val_app: forall (typ: P4Type) (val1 val2: Val) l1 l2,
      ext_val_typ val1 typ -> ext_val_typ val2 typ -> is_packet_typ typ = true ->
      encode val1 ++ l1 = encode val2 ++ l2 -> val1 = val2 /\ l1 = l2.
  Proof.
    intros. assert (length (encode val1) = length (encode val2)) by
      (eapply encode_same_type_same_length; eauto).
    eapply app_eq_len_eq in H3; eauto. destruct H3. split; auto.
    eapply encode_same_type_same_val in H3; eauto.
  Qed.

End PacketFormat.

Inductive format :=
| null: format
| accurate: packet -> format
| unspecified: nat -> format
| guarded: bool -> format -> format -> format.

Fixpoint format_length (f: format) : nat :=
  match f with
  | null => O
  | accurate p => length p
  | unspecified n => n
  | guarded b f1 f2 => match b with
                      | true => format_length f1
                      | false => format_length f2
                      end
  end.

Inductive match_one: format -> packet -> Prop :=
| match_null: match_one null []
| match_accurate: forall p, match_one (accurate p) p
| match_unspecified: forall p n, length p = n -> match_one (unspecified n) p
| match_guarded_true: forall p f1 f2,
    match_one f1 p -> match_one (guarded true f1 f2) p
| match_guarded_false: forall p f1 f2,
    match_one f2 p -> match_one (guarded false f1 f2) p.

Lemma match_one_accurate: forall a p, match_one (accurate a) p -> a = p.
Proof. intros. inversion H. reflexivity. Qed.

Lemma match_one_accurate_iff: forall a p, match_one (accurate a) p <-> a = p.
Proof.
  intros. split; intros.
  - apply match_one_accurate in H; assumption.
  - subst. constructor.
Qed.

Lemma match_one_guarded_true: forall p f1 f2,
    match_one (guarded true f1 f2) p -> match_one f1 p.
Proof. intros. inversion H. assumption. Qed.

Lemma match_one_guarded_true_iff: forall p f1 f2,
    match_one (guarded true f1 f2) p <-> match_one f1 p.
Proof.
  intros; split; intros.
  - apply match_one_guarded_true in H. assumption.
  - constructor. assumption.
Qed.

Lemma match_one_guarded_false: forall p f1 f2,
    match_one (guarded false f1 f2) p -> match_one f2 p.
Proof. intros. inversion H. assumption. Qed.

Lemma match_one_guarded_false_iff: forall p f1 f2,
    match_one (guarded false f1 f2) p <-> match_one f2 p.
Proof.
  intros; split; intros.
  - apply match_one_guarded_false in H. assumption.
  - constructor. assumption.
Qed.

Lemma match_one_size_eq: forall f p1 p2,
    match_one f p1 -> match_one f p2 -> length p1 = length p2.
Proof. induction f; intros; inv H; inv H0; auto. Qed.

Lemma match_one_size: forall f p,
    match_one f p -> length p = format_length f.
Proof. intros. induction H; simpl; auto. Qed.

Definition format_match (f: list format) (p: packet): Prop :=
  exists l, concat l = p /\ Forall2 match_one f l.

Lemma format_match_size_unspec_le: forall p n f,
    format_match (unspecified n :: f) p -> ((Z.of_nat n) <= Zlength p)%Z.
Proof.
  intros. destruct H as [l [? ?]]. destruct l; inv H0. inv H4.
  simpl. rewrite Zlength_app, <- Zlength_correct.
  pose proof (Zlength_nonneg (concat l0)). lia.
Qed.

Lemma format_match_size': forall f p len,
    format_match f p -> length p + len = fold_left Nat.add (map format_length f) len.
Proof.
  intros. hnf in H. destruct H as [l [? ?]]. revert len p H. induction H0.
  - intros. simpl in *. subst p. reflexivity.
  - simpl. intros.
    specialize (IHForall2 (len + format_length x) (concat l') ltac:(reflexivity)).
    rewrite <- IHForall2. subst p. rewrite app_length. apply match_one_size in H.
    rewrite H. lia.
Qed.

Lemma format_match_size: forall f p,
    format_match f p -> length p = fold_left Nat.add (map format_length f) O.
Proof. intros. rewrite <- (format_match_size' f p O); auto. Qed.

Lemma format_match_skipn: forall p n p',
    format_match [unspecified n ; accurate p'] p -> skipn n p = p'.
Proof.
  intros. destruct H as [l [? ?]]. inv H0. inv H5. inv H4. inv H3. inv H1.
  simpl. rewrite app_nil_r, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma format_match_cons_iff: forall f l p,
    format_match (f :: l) p <->
      exists p1 p2,  p = p1 ++ p2 /\ match_one f p1 /\ format_match l p2.
Proof.
  intros. split; intros.
  - inv H. destruct H0. inv H0. simpl. exists y, (concat l').
    split; [|split]; auto. exists l'. split; auto.
  - destruct H as [p1 [p2 [? [? [pl []]]]]].
    exists (p1 :: pl). split; simpl; [rewrite H1 | constructor]; auto.
Qed.

Lemma format_match_nil: forall p, format_match [] p -> p = [].
Proof. intros. destruct H as [l []]. inv H0. reflexivity. Qed.

Lemma format_match_guarded_true: forall f1 f2 l p,
    format_match (guarded true f1 f2 :: l) p -> format_match (f1 :: l) p.
Proof.
  intros. rewrite format_match_cons_iff in H. destruct H as [p1 [p2 [? [? ?]]]].
  apply match_one_guarded_true in H0. rewrite format_match_cons_iff.
  exists p1, p2. split; auto.
Qed.

Lemma format_match_guarded_true_iff: forall f1 f2 l p,
    format_match (guarded true f1 f2 :: l) p <-> format_match (f1 :: l) p.
Proof.
  intros. split; intros.
  - apply format_match_guarded_true in H; assumption.
  - rewrite format_match_cons_iff in *. destruct H as [p1 [p2 [? [? ?]]]].
    exists p1, p2. split; auto. split; auto. rewrite match_one_guarded_true_iff. assumption.
Qed.

Lemma format_match_guarded_false: forall f1 f2 l p,
    format_match (guarded false f1 f2 :: l) p -> format_match (f2 :: l) p.
Proof.
  intros. rewrite format_match_cons_iff in H. destruct H as [p1 [p2 [? [? ?]]]].
  apply match_one_guarded_false in H0. rewrite format_match_cons_iff.
  exists p1, p2. split; auto.
Qed.

Lemma format_match_guarded_false_iff: forall f1 f2 l p,
    format_match (guarded false f1 f2 :: l) p <-> format_match (f2 :: l) p.
Proof.
  intros. split; intros.
  - apply format_match_guarded_false in H; assumption.
  - rewrite format_match_cons_iff in *. destruct H as [p1 [p2 [? [? ?]]]].
    exists p1, p2. split; auto. split; auto. rewrite match_one_guarded_false_iff. assumption.
Qed.

Lemma format_match_null: forall l p,
    format_match (null :: l) p -> format_match l p.
Proof.
  intros. rewrite format_match_cons_iff in H. destruct H as [p1 [p2 [? [? ?]]]].
  inversion H0. subst p1. simpl in H. subst p2. assumption.
Qed.

Lemma format_match_null_iff: forall l p,
    format_match (null :: l) p <-> format_match l p.
Proof.
  intros; split; intros.
  - apply format_match_null in H; assumption.
  - rewrite format_match_cons_iff. exists [], p. simpl; split; auto. split; auto. constructor.
Qed.

Ltac simpl_format_list :=
  match goal with
  | H: format_match (accurate _ :: _) ?p |- _ =>
      rewrite format_match_cons_iff in H;
      let p1 := fresh "p1" in
      let p2 := fresh "p2" in
      destruct H as [p1 [p2 [? [? ?]]]]; subst p;
      match goal with
      | HS: match_one (accurate _) ?ps |- _ =>
          apply match_one_accurate in HS; subst ps
      end
  | H: format_match (guarded true _ _ :: _) _ |- _ =>
      apply format_match_guarded_true in H
  | H: format_match (guarded false _ _ :: _) _ |- _ =>
      apply format_match_guarded_false in H
  | H: format_match (null :: _) _ |- _ =>
      apply format_match_null in H
  | H: format_match nil ?p |- _ =>
      apply format_match_nil in H; subst p
  end.

Lemma format_match_app_iff: forall l1 l2 p,
    format_match (l1 ++ l2) p <->
      exists p1 p2,  p = p1 ++ p2 /\ format_match l1 p1 /\ format_match l2 p2.
Proof.
  induction l1; intros; simpl.
  - split; intros.
    + exists nil, p. simpl. split; [|split]; auto. exists nil. simpl. split; auto.
    + destruct H as [p1 [p2 [? [? ?]]]]. destruct H0 as [l1 [? ?]].
      inv H2. simpl. assumption.
  - rewrite format_match_cons_iff.
    split; intros; destruct H as [p1 [p2 [? [? ?]]]]; subst.
    + rewrite IHl1 in H1. destruct H1 as [p3 [p4 [? [? ?]]]]. subst p2.
      exists (p1 ++ p3), p4. split; [|split]; auto. 1: rewrite app_assoc; reflexivity.
      rewrite format_match_cons_iff. exists p1, p3. split; auto.
    + rewrite format_match_cons_iff in H0. destruct H0 as [p3 [p4 [? [? ?]]]].
      subst. rewrite <- app_assoc. exists p3, (p4 ++ p2). split; [|split]; auto.
      rewrite IHl1. exists p4, p2. split; auto.
Qed.

Notation "'ε'" := (null).
Notation "⦑ p ⦒" := (accurate p).
Notation "⟨ n ⟩" := (unspecified n).
Notation "⦃ b ? f1 | f2 ⦄" := (guarded b f1 f2).
Notation "p ⫢ f" := (format_match f p) (at level 80, no associativity).
Notation "'⊫ᵥ' v '\:' t" := (ext_val_typ v t) (at level 80, no associativity).

Lemma format_match_singleton: forall p, p ⫢ [⦑ p ⦒].
Proof.
  intros. exists [p]. split.
  - simpl. rewrite app_nil_r. reflexivity.
  - repeat constructor.
Qed.

Lemma format_match_cons: forall p1 p2 f l,
    match_one f p1 -> p2 ⫢ l -> p1 ++ p2 ⫢ f :: l.
Proof. intros. rewrite format_match_cons_iff. exists p1, p2. split; auto. Qed.

Lemma nil_format_match: [] ⫢ [].
Proof. exists []. simpl. split; [reflexivity | constructor]. Qed.

Lemma format_match_app_iff_front: forall l1 l2 p,
    p ⫢ l1 ++ l2 <-> exists p1 p2 : packet, p = p1 ++ p2 /\ (p1 ⫢ l1) /\ p ⫢ [⦑ p1 ⦒] ++ l2.
Proof.
  intros. split; intros.
  - rewrite format_match_app_iff in H. destruct H as [p1 [p2 [? [? ?]]]]; subst.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. apply format_match_singleton.
  - destruct H as [p1 [p2 [? [? ?]]]]; subst. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff in H1.
    destruct H1 as [p3 [p4 [? [? ?]]]]. inv H1. destruct H3. inv H3. inv H8.
    inv H6. simpl in H. rewrite app_nil_r in H. apply app_inv_head in H.
    subst. assumption.
Qed.

Lemma format_match_app_iff_rear: forall l1 l2 p,
    p ⫢ l1 ++ l2 <-> exists p1 p2 : packet, p = p1 ++ p2 /\ (p ⫢ l1 ++ [⦑ p2 ⦒]) /\ p2 ⫢ l2.
Proof.
  intros. split; intros.
  - rewrite format_match_app_iff in H. destruct H as [p1 [p2 [? [? ?]]]]; subst.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. apply format_match_singleton.
  - destruct H as [p1 [p2 [? [? ?]]]]; subst. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff in H0.
    destruct H0 as [p3 [p4 [? [? ?]]]]. inv H2. destruct H3. inv H3. inv H8.
    inv H6. simpl in H. rewrite app_nil_r in H. apply app_inv_tail in H.
    subst. assumption.
Qed.

#[export] Hint Resolve nil_format_match: core.

Ltac format_match_solve :=
  repeat lazymatch goal with
    | |- ?A ++ _ ⫢ accurate ?A :: _ => apply format_match_cons; [apply match_accurate |]
    | |- _ ⫢ guarded false _ _ :: _ => rewrite format_match_guarded_false_iff
    | |- _ ⫢ guarded true _ _ :: _ => rewrite format_match_guarded_true_iff
    | |- _ ⫢ null :: _ => rewrite format_match_null_iff
    | |- [] ⫢ [] => apply nil_format_match
    | |- ?A ⫢ [⦑ ?A ⦒] => apply format_match_singleton
    end.

Fixpoint format_equiv (f1: format) := fix format_equiv' (f2: format) : Prop :=
    match f1 with
    | null => match f2 with
             | guarded true g _
             | guarded false _ g => format_equiv' g
             | null => True
             | _ => False
             end
    | accurate p1 => match f2 with
                    | guarded true g _
                    | guarded false _ g => format_equiv' g
                    | accurate p2 => p1 = p2
                    | _ => False
                    end
    | unspecified n1 => match f2 with
                       | guarded true g _
                       | guarded false _ g => format_equiv' g
                       | unspecified n2 => n1 = n2
                       | _ => False
                       end
    | guarded true g1 _
    | guarded false _ g1 => match f2 with
                          | guarded true g2 _ => format_equiv g1 g2
                          | guarded fasle _ g2 => format_equiv g1 g2
                          | _ => format_equiv g1 f2
                          end
    end.

Inductive format_list_equiv: list format -> list format -> Prop :=
| list_equiv_nil : format_list_equiv [] []
| list_equiv_epsilon_left: forall l1 l2 f, format_equiv f ε -> format_list_equiv l1 l2 -> format_list_equiv (f :: l1) l2
| list_equiv_epsilon_right: forall l1 l2 f, format_equiv f ε -> format_list_equiv l1 l2 -> format_list_equiv l1 (f :: l2)
| list_equiv_epsilon_cons: forall f1 f2 l1 l2,
    format_equiv f1 f2 -> format_list_equiv l1 l2 -> format_list_equiv (f1 :: l1) (f2 :: l2).

Lemma format_equiv_sym: forall f1 f2, format_equiv f1 f2 -> format_equiv f2 f1.
Proof.
  induction f1, f2; intros; simpl in H; try contradiction; simpl; auto.
  - destruct b.
    + induction f2_1; auto. simpl. destruct b; [apply IHf2_1_1 | apply IHf2_1_2]; auto.
    + induction f2_2; auto. simpl. destruct b; [apply IHf2_2_1 | apply IHf2_2_2]; auto.
  - destruct b.
    + induction f2_1; auto. 1: simpl; symmetry; assumption. destruct b; [apply IHf2_1_1 | apply IHf2_1_2]; auto.
    + induction f2_2; auto. 1: simpl; symmetry; assumption. destruct b; [apply IHf2_2_1 | apply IHf2_2_2]; auto.
  - destruct b.
    + induction f2_1; auto. 1: simpl; symmetry; assumption. destruct b; [apply IHf2_1_1 | apply IHf2_1_2]; auto.
    + induction f2_2; auto. 1: simpl; symmetry; assumption. destruct b; [apply IHf2_2_1 | apply IHf2_2_2]; auto.
  - destruct b.
    + specialize (IHf1_1 _ H). apply IHf1_1.
    + specialize (IHf1_2 _ H). apply IHf1_2.
  - destruct b.
    + specialize (IHf1_1 _ H). apply IHf1_1.
    + specialize (IHf1_2 _ H). apply IHf1_2.
  - destruct b.
    + specialize (IHf1_1 _ H). apply IHf1_1.
    + specialize (IHf1_2 _ H). apply IHf1_2.
  - destruct b, b0; [apply IHf1_1 | apply IHf1_1 | apply IHf1_2 | apply IHf1_2]; assumption.
Qed.

Lemma format_equiv_refl: forall f, format_equiv f f.
Proof. induction f; intros; simpl; auto. destruct b; auto. Qed.

Lemma format_equiv_true:
  forall f1 f2: format, format_equiv ⦃ true ? f1 | f2 ⦄ f1.
Proof. induction f1; simpl; intros; auto. destruct b; [apply IHf1_1 | apply IHf1_2]; assumption. Qed.

Lemma format_equiv_false:
  forall f1 f2: format, format_equiv ⦃ false ? f1 | f2 ⦄ f2.
Proof. intros. induction f2; simpl; intros; auto. destruct b; [apply IHf2_1 | apply IHf2_2]; assumption. Qed.

Lemma format_equiv_true_false_iff:
  forall f1 f2 f3 : format, format_equiv ⦃ true ? f1 | f2 ⦄ f3 <-> format_equiv ⦃ false ? f2 | f1 ⦄ f3.
Proof. simpl; split; intros; apply H. Qed.

Lemma format_equiv_true_swap:
  forall f1 f2 f3 : format, format_equiv f1 ⦃ true ? f2 | f3 ⦄ <-> format_equiv ⦃ true ? f1 | f3 ⦄ f2.
Proof.
  intros. split; intros.
  - revert f1 f2 f3 H. induction f1, f2; simpl; intros; auto; try contradiction. destruct b, b0.
    + apply IHf1_1 with (f3 := f2_2). apply H.
    + apply IHf1_1 with (f3 := f2_1). apply format_equiv_sym in H. rewrite <- format_equiv_true_false_iff in H.
      apply format_equiv_sym, H.
    + apply IHf1_2 with (f3 := f2_2). apply H.
    + apply IHf1_2 with (f3 := f2_1). apply format_equiv_sym in H. rewrite <- format_equiv_true_false_iff in H.
      apply format_equiv_sym, H.
  - revert f1 f2 f3 H. induction f1, f2; simpl; intros; auto; try contradiction. destruct b, b0.
    + apply IHf1_1 with (f3 := f2_2). apply H.
    + apply format_equiv_sym. rewrite <- format_equiv_true_false_iff. apply format_equiv_sym. apply IHf1_1 with (f3 := f2_1), H.
    + apply IHf1_2 with (f3 := f2_2), H.
    + apply format_equiv_sym. rewrite <- format_equiv_true_false_iff. apply format_equiv_sym. apply IHf1_2 with (f3 := f2_1), H.
Qed.

Lemma format_equiv_true_elim1:
  forall f1 f2 f3 : format, format_equiv ⦃ true ? f1 | f2 ⦄ f3 -> format_equiv f1 f3.
Proof.
  intros f1 f2 f3. simpl. clear f2. revert f1 f3. induction f1, f3; simpl; intros; auto; try contradiction.
  destruct b, b0; simpl in *.
  - apply IHf1_1, H.
  - apply IHf1_1, H.
  - apply IHf1_2, H.
  - apply IHf1_2, H.
Qed.

Lemma format_equiv_true_elim2:
  forall f1 f2 f3 : format, format_equiv f1 ⦃ true ? f2 | f3 ⦄ -> format_equiv f1 f2.
Proof. intros. rewrite format_equiv_true_swap in H. apply format_equiv_true_elim1 in H. assumption. Qed.

Lemma format_equiv_false_elim1:
  forall f1 f2 f3 : format, format_equiv ⦃ false ? f1 | f2 ⦄ f3 -> format_equiv f2 f3.
Proof. intros. rewrite <- format_equiv_true_false_iff in H. apply format_equiv_true_elim1 in H. assumption. Qed.

Lemma format_equiv_false_elim2:
  forall f1 f2 f3 : format, format_equiv f1 ⦃ false ? f2 | f3 ⦄ -> format_equiv f1 f3.
Proof.
  intros. apply format_equiv_sym in H. rewrite <- format_equiv_true_false_iff in H.
  apply format_equiv_true_elim1, format_equiv_sym in H. assumption.
Qed.

Ltac simpl_format_equiv :=
  repeat lazymatch goal with
  | H: format_equiv ⦃ true ? _ | _ ⦄ _ |- _ => apply format_equiv_true_elim1 in H
  | H: format_equiv _ ⦃ true ? _ | _ ⦄ |- _ => apply format_equiv_true_elim2 in H
  | H: format_equiv ⦃ false ? _ | _ ⦄ _ |- _ => apply format_equiv_false_elim1 in H
  | H: format_equiv _ ⦃ false ? _ | _ ⦄ |- _ => apply format_equiv_false_elim2 in H
  end.

Lemma format_equiv_trans: forall f1 f2 f3, format_equiv f1 f2 -> format_equiv f2 f3 -> format_equiv f1 f3.
Proof.
  induction f1, f2, f3; simpl; intros; try contradiction; simpl; auto.
  1,2,6,8,12,13: destruct b;
      [ induction f2_1; simpl in H0; auto; destruct b; [apply IHf2_1_1 | apply IHf2_1_2]; auto |
        induction f2_2; simpl in H0; auto; destruct b; [apply IHf2_2_1 | apply IHf2_2_2]; auto ].
  - destruct b, b0.
    + assert (format_equiv ε f2_1) by apply H. clear H. cut (format_equiv ε f3_1). 1: intros Hs; apply Hs.
      induction f2_1; [assumption | simpl in H1; contradiction..|]. destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ε f2_1) by apply H. clear H. cut (format_equiv ε f3_2). 1: intros Hs; apply Hs.
      induction f2_1; [assumption | simpl in H1; contradiction..|]. destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ε f2_2) by apply H. clear H. cut (format_equiv ε f3_1). 1: intros Hs; apply Hs.
      induction f2_2; [assumption | simpl in H1; contradiction..|]. destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ε f2_2) by apply H. clear H. cut (format_equiv ε f3_2). 1: intros Hs; apply Hs.
      induction f2_2; [assumption | simpl in H1; contradiction..|]. destruct b; simpl_format_equiv; auto.
  - transitivity l0; auto.
  - subst l0. apply H0.
  - destruct b.
    + assert (format_equiv ⦑ l ⦒ f2_1) by apply H. clear H. induction f2_1.
      * simpl in H0; contradiction.
      * simpl in *; transitivity l1; auto.
      * simpl in H0; contradiction.
      * destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⦑ l ⦒ f2_2) by apply H. clear H. induction f2_2.
      * simpl in H0; contradiction.
      * simpl in *; transitivity l1; auto.
      * simpl in H0; contradiction.
      * destruct b; simpl_format_equiv; auto.
  - destruct b, b0.
    + assert (format_equiv ⦑ l ⦒ f2_1) by apply H. clear H. cut (format_equiv ⦑ l ⦒ f3_1). 1: intros Hs; apply Hs.
      induction f2_1; [simpl in H1; contradiction | simpl in H1; subst; assumption | simpl in H1; contradiction |].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⦑ l ⦒ f2_1) by apply H. clear H. cut (format_equiv ⦑ l ⦒ f3_2). 1: intros Hs; apply Hs.
      induction f2_1; [simpl in H1; contradiction | simpl in H1; subst; assumption | simpl in H1; contradiction |].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⦑ l ⦒ f2_2) by apply H. clear H. cut (format_equiv ⦑ l ⦒ f3_1). 1: intros Hs; apply Hs.
      induction f2_2; [simpl in H1; contradiction | simpl in H1; subst; assumption | simpl in H1; contradiction |].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⦑ l ⦒ f2_2) by apply H. clear H. cut (format_equiv ⦑ l ⦒ f3_2). 1: intros Hs; apply Hs.
      induction f2_2; [simpl in H1; contradiction | simpl in H1; subst; assumption | simpl in H1; contradiction |].
      destruct b; simpl_format_equiv; auto.
  - transitivity n0; auto.
  - subst n0. apply H0.
  - destruct b.
    + assert (format_equiv ⟨ n ⟩ f2_1) by apply H. clear H. induction f2_1.
      * simpl in H0; contradiction.
      * simpl in H0; contradiction.
      * simpl in *; transitivity n1; auto.
      * destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⟨ n ⟩ f2_2) by apply H. clear H. induction f2_2.
      * simpl in H0; contradiction.
      * simpl in H0; contradiction.
      * simpl in *; transitivity n1; auto.
      * destruct b; simpl_format_equiv; auto.
  - destruct b, b0.
    + assert (format_equiv ⟨ n ⟩ f2_1) by apply H. clear H. cut (format_equiv ⟨ n ⟩ f3_1). 1: intros Hs; apply Hs.
      induction f2_1; [simpl in H1; contradiction.. | simpl in H1; subst; assumption | ].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⟨ n ⟩ f2_1) by apply H. clear H. cut (format_equiv ⟨ n ⟩ f3_2). 1: intros Hs; apply Hs.
      induction f2_1; [simpl in H1; contradiction.. | simpl in H1; subst; assumption | ].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⟨ n ⟩ f2_2) by apply H. clear H. cut (format_equiv ⟨ n ⟩ f3_1). 1: intros Hs; apply Hs.
      induction f2_2; [simpl in H1; contradiction.. | simpl in H1; subst; assumption | ].
      destruct b; simpl_format_equiv; auto.
    + assert (format_equiv ⟨ n ⟩ f2_2) by apply H. clear H. cut (format_equiv ⟨ n ⟩ f3_2). 1: intros Hs; apply Hs.
      induction f2_2; [simpl in H1; contradiction.. | simpl in H1; subst; assumption | ].
      destruct b; simpl_format_equiv; auto.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - subst l0. apply H.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - subst n0. apply H.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - destruct b, b0.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
  - destruct b, b0, b1.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_1; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
    + eapply IHf1_2; eauto.
Qed.

Lemma format_equiv_branch:
      forall (b : bool) (f1_1 f1_2 : format) (b0 : bool) (f2_1 f2_2 : format),
        (if b0 then format_equiv ⦃ b ? f1_1 | f1_2 ⦄ f2_1 else format_equiv ⦃ b ? f1_1 | f1_2 ⦄ f2_2) ->
        format_equiv ⦃ b ? f1_1 | f1_2 ⦄ ⦃ b0 ? f2_1 | f2_2 ⦄.
Proof. intros b f1_1 f1_2 b0 f2_1 f2_2 H. destruct b, b0; simpl; simpl_format_equiv; auto. Qed.

Lemma format_equiv_match: forall p f1 f2, format_equiv f1 f2 -> match_one f1 p -> match_one f2 p.
Proof.
  intros. revert dependent f2. induction H0, f2; simpl; intros; try contradiction; try (subst; constructor; auto).
  - destruct b; constructor.
    + induction f2_1; try contradiction; try constructor.
      destruct b; constructor; [apply IHf2_1_1, H | apply IHf2_1_2, H].
    + induction f2_2; try contradiction; try constructor.
      destruct b; constructor; [apply IHf2_2_1, H | apply IHf2_2_2, H].
  - destruct b; constructor.
    + induction f2_1; try contradiction. subst; constructor.
      destruct b; constructor; [apply IHf2_1_1, H | apply IHf2_1_2, H].
    + induction f2_2; try contradiction. subst; constructor.
      destruct b; constructor; [apply IHf2_2_1, H | apply IHf2_2_2, H].
  - destruct b; constructor.
    + induction f2_1; try contradiction. subst; constructor; auto.
      destruct b; constructor; [apply IHf2_1_1, H0 | apply IHf2_1_2, H0].
    + induction f2_2; try contradiction. subst; constructor; auto.
      destruct b; constructor; [apply IHf2_2_1, H0 | apply IHf2_2_2, H0].
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
    clear dependent p. destruct b, b0; simpl; simpl_format_equiv; assumption.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
    clear dependent p. destruct b, b0; simpl; simpl_format_equiv; assumption.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
    clear dependent p. destruct b, b0; simpl; simpl_format_equiv; assumption.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
    clear dependent p. destruct b1, b0; simpl; simpl_format_equiv; assumption.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
  - induction f1; apply IHmatch_one; clear IHmatch_one; induction f2; auto.
  - destruct b.
    + apply IHmatch_one. assert (format_equiv ⦃ true ? ⦃ true ? f2_1 | f2_2 ⦄ | f2 ⦄ f2) by apply H.
      apply format_equiv_true_elim1 in H1. assumption.
    + apply IHmatch_one. assert (format_equiv ⦃ false ? f2 | ⦃ false ? f2_1 | f2_2 ⦄ ⦄ f2) by apply H.
      apply format_equiv_false_elim1 in H1. assumption.
Qed.

Lemma format_list_equiv_match: forall p l1 l2, format_list_equiv l1 l2 -> format_match l1 p -> format_match l2 p.
Proof.
  intros. revert p H0. induction H; intros; auto.
  - apply IHformat_list_equiv. destruct H1 as [l [? ?]]. destruct l; inversion H2. subst; clear H2.
    pose proof (format_equiv_match _ _ _ H H6). inversion H1. subst l. simpl. exists l0. split; auto.
  - apply IHformat_list_equiv in H1. destruct H1 as [l [? ?]]. exists ([] :: l). split. 1: simpl; assumption.
    constructor; auto. assert (match_one ε []) by constructor. eapply format_equiv_match; eauto.
    apply format_equiv_sym; assumption.
  - assert (exists h r, p = h ++ r /\ match_one f1 h /\ r ⫢ l1). {
      destruct H1 as [l [? ?]]. destruct l; inversion H2. subst; clear H2.
      exists l, (concat l0). simpl. do 2 (split; auto). exists l0. split; auto. }
    destruct H2 as [h [r [? [? ?]]]]. apply IHformat_list_equiv in H4. subst p.
    pose proof (format_equiv_match _ _ _ H H3). destruct H4 as [l [? ?]].
    exists (h :: l). simpl. rewrite H4. split; auto.
Qed.
