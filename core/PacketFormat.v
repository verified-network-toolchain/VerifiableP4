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

  Fixpoint header_is_valid (val: Val) : bool :=
    match val with
    | ValBaseHeader _ false => false
    | ValBaseStruct fields
    | ValBaseHeader fields true => forallb (header_is_valid ∘ snd) fields
    | ValBaseTuple l => forallb header_is_valid l
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
      | H: forallb header_is_valid (_ :: _) = true |- _ => simpl in H
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
    ⊢ᵥ val \: typ /\ header_is_valid val = true.

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

End PacketFormat.

Inductive format :=
| null: format
| accurate: packet -> format
| unspecified: nat -> format
| guarded: bool -> format -> format -> format.

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

Lemma match_one_guarded_true: forall p f1 f2,
    match_one (guarded true f1 f2) p -> match_one f1 p.
Proof. intros. inversion H. assumption. Qed.

Lemma match_one_guarded_false: forall p f1 f2,
    match_one (guarded false f1 f2) p -> match_one f2 p.
Proof. intros. inversion H. assumption. Qed.


Lemma match_one_size_eq: forall f p1 p2,
    match_one f p1 -> match_one f p2 -> length p1 = length p2.
Proof. induction f; intros; inv H; inv H0; auto. Qed.

Definition format_match (f: list format) (p: packet): Prop :=
  exists l, concat l = p /\ Forall2 match_one f l.

Lemma format_match_size: forall p n f,
    format_match (unspecified n :: f) p -> ((Z.of_nat n) <= Zlength p)%Z.
Proof.
  intros. destruct H as [l [? ?]]. destruct l; inv H0. inv H4.
  simpl. rewrite Zlength_app, <- Zlength_correct.
  pose proof (Zlength_nonneg (concat l0)). lia.
Qed.

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

Lemma format_match_guarded_false: forall f1 f2 l p,
    format_match (guarded false f1 f2 :: l) p -> format_match (f2 :: l) p.
Proof.
  intros. rewrite format_match_cons_iff in H. destruct H as [p1 [p2 [? [? ?]]]].
  apply match_one_guarded_false in H0. rewrite format_match_cons_iff.
  exists p1, p2. split; auto.
Qed.

Lemma format_match_null: forall l p,
    format_match (null :: l) p -> format_match l p.
Proof.
  intros. rewrite format_match_cons_iff in H. destruct H as [p1 [p2 [? [? ?]]]].
  inversion H0. subst p1. simpl in H. subst p2. assumption.
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

Lemma format_match_app_iff': forall l1 l2 p,
    format_match (l1 ++ l2) p <->
      exists p1 p2,  p = p1 ++ p2 /\
                  format_match (l1 ++ [accurate p2]) p /\
                  format_match l2 p2.
Proof.
  intros. split; intros.
  - rewrite format_match_app_iff in H. destruct H as [p1 [p2 [? [? ?]]]]; subst.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. exists [p2]. simpl. rewrite app_nil_r. split; auto.
    repeat constructor.
  - destruct H as [p1 [p2 [? [? ?]]]]; subst. rewrite format_match_app_iff.
    exists p1, p2. split; [|split]; auto. rewrite format_match_app_iff in H0.
    destruct H0 as [p3 [p4 [? [? ?]]]]. inv H2. destruct H3. inv H3. inv H8.
    inv H6. simpl in H. rewrite app_nil_r in H. apply app_inv_tail in H.
    subst. assumption.
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

#[export] Hint Resolve nil_format_match: core.
