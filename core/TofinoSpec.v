Require Import Coq.Strings.String.
Require Import BinNat.
Require Import BinInt.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Poulet4.Utils.P4Arith.
Require Import ProD3.core.Core.
Require Import Hammer.Plugin.Hammer.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Lemma mod_bound_succ: forall w z,
    BitArith.mod_bound (N.succ w) z =
      2 * BitArith.mod_bound w (z / 2) + Z.b2z (Z.odd z).
Proof.
  intros. unfold BitArith.mod_bound, BitArith.upper_bound.
  rewrite Znat.N2Z.inj_succ, Z.pow_succ_r, <- div_2_mod_2_pow, Z.mul_comm by lia.
  reflexivity.
Qed.

Lemma to_lbool_succ: forall w z, to_lbool (N.succ w) z = to_lbool w (z / 2) ++ [Z.odd z].
Proof.
  intros. unfold to_lbool. rewrite Nnat.N2Nat.inj_succ.
  simpl. rewrite P4Arith.to_lbool'_app. reflexivity.
Qed.

Lemma vmm_help_app: forall l1 l1' l2 l2' l3 l3',
    length l1 = length l2 -> length l2 = length l3 ->
    vmm_help (l1 ++ l1') (l2 ++ l2') (l3 ++ l3') =
      andb (vmm_help l1 l2 l3) (vmm_help l1' l2' l3').
Proof.
  induction l1; intros l1' l2 l2' l3 l3' Hl12 Hl23.
  - destruct l2, l3; simpl in *; [reflexivity | discriminate..].
  - destruct l2, l3; simpl in *; try discriminate.
    destruct b0; rewrite IHl1; auto.
    rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma land_mod_bound: forall a b w,
    Z.land a (BitArith.mod_bound w b) =
      Z.land (BitArith.mod_bound w a) (BitArith.mod_bound w b).
Proof.
  intros. unfold BitArith.mod_bound, BitArith.upper_bound.
  rewrite <- !Z.land_ones, !Z.land_assoc, !Z.land_ones by lia.
  rewrite <- (Z.land_ones a), <- Z.land_assoc,
    (Z.land_comm (Z.ones (Z.of_N w))), Z.land_assoc, Z.land_ones by lia.
  rewrite Zdiv.Zmod_mod. reflexivity.
Qed.

Lemma land_double_add_b2z: forall a b c1 c2,
    Z.land (2 * a + Z.b2z c1) (2 * b + Z.b2z c2) =
      2 * Z.land a b + Z.b2z (c1 && c2).
Proof.
  intros. apply Z.bits_inj'. intros. rewrite Z.land_spec.
  rewrite Z.le_lteq in H. destruct H.
  - replace n with (Z.succ (Z.pred n)) by lia.
    rewrite !Z.testbit_succ_r, Z.land_spec by lia. reflexivity.
  - subst. rewrite !Z.testbit_0_r. reflexivity.
Qed.

Lemma values_match_mask_land: forall w key val mask,
    values_match_mask
      (ValBaseBit (to_lbool w key))
      (ValBaseBit (to_lbool w val))
      (ValBaseBit (to_lbool w mask)) =
      (Z.land key (BitArith.mod_bound w mask) =?
       Z.land val (BitArith.mod_bound w mask)).
Proof.
  intros w key val mask. unfold values_match_mask. simpl.
  rewrite !Zlength_to_lbool, N.eqb_refl. simpl.
  revert key val mask.
  induction w using N.peano_ind; intros key val mask.
  - simpl. rewrite bit_mod_bound_0, !Z.land_0_r. reflexivity.
  - rewrite !to_lbool_succ, vmm_help_app by now rewrite !length_to_lbool.
    rewrite (land_mod_bound key), (land_mod_bound val).
    rewrite !mod_bound_succ. rewrite !land_double_add_b2z.
    rewrite <- !land_mod_bound. rewrite IHw.
    remember (BitArith.mod_bound w (mask / 2)) as z. simpl vmm_help.
    destruct (Z.land (key / 2) z =? Z.land (val / 2) z) eqn: Hkv.
    + rewrite Z.eqb_eq in Hkv. rewrite Hkv. simpl andb. destruct (Z.odd mask).
      * rewrite !Bool.andb_true_r.
        destruct (Z.odd key), (Z.odd val); simpl Z.b2z; simpl Bool.eqb;
          (try now rewrite Z.eqb_refl); symmetry; rewrite Z.eqb_neq; lia.
      * rewrite !Bool.andb_false_r, Z.eqb_refl. reflexivity.
    + rewrite Bool.andb_false_l. symmetry. rewrite Z.eqb_neq in *.
      destruct (Z.odd key && Z.odd mask), (Z.odd val && Z.odd mask);
        simpl Z.b2z; lia.
Qed.

Section TofinoSpec.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := ValueLvalue.

Notation ident := (String.string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation Expression := (@Expression tags_t).
Notation table_entry_valset := (@table_entry_valset Expression).

Instance target : @Target tags_t Expression := Tofino.

Variable ge : genv.
Variable am_ge : genv.

Lemma hoare_extern_match_list_intro : forall keys_match_kinds entryvs,
  hoare_extern_match_list keys_match_kinds entryvs (extern_matches keys_match_kinds entryvs).
Proof.
  intros. unfold hoare_extern_match_list.
  simpl. unfold extern_match.
  remember (extern_matches keys_match_kinds entryvs) as cases.
  clear Heqcases.
  induction cases.
  - auto.
  - destruct a.
    destruct b; auto.
Qed.

Fixpoint assert_int_nondet (sv : Sval) : option (N * option Z * list (option bool)) :=
  match sv with
  | ValBaseBit sbits =>
      match lift_option sbits with
      | Some bits =>
          Some (map_snd Some (BitArith.from_lbool bits), sbits)
      | None =>
          Some (Z.to_N (Zlength sbits), None, sbits)
      end
  | ValBaseInt sbits =>
      match lift_option sbits with
      | Some bits =>
          Some (map_snd Some (BitArith.from_lbool bits), sbits)
      | None =>
          Some (Z.to_N (Zlength sbits), None, sbits)
      end
  | ValBaseSenumField _ val => assert_int_nondet val
  | _ => None
  end.

Definition values_match_singleton_nondet (key: Sval) (val: Val): option bool :=
  match eval_sval_to_val key with
  | Some v =>
      Some (values_match_singleton v val)
  | None => None
  end.

(* Fixpoint vmm_help (bits0 bits1 bits2: list bool): bool :=
  match bits2, bits1, bits0 with
  | [], [], [] => true
  | false::tl2, _::tl1, _::tl0 => vmm_help tl0 tl1 tl2
  | true::tl2, hd1::tl1, hd0::tl0 =>
      if (Bool.eqb hd0 hd1)
      then (vmm_help tl0 tl1 tl2)
      else false
  (* should never hit *)
  | _, _, _ => dummy_bool
  end.

Definition values_match_mask (key: Val) (val mask: Val): bool :=
  match assert_int key, assert_int val, assert_int mask with
  | Some (w0, _, bits0), Some (w1, _, bits1), Some (w2, _, bits2) =>
    if negb ((w0 =? w1)%N && (w1 =? w2)%N) then dummy_bool
    else vmm_help bits0 bits1 bits2
  | _, _, _ => dummy_bool
  end.

Fixpoint vmm_help_z (v : Z) (bits1 bits2: list bool) :=
  match bits2, bits1 with
  | [], [] => true
  | false::tl2, _::tl1 => vmm_help_z (v / 2) tl1 tl2
  | true::tl2, hd1::tl1 =>
      if Bool.eqb (Z.odd v) hd1
      then (vmm_help_z (v / 2) tl1 tl2)
      else false
  | _, _ => dummy_bool
  end.

(* Fixpoint vmm_help_z' (v : Z) (bits1 bits2: list bool) :=
  match bits2, bits1 with
  | [], [] => true
  | false::tl2, _::tl1 => vmm_help_z' (v / 2) tl1 tl2
  | true::tl2, hd1::tl1 =>
      andb (Bool.eqb (Z.odd v) hd1) (vmm_help_z' (v / 2) tl1 tl2)
  | _, _ => Tofino.dummy_bool
  end. *)


Definition lpm_nbits_to_mask (w1 w2 : N) : list bool :=
(Zrepeat false (Z.of_N (w1 - w2))) ++ (Zrepeat true (Z.of_N w2)).

Definition values_match_lpm (key: Val) (val: Val) (lpm_num_bits: N): bool :=
  match assert_int key, assert_int val with
  | Some (w0, _, bits0), Some (w1, _, bits1) =>
    if negb ((w0 =? w1)%N && (lpm_num_bits <=? w1)%N) then dummy_bool
    else let bits2 := lpm_nbits_to_mask w1 lpm_num_bits in
     vmm_help bits0 bits1 bits2
  | _, _ => dummy_bool
  end. *)

Definition values_match_range_nondet (key: Sval) (lo hi: Val): option bool :=
  match assert_int_nondet key, assert_int lo, assert_int hi with
  | Some (w0, Some z0, _), Some (w1, z1, _), Some (w2, z2, _) =>
      if negb ((w0 =? w1)%N && (w1 =? w2)%N) then Some dummy_bool
      else Some ((z1 <=? z0) && (z0 <=? z2))
  | _, _, _ => None
  end.

Definition values_match_set_nondet (keys : list Sval) (valset : ValSetT) : option bool :=
  let values_match_set'' (key_valset: Sval * ValSetT) :=
    let (key, valset) := key_valset in
    match valset with
    | VSTSingleton v => values_match_singleton_nondet key v
    | VSTUniversal => Some true
    | VSTMask v1 v2 => None (* values_match_mask key v1 v2 *)
    | VSTRange lo hi => values_match_range_nondet key lo hi
    | VSTLpm w2 v1 => None (* values_match_lpm key v1 w2 *)
    | _ => Some dummy_bool
    end in
  let values_match_set' (keys: list Sval) (valset: ValSetT) :=
    match valset with
    | VSTProd l =>
        if negb (Nat.eqb (List.length l) (List.length keys)) then Some dummy_bool
        else option_map fold_andb (lift_option (List.map values_match_set'' (List.combine keys l)))
    | _ => values_match_set'' (List.hd ValBaseNull keys, valset)
    end in
  match valset with
  | VSTValueSet _ _ sets =>
      option_map fold_orb (lift_option (List.map (values_match_set' keys) sets))
  | _ => values_match_set' keys valset
  end.

Definition extern_matches_nondet (key: list (Sval * ident)) (entries: list table_entry_valset)
    : list (option bool * action_ref) :=
  let ks := List.map fst key in
  let mks := List.map snd key in
  match check_lpm_count mks with
  | None => []
  | Some lpm_idx =>
    let entries' := List.map (fun p => (valset_to_valsett (fst p), snd p)) entries in
    let entries'' :=
      if (Nat.ltb lpm_idx (List.length mks))
      then sort_lpm entries' lpm_idx
      else entries' in
    List.map (fun s => (values_match_set_nondet ks (fst s), snd s)) entries''
  end.

Lemma hoare_extern_match_list_nondet_intro : forall keys match_kinds entryvs,
  hoare_extern_match_list_nondet keys match_kinds entryvs
      (extern_matches_nondet (combine keys match_kinds) entryvs).
Proof.
  (* intros. induction entryvs.
  - red; intros.
    unfold extern_matches_nondet.
    simpl.
  unfold hoare_extern_match_list_nondet.
    simpl.
  unfold hoare_extern_match_list_nondet; intros.

  simpl. unfold extern_match.
  inductionn
  remember (extern_matches keys_match_kinds c) as cases.
  clear Heqcases.
  induction cases.
  - auto.
  - destruct a.
    destruct b; auto. *)
(* Qed. *)
Abort.

Open Scope func_spec.

(** TODO This spec only considers the ideal situation: there is no
error in packet parsing. This is reasonable because the error packets
will be dropped so that they will not affect the ingress after parser,
at least in the Tofino switch. *)
Definition packet_in_extract_spec (p: path) (typ: P4Type): func_spec :=
  WITH,
    PATH p
    MOD None [p]
    WITH (pin: packet_in) v pin' (H: extract typ pin = Some (v, SReturnNull, pin')),
    PRE (ARG []
           (MEM []
              (EXT [ExtPred.singleton p (ObjPin pin)])))
    POST (ARG_RET [eval_val_to_sval v] ValBaseNull
         (MEM []
         (EXT [ExtPred.singleton p (ObjPin pin')]))).

Lemma packet_in_extract_body: forall (p: path) (typ: P4Type),
    func_sound ge (FExternal "packet_in" "extract") [typ]
      (packet_in_extract_spec p typ).
Proof.
  intros. unfold packet_in_extract_spec. simpl. split; repeat intro.
  - inv H0. inv H6. simpl in H0. inv H0.
    + destruct H. destruct H0. destruct H1. simpl in H1. rewrite H1 in H2.
      inv H2. rewrite x2 in H7. inv H7. constructor.
      * hnf. red in H12.
        eapply ForallMap.Forall2_forall_impl_Forall2; [|apply H12].
        constructor. 2: constructor. clear. intros.
        rewrite val_to_sval_iff in H. subst. apply sval_refine_refl.
      * split.
        -- apply eval_val_to_sval_ret_denote. reflexivity.
        -- split; auto. hnf. split; simpl; auto. apply PathMap.get_set_same.
    + red in H. destruct H. red in H. red in H. inv H. inv H3.
  - red. split; simpl; auto. repeat intro. inv H. inv H6. simpl in *.
    assert (q <> p). {
      intro. apply H0. subst. rewrite Bool.orb_false_r. red.
      unfold in_scope. apply is_prefix_refl. }
    inv H; rewrite PathMap.get_set_diff; auto.
Qed.

Definition packet_in_advance_spec (p: path): func_spec :=
  WITH,
    PATH p
    MOD None [p]
    WITH (pin: packet_in) (size: Z) (_: 0 <= size < 2 ^ 32)
         (_: size < Zlength pin),
    PRE (ARG [P4Bit 32 size]
           (MEM []
              (EXT [ExtPred.singleton p (ObjPin pin)])))
    POST (ARG_RET [] ValBaseNull
         (MEM []
         (EXT [ExtPred.singleton p (ObjPin (skipn (Z.to_nat size) pin))]))).

Lemma packet_in_advance_body: forall (p: path),
    func_sound ge (FExternal "packet_in" "advance") [] (packet_in_advance_spec p).
Proof.
  intros. unfold packet_in_advance_spec. simpl. split; repeat intro.
  - inv H0. inv H6. simpl in H0. inv H0. destruct H. hnf in H. red in H3.
    inv H. inv H9. inv H3. clear H10. apply sval_refine_bit_to_loptbool in H7.
    subst y. apply sval_to_val_bit_to_loptbool in H8.
    remember (to_lbool 32 (Z.of_nat len)) as lb1.
    remember (to_lbool 32 x0) as lb2. inversion H8. clear H8.
    rewrite Heqlb1, Heqlb2 in H3. clear dependent lb1. clear dependent lb2.
    apply to_lbool_inj_bit_mod in H3.
    unfold BitArith.mod_bound, BitArith.upper_bound in H3. simpl in H3.
    destruct H0. destruct H0. simpl in H0. rewrite H0 in H1. inv H1.
    rewrite (Zdiv.Zmod_small x0) in H3 by lia.
    rewrite Zdiv.Zmod_small in H3 by lia. subst x0. rewrite Znat.Nat2Z.id.
    unfold advance in H4. unfold Packet.extract_bits in H4. simpl in H4.
    unfold Packet.packet_bind, Packet.packet_ret, ExceptionState.state_bind,
      ExceptionState.state_return, Packet.verify, Packet.pkt_min_size in H4.
    assert (Nat.leb len (Datatypes.length pin) = true). {
      pose proof (Zlength_correct pin). rewrite PeanoNat.Nat.leb_le. lia. }
    rewrite H1 in H4. simpl in H4. inv H4. constructor.
    + hnf in H12 |- * . inversion H12. constructor.
    + split.
      * apply eval_val_to_sval_ret_denote. reflexivity.
      * split; auto. hnf. split; simpl; auto. apply PathMap.get_set_same.
  - red. split; simpl; auto. repeat intro. inv H. inv H6. simpl in *.
    assert (q <> p). {
      intro. apply H0. subst. rewrite Bool.orb_false_r. red.
      unfold in_scope. apply is_prefix_refl. }
    inv H; rewrite PathMap.get_set_diff; auto.
Qed.

Definition parser_accept_spec (p: path): func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH ,
    PRE (ARG [] (MEM [] (EXT [])))
    POST (ARG_RET [] ValBaseNull (MEM [] (EXT []))).

Lemma parser_accept_body: forall p,
    func_sound ge (@accept_state tags_t tags_t_inhabitant) []
      (parser_accept_spec p).
Proof.
  intros. unfold accept_state, BlockNil.
  start_function.
  step.
  entailer.
Qed.

Definition parser_reject_spec (p: path): func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (_: False),
    PRE (ARG [] (MEM [] (EXT [])))
    POST (ARG_RET [] ValBaseNull (MEM [] (EXT []))).

Lemma parser_reject_body: forall p,
    func_sound ge (@reject_state tags_t tags_t_inhabitant) []
      (parser_reject_spec p).
Proof.
  intros. unfold reject_state, BlockNil.
  start_function. exfalso; auto.
  red. split; admit.
Admitted.

(* This is the general form of RegisterAction's apply method's spec that we support.
  We expecct this is general enough for all practical application. We don't support
  other kind of apply methods. *)
(* I don't define f as (Val -> Val) because this function should be partial. *)
Definition RegisterAction_apply_spec {A} (p : path) (repr : A -> Val) (f : A -> A) (retv : A -> Sval) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (old_value : A),
      PRE
        (ARG [eval_val_to_sval (repr old_value)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [eval_val_to_sval (repr (f old_value));
                  retv old_value]
           ValBaseNull
        (MEM []
        (EXT []))).

Definition RegisterAction_apply_spec' {A} (p : path) (valid : A -> Prop) (repr : A -> Val) (f : A -> A) (retv : A -> Sval) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (old_value : A) (H_old_value : valid old_value),
      PRE
        (ARG [eval_val_to_sval (repr old_value)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [eval_val_to_sval (repr (f old_value));
                  retv old_value]
           ValBaseNull
        (MEM []
        (EXT []))).

(* Remove the content type constaint of register, right? *)

Definition RegisterAction_execute_spec : func_spec :=
  WITH A p (* path *) index_w typ s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (index_w, typ, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd repr apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : func_sound am_ge apply_fd nil
          (RegisterAction_apply_spec (A := A) p repr apply_f apply_retv)),
    PATH p
    MOD None [r]
    WITH (c : list Val) (i : Z)
      (H_c : Zlength c = s)
      (H_i : 0 <= i < s)
      old_v
      (H_old_v : Znth i c = repr old_v),
      PRE
        (ARG [P4Bit index_w i]
        (MEM []
        (EXT [ExtPred.singleton r (Tofino.ObjRegister c)])))
      POST
        (ARG_RET [] (apply_retv old_v)
        (MEM []
        (EXT [ExtPred.singleton r
            (Tofino.ObjRegister (upd_Znth i c (repr (apply_f old_v))))]))).

Definition RegisterAction_execute_spec' : func_spec :=
  WITH A p (* path *) index_w typ s (* size *) r (* reg *)
      (H_r : PathMap.get p (ge_ext ge) = Some (Tofino.EnvRegAction r))
      (H_ws : PathMap.get r (ge_ext ge) = Some (Tofino.EnvRegister (index_w, typ, s)))
      (H_s : 0 <= s <= Z.pow 2 (Z.of_N index_w))
      apply_fd apply_valid repr apply_f apply_retv
      (H_apply_fd : PathMap.get (p ++ ["apply"]) (ge_ext ge) =
          Some (Tofino.EnvAbsMet (exec_abstract_method am_ge p apply_fd)))
      (H_apply_body : func_sound am_ge apply_fd nil
          (RegisterAction_apply_spec' (A := A) p apply_valid repr apply_f apply_retv)),
    PATH p
    MOD None [r]
    WITH (c : list Val) (i : Z)
      (H_c : Zlength c = s)
      (H_i : 0 <= i < s)
      old_v
      (H_old_v : Znth i c = repr old_v)
      (H_valid : apply_valid old_v),
      PRE
        (ARG [P4Bit index_w i]
        (MEM []
        (EXT [ExtPred.singleton r (Tofino.ObjRegister c)])))
      POST
        (ARG_RET [] (apply_retv old_v)
        (MEM []
        (EXT [ExtPred.singleton r
            (Tofino.ObjRegister (upd_Znth i c (repr (apply_f old_v))))]))).

Definition execute_fundef : (@fundef tags_t) := FExternal "RegisterAction" "execute".

Lemma to_lbool_lbool_to_val' : forall bs w,
  w = Z.to_N (Zlength bs) ->
  P4Arith.to_lbool w
      (P4Arith.BitArith.lbool_to_val bs 1 0)
  = bs.
Proof.
  intros; subst.
  apply to_lbool_lbool_to_val.
Qed.

Lemma RegisterAction_execute_body' :
  func_sound ge execute_fundef nil RegisterAction_execute_spec'.
Proof.
  intros_fs_bind.
  split.
  2 : {
    unfold func_modifies. intros.
    inv H.
    inv H5. inv H.
    eapply eq_trans in H0; only 2 : (symmetry; apply H_r).
    symmetry in H0; inv H0.
    eapply eq_trans in H3; only 2 : (symmetry; apply H_ws).
    symmetry in H3; inv H3.
    eapply eq_trans in H1; only 2 : (symmetry; apply H_apply_fd).
    symmetry in H1; inv H1.
    destruct (-1 <? index) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    destruct (index <? s) eqn:?.
    2 : {
      simpl in H8. destruct H8; subst.
      apply modifies_refl.
    }
    simpl in H8. destruct H8; subst.
    eapply modifies_trans.
    { eapply modifies_incl.
      { assert (modifies None [] (m, es) (m, s')). {
          inv H7.
          eapply (proj2 H_apply_body) in H1.
          solve_modifies.
        }
        eassumption.
      }
      all : solve_modifies.
    }
    eapply modifies_set_ext with (st := (m, s')).
    simpl.
    replace (in_scope r r) with true. 2 : {
      clear; induction r.
      - auto.
      - simpl. rewrite eqb_refl; auto.
    }
    auto.
  }
  intros_fsh_bind.
  unfold fundef_satisfies_hoare.
  unfold hoare_func; intros.
  inv H0. inv H6.
  inv H0.
  eapply eq_trans in H1; only 2 : (symmetry; apply H_r).
  symmetry in H1; inv H1.
  eapply eq_trans in H4; only 2 : (symmetry; apply H_ws).
  symmetry in H4; inv H4.
  eapply eq_trans in H2; only 2 : (symmetry; apply H_apply_fd).
  symmetry in H2; inv H2.
  destruct H as [? []].
  destruct H1 as [? _].
  simpl in H1.
  rewrite H5 in H1. inv H1.
  assert (index = i). {
    clear -H_i H_s H H3 H6.
    unfold arg_denote, arg_satisfies in H.
    inv H. inv H5.
    inv H3. clear H7.
    assert (ValBaseBit indexb = (ValBaseBit (P4Arith.to_lbool index_w i))). {
      eapply exec_val_eq.
      eapply exec_val_sym with eq.
      { clear; auto. }
      assert (val_to_sval
          (ValBaseBit (P4Arith.to_lbool index_w i))
          (eval_val_to_sval (ValBaseBit (P4Arith.to_lbool index_w i)))). {
        eapply exec_val_sym with strict_read_ndetbit.
        2 : eapply sval_to_val_eval_val_to_sval.
        { clear; sauto. }
        { clear; sauto. }
      }
      eapply exec_val_trans with (f := read_detbit);
        [ | eapply exec_val_trans; [ | eassumption | eassumption] | eassumption ].
      { unfold rel_trans; clear; sauto. }
      { unfold rel_trans; clear; sauto. }
    }
    inv H.
    rewrite P4Arith.bit_from_to_bool in H6.
    inv H6.
    apply Z.mod_small.
    unfold P4Arith.BitArith.upper_bound.
    lia.
  }
  clear H H3 H6.
  subst.
  destruct (-1 <? i) eqn:Heqb; only 2 : lia. clear Heqb.
  destruct (i <? Zlength c) eqn:Heqb; only 2 : lia. clear Heqb.
  simpl in H7. destruct H9. subst.
  clear H0.
  assert (content' = c). {
    clear -H_apply_body H H5 H8.
    inv H8.
    apply (H_apply_body) in H1.
    destruct H1.
    assert (PathMap.get r s' = PathMap.get r es). {
      symmetry.
      apply H3.
      auto.
    }
    rewrite H4 in H.
    change (@extern_object tags_t Expression (@extern_sem tags_t Expression target))
      with (@Tofino.object Expression) in H.
    congruence.
  }
  clear H H5.
  subst.
  rewrite H_old_v in H8.
  assert (new_value = repr (apply_f old_v)
      /\ sval_to_val read_ndetbit (apply_retv old_v) retv). {
    clear -H_apply_body H_valid H8.
    inv H8.
    eapply (proj1 H_apply_body old_v) in H0.
    2 : { auto. }
    2 : {
      split.
      2 : { split; constructor. }
      inv H. inv H6.
      apply val_to_sval_iff in H4.
      subst.
      constructor; only 2 : constructor.
      apply sval_refine_refl.
    }
    clear H.
    destruct H0.
    inv H. inv H6. inv H7.
    inv H1. inv H8. inv H9.
    eapply sval_refine_sval_to_val_n_trans in H6. 2 : eapply H4. clear H4.
    eapply sval_refine_sval_to_val_n_trans in H5. 2 : eapply H3. clear H3.
    split.
    { eapply sval_to_val_n_eval_val_to_sval_eq; eauto. }
    { auto. }
  }
  clear H8.
  destruct H; subst.
  split.
  { inv H12. constructor. }
  clear H12.
  split.
  { unfold ret_denote, ret_satisfies.
    intros.
    eapply exec_val_trans; only 2, 3 : eassumption.
    clear; red; sauto.
  }
  split.
  { constructor. }
  { constructor.
    2 : constructor.
    simpl.
    rewrite PathMap.get_set_same.
    auto.
  }
Qed.

Lemma RegisterAction_execute_body :
  func_sound ge execute_fundef nil RegisterAction_execute_spec.
Proof.
  intros_fs_bind.
  assert (H_apply_body' : func_sound am_ge apply_fd []
      (RegisterAction_apply_spec' p (fun _ => True) repr apply_f apply_retv)). {
    refine_function H_apply_body.
    entailer.
    entailer.
  }
  split.
  2 : {
    unshelve eapply (proj2 (RegisterAction_execute_body' _ _ _ _ _ _ _ _ _ _ (fun _ => True) _ _ _ _ _));
      eauto.
  }
  intros_fsh_bind.
  eapply hoare_func_post.
  { eapply hoare_func_pre.
    2 : {
      unshelve eapply (proj1 (RegisterAction_execute_body' _ _ _ _ s _ _ _ _ _ (fun _ => True) _ _ _ _ _));
        eauto.
    }
    entailer.
  }
  entailer.
Qed.

Definition extend_hash_output_Z (hash_w : N) (output : list bool) : Z :=
  let output_w := N.of_nat (List.length output) in
  let num_copies := N.div hash_w output_w in
  let num_remainder := Z.of_N (N.modulo hash_w output_w) in
  let lsbs := repeat_concat_list (N.to_nat num_copies) output in
  let msbs := sublist (Z.of_N output_w - num_remainder) (Z.of_N output_w) output in
  BitArith.lbool_to_val (app msbs lsbs) 1 0.

Definition dummy_Z : Z.
Proof. exact 0. Qed.

Definition hash_Z (hash_w : N) (poly : CRC_polynomial) (v : Val) : Z :=
  match convert_to_bits v with
  | Some input =>
      extend_hash_output_Z hash_w (Hash.compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_N (CRCP_coeff poly))
          (lbool_to_N (CRCP_init poly)) (lbool_to_N (CRCP_xor poly))
          (CRCP_reversed poly) (CRCP_reversed poly) input)
  | None =>
      dummy_Z
  end.

Definition Hash_get_fundef : (@fundef tags_t) := FExternal "Hash" "get".

Definition Hash_get_spec : func_spec :=
  WITH p (* path *) hash_w poly
      (H_p : PathMap.get p (ge_ext ge) = Some (EnvHash (hash_w, poly)))
      (H_width : (CRCP_width poly > 0)%N),
    PATH p
    MOD None []
    WITH (v : Val),
      PRE
        (ARG [eval_val_to_sval v]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] (P4Bit hash_w (hash_Z hash_w poly v))
        (MEM []
        (EXT []))).

Lemma Zlength_repeat_concat_list : forall {A} num (l : list A),
  Zlength (repeat_concat_list num l) = Z.of_nat num * Zlength l.
Proof.
  intros. unfold repeat_concat_list.
  assert (forall l',
    Zlength
      ((fix repeat_concat_list' (num0 : nat) (l0 res : list A) {struct num0} : list A :=
          match num0 with
          | 0%nat => res
          | S num' => repeat_concat_list' num' l0 (l0 ++ res)
          end) num l l') = Z.of_nat num * Zlength l + Zlength l'). {
    induction num; intros.
    - list_solve.
    - rewrite IHnum.
      list_solve.
  }
  specialize (H []).
  list_solve.
Qed.

Lemma Hash_get_body targs :
  func_sound ge Hash_get_fundef targs Hash_get_spec.
Proof.
  intros_fs_bind.
  split.
  2 : {
    red. intros.
    inv H.
    inv H5. inv H.
    apply modifies_refl.
  }
  intros_fsh_bind.
  hnf; intros.
  inv H0. inv H6.
  inv H0.
  eapply eq_trans in H1; only 2 : (symmetry; apply H_p).
  symmetry in H1; inv H1.
  unfold hash_Z.
  destruct H as [? []].
  hnf in H. inv H. inv H8.
  inv H3. clear H9.
  assert (sval_to_val read_ndetbit (eval_val_to_sval v) v0). {
    eapply exec_val_trans. 2, 3 : eassumption.
    red; clear; sauto lq: on.
  }
  clear H7. rename H into H7.
  apply sval_to_val_eval_val_to_sval_iff in H7. 2 : {
    clear; sauto lq: on.
  }
  subst.
  rewrite H2. clear H2.
  split.
  { inv H12. constructor. }
  split.
  { apply eval_val_to_sval_ret_denote.
    unfold extend_hash_output_Z.
    unfold P4Bit.
    unfold to_loptbool.
    rewrite to_lbool_lbool_to_val'. 2 : {
      clear -H_width.
      assert (Datatypes.length
                 (Hash.compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_N (CRCP_coeff poly))
                    (lbool_to_N (CRCP_init poly)) (lbool_to_N (CRCP_xor poly))
                    (CRCP_reversed poly) (CRCP_reversed poly) input) = N.to_nat (CRCP_width poly)). {
        apply Hash.length_compute_crc.
      }
      revert H.
      generalize (Hash.compute_crc (N.to_nat (CRCP_width poly)) (lbool_to_N (CRCP_coeff poly))
                    (lbool_to_N (CRCP_init poly)) (lbool_to_N (CRCP_xor poly))
                    (CRCP_reversed poly) (CRCP_reversed poly) input).
      intros.
      replace (N.of_nat (Datatypes.length b)) with (Z.to_N (Zlength b)). 2 : {
        rewrite Zlength_correct. lia.
      }
      assert (Zlength b > 0). {
        rewrite Zlength_correct. lia.
      }
      clear -H0.
      assert (0 <= Z.of_N (hash_w mod Z.to_N (Zlength b)) < (Zlength b)). {
        assert (0 <= hash_w mod Z.to_N (Zlength b) < Z.to_N (Zlength b))%N. {
          apply N.mod_bound_pos; lia.
        }
        lia.
      }
      list_simplify.
      rewrite Zlength_repeat_concat_list.
      replace (Z.of_N (Z.to_N (Zlength b))) with (Zlength b) by list_solve.
      replace (Z.of_nat (N.to_nat (hash_w / Z.to_N (Zlength b))) * Zlength b) with
        (Z.of_N (hash_w / Z.to_N (Zlength b) * Z.to_N (Zlength b))) by lia.
      pose proof (N.div_mod hash_w (Z.to_N (Zlength b))).
      lia.
    }
    reflexivity.
  }
  repeat constructor.
Qed.

(* Lemmas for table matching simplifcation. *)

Lemma reduce_match_range: forall w x lo hi x' lo' hi' xb lob hib,
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int lo = Some (w, lo', lob) ->
  Tofino.assert_int hi = Some (w, hi', hib) ->
  Tofino.values_match_range x lo hi = (lo' <=? x') && (x' <=? hi').
Proof.
  intros.
  unfold Tofino.values_match_range.
  rewrite H, H0, H1. rewrite N.eqb_refl. simpl.
  reflexivity.
Qed.

Lemma reduce_match_singleton: forall w x y x' y' xb yb,
  val_sim x y ->
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int y = Some (w, y', yb) ->
  Tofino.values_match_singleton x y = (x' =? y').
Proof.
  intros. revert y H H1.
  induction x;
  induction y; intros;
  simpl in H0; simpl in H1; unfold val_sim in H; try discriminate; try inv H.
  { unfold Tofino.values_match_singleton, Ops.eval_binary_op_eq.
    remember (P4Arith.BitArith.from_lbool value0) as n0_name. inv H1.
    remember (P4Arith.BitArith.from_lbool value) as n_name. inv H0.
    rewrite N.eqb_refl. trivial. }
  { unfold Tofino.values_match_singleton, Ops.eval_binary_op_eq.
    remember (P4Arith.IntArith.from_lbool value0) as z0_name. inv H1.
    remember (P4Arith.IntArith.from_lbool value) as z_name. inv H0.
    rewrite N.eqb_refl. trivial. }
  unfold Tofino.values_match_singleton in IHx |- *. simpl in IHx |- *. rewrite String.eqb_refl.
  eapply IHx; assumption.
Qed.

Lemma assert_int_len : forall x w x' xb,
  Tofino.assert_int x = Some (w, x', xb) -> Z.to_N (Zlength xb) = w.
Proof.
  induction x; intros; simpl in H; try discriminate.
  - unfold P4Arith.BitArith.from_lbool in H; inv H; trivial.
  - unfold P4Arith.IntArith.from_lbool in H; inv H; trivial.
  - eapply IHx; eauto.
Qed.

(* This lemma is unused. *)
Lemma to_lbool''_to_lbool : forall (width : N) (value : Z),
  rev (to_lbool'' (N.to_nat width) value) = P4Arith.to_lbool width value.
Proof.
  intros.
  apply to_lbool''_to_lbool'.
Qed.

(* This lemma is unused. *)
Lemma bit_to_from_bool : forall bl,
  P4Arith.to_lbool (fst (P4Arith.BitArith.from_lbool bl)) (snd (P4Arith.BitArith.from_lbool bl)) = bl.
Proof.
  intros.
  rewrite <- to_lbool''_to_lbool.
  unfold BitArith.from_lbool, BitArith.lbool_to_val. simpl.
  rewrite <- Zlength_rev. rewrite <- (rev_involutive bl) at 3. f_equal.
  generalize (rev bl). clear bl. intro bl.
  induction bl; auto.
  simpl.
  replace (N.to_nat (Z.to_N (Zlength (a :: bl)))) with (S (N.to_nat (Z.to_N (Zlength bl)))) by list_solve.
  simpl to_lbool''.
  destruct a; rewrite P4Arith.BitArith.le_lbool_to_val_1_0.
  - f_equal.
    { replace (P4Arith.BitArith.le_lbool_to_val bl 1 0 * 2 + 1) with
        (1 + 2 * P4Arith.BitArith.le_lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    rewrite Z.div_add_l by lia.
    replace (1 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
  - f_equal.
    { replace (P4Arith.BitArith.le_lbool_to_val bl 1 0 * 2 + 0) with
        (0 + 2 * P4Arith.BitArith.le_lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    rewrite Z.div_add_l by lia.
    replace (0 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
Qed.

(* This lemma is unused. *)
Lemma int_to_from_bool : forall bl,
  P4Arith.to_lbool (fst (P4Arith.IntArith.from_lbool bl)) (snd (P4Arith.IntArith.from_lbool bl)) = bl.
Proof.
  intros.
  rewrite <- to_lbool''_to_lbool.
  unfold IntArith.from_lbool, IntArith.lbool_to_val. simpl.
  rewrite <- Zlength_rev. rewrite <- (rev_involutive bl) at 3. f_equal.
  generalize (rev bl). clear bl. intro bl.
  induction bl; auto.
  simpl.
  replace (N.to_nat (Z.to_N (Zlength (a :: bl)))) with (S (N.to_nat (Z.to_N (Zlength bl)))) by list_solve.
  simpl to_lbool''.
  destruct a; rewrite P4Arith.IntArith.le_lbool_to_val_1_0.
  - f_equal.
    { destruct bl as [ | b bl']; auto.
      set (bl := b :: bl') in *.
      replace (P4Arith.IntArith.le_lbool_to_val bl 1 0 * 2 + 1) with
        (1 + 2 * P4Arith.IntArith.le_lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    destruct bl as [ | b bl']; auto.
    set (bl := b :: bl') in *.
    rewrite Z.div_add_l by lia.
    replace (1 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
  - f_equal.
    { destruct bl as [ | b bl']; auto.
      set (bl := b :: bl') in *.
      replace (P4Arith.IntArith.le_lbool_to_val bl 1 0 * 2 + 0) with
        (0 + 2 * P4Arith.IntArith.le_lbool_to_val bl 1 0) by lia.
      rewrite Z.odd_add_mul_2; auto.
    }
    destruct bl as [ | b bl']; auto.
    set (bl := b :: bl') in *.
    rewrite Z.div_add_l by lia.
    replace (0 / 2) with 0 by auto.
    rewrite Z.add_0_r.
    apply IHbl.
Qed.

(* This lemma is unused. *)
Lemma assert_int_conv : forall w x x' xb,
  Tofino.assert_int x = Some (w, x', xb) ->
  P4Arith.to_lbool w x' = xb.
Proof.
  induction x; intros; simpl in H; try discriminate; inv H.
  - apply bit_to_from_bool.
  - apply int_to_from_bool.
  - auto.
Qed.

Lemma reduce_match_mask: forall w x v m x' v' m' xb vb mb,
  Tofino.assert_int x = Some (w, x', xb) ->
  Tofino.assert_int v = Some (w, v', vb) ->
  Tofino.assert_int m = Some (w, m', mb) ->
  Tofino.values_match_mask x v m = Tofino.vmm_help xb vb mb.
Proof.
  intros.
  unfold Tofino.values_match_mask; rewrite H, H0, H1; rewrite N.eqb_refl; simpl.
  auto.
Qed.

(* NoAction *)

Definition NoAction_fundef: @fundef tags_t :=
  FInternal [] (BlockEmpty default).

Definition NoAction_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH,
      PRE
        (ARG []
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
        (EXT []))).

Lemma NoAction_body :
  func_sound ge NoAction_fundef nil NoAction_spec.
Proof.
  start_function.
  step.
  entailer.
Qed.

End TofinoSpec.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) =>
  (refine (proj2 (Hash_get_body _ _ _ _ _ _ _)); try exact (@nil _); compute; reflexivity) : func_specs.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply packet_in_advance_body) : func_specs.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (refine (proj2 (packet_in_extract_body _ _ _)); exact TypBool) : func_specs.

#[export] Hint Extern 5 (func_modifies ?g _ _ _ _) => (apply (parser_reject_body g g)) : func_specs.
