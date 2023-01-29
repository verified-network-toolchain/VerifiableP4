Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Coq.Program.Program.
Open Scope string_scope.
Import ListNotations.

Require Import Poulet4.Utils.Maps.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Transformations.SimplExpr.
Require Import Poulet4.P4light.Architecture.V1ModelTarget.
Require Import Poulet4.Utils.P4Arith.

Require Import ProD3.core.Core.
Require Import ProD3.core.V1ModelSpec.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.general_bf.

#[local] Instance target : @Target Info (@Expression Info) := V1Model.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Opaque PathMap.empty PathMap.set.

(* Global environment *)
Definition ge : genv := ltac:(
  let ge := eval compute in (gen_ge prog) in
  lazymatch ge with
  | Result.Ok ?ge =>
      exact (ge : (@genv _ ltac:(typeclasses eauto)))
  | Result.Error ?msg =>
      fail 0 "Global environment evaluation failed with message:" msg
  end).

(* Initial extern state *)
Definition instantiation := ltac:(
  let instantiation := eval compute in (instantiate_prog ge (ge_typ ge) prog) in
  lazymatch instantiation with
  | Result.Ok ?instantiation =>
      exact instantiation
  | Result.Error ?msg =>
      fail 0 "Global environment evaluation failed with message:" msg
  end).

Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition custom_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "custom_metadata_t" (ge_typ ge)).

Definition standard_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "standard_metadata_t" (ge_typ ge)).

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.

Open Scope func_spec.

Definition NUM_ENTRY : Z := 1024.

Definition NUM_ROW : Z := 3.

(* Bloom filter encoding *)

Definition Filter := row NUM_ENTRY.

Definition bloomfilter_state : Type := frame NUM_ROW NUM_ENTRY.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Definition list_of_filter (f : Filter) := map_listn bool_to_Z f.

Definition blooms (bst: bloomfilter_state) := map_listn list_of_filter bst.

Definition reg_encode {size} (l : listn Z size) : extern_object :=
  ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (`l))).

(* list_of_filter lemmas *)

Lemma Zlength_seq : forall n start,
  0 <= n ->
  Zlength (seq start (Z.to_nat n)) = n.
Proof.
  intros.
  pose proof (seq_length (Z.to_nat n) start).
  rewrite Zlength_length; eauto.
Qed.

#[local] Hint Rewrite Zlength_seq using lia : Zlength.

Lemma Znth_seq : forall n i start,
  0 <= i < n ->
  Znth i (seq start (Z.to_nat n)) = (start + Z.to_nat i)%nat.
Proof.
  intros.
  rewrite <- nth_Znth by list_solve.
  rewrite seq_nth; lia.
Qed.

#[local] Hint Rewrite Znth_seq using lia : Znth.

Lemma Znth_list_of_filter : forall filter i,
  0 <= i < NUM_ENTRY ->
  Znth i (` (list_of_filter filter)) = bool_to_Z (Znth i (`filter)).
Proof.
  intros. destruct filter as [filter ?H].
  unfold list_of_filter, map_listn. simpl.
  list_simplify.
Qed.

#[local] Hint Rewrite Znth_list_of_filter using lia : Znth.

Lemma update_bit : forall filter hash,
    reg_encode (list_of_filter (row_insert filter hash)) =
  ObjRegister
    (upd_Znth hash (map ValBaseBit (map (to_lbool 1) (` (list_of_filter filter))))
       (ValBaseBit (to_lbool 1 (BitArith.mod_bound 1 1)))).
Proof.
  intros.
  unfold reg_encode.
  f_equal.
  unfold row_insert. simpl.
  destruct filter as [filter ?H]. simpl in *.
  list_simplify. f_equal. list_solve.
Qed.

Lemma get_bit : forall (filter : Filter) hash,
  0 <= hash < NUM_ENTRY ->
  Znth hash (map ValBaseBit (map (to_lbool 1) (` (list_of_filter filter))))
  = ValBaseBit [Znth hash (`filter)].
Proof.
  intros. unfold list_of_filter, map_listn. destruct filter as [filter ?H]. simpl.
  list_simplify.
  destruct (Znth hash filter); reflexivity.
Qed.

Definition Add_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Add"; "apply"] (ge_func ge)).

Definition havoc := uninit_sval_of_sval.

Section CRC.

Definition CRC : list bool -> list bool := Hash.compute_crc 16%nat 0x8005 0 0 true true.

End CRC.

Definition BASE : Z := 0.
Definition MAX : Z := 1024.

Definition CRC_Z (data : list bool) : Z :=
  BASE + Z.modulo (BitArith.lbool_to_val (CRC data) 1 0) MAX.

Lemma CRC_range : forall data, 0 <= CRC_Z data < NUM_ENTRY.
Proof.
  intros. unfold CRC_Z. unfold BASE. rewrite Z.add_0_l.
  apply Z.mod_pos_bound. unfold NUM_ENTRY. lia.
Qed.

Definition CRC_pad (pad : list bool) (data : Z) : Z :=
  CRC_Z (List.concat [to_lbool 16%N data; pad]).

Definition CRC_pad0 := CRC_pad (to_lbool 3%N 3).
Definition CRC_pad1 := CRC_pad (to_lbool 5%N 5).
Definition CRC_pad2 := CRC_pad (to_lbool 7%N 7).

Definition bloomfilter_exts := [["bloom0"]; ["bloom1"]; ["bloom2"]].

#[global] Program Instance z_num_entry_inhabit: Inhabitant (listn Z NUM_ENTRY) :=
  Zrepeat 0 NUM_ENTRY.

Definition encode_bloomfilter_state bf : ext_pred :=
  ExtPred.and
    (ExtPred.singleton ["bloom0"] (reg_encode (Znth 0 (` (blooms bf)))))
    (ExtPred.and
       (ExtPred.singleton ["bloom1"] (reg_encode (Znth 1 (` (blooms bf)))))
       (ExtPred.singleton ["bloom2"] (reg_encode (Znth 2 (` (blooms bf)))))).

Program Definition CRC_pads : listn HashFunc NUM_ROW := [CRC_pad0; CRC_pad1; CRC_pad2].

Definition bloomfilter_add (bf: bloomfilter_state) data :=
  general_bf.add CRC_pads bf data.

Definition bloomfilter_query (bf: bloomfilter_state) data :=
  general_bf.query (`CRC_pads) bf data.

Definition havoc_typ (typ : @P4Type Info) : Sval :=
  force ValBaseNull (uninit_sval_of_typ None typ).

Definition hash_fundef :=
  force dummy_fundef (PathMap.get ["hash"] (ge_func ge)).

Open Scope arg_ret_assr.

Lemma Forall2_bit_refine_eval_val_eq:
  forall l1 l2, Forall2 (exec_val SvalRefine.bit_refine) (map eval_val_to_sval l1) l2 ->
           map eval_val_to_sval l1 = l2.
Proof.
  induction l1; simpl; intros; inv H; auto. f_equal. 2: now apply IHl1.
  apply exec_val_eval_val_to_sval_eq in H2; auto. intros. now inv H.
Qed.

Lemma Forall2_ndetbit_eval_val_eq: forall l1 l2,
    Forall2 (exec_val read_ndetbit) (map eval_val_to_sval l1) l2 -> l1 = l2.
Proof.
  induction l1; simpl; intros; inv H; auto. f_equal. 2: now apply IHl1.
  apply sval_to_val_eval_val_to_sval_eq in H2; auto. intros. now inv H.
Qed.

(* A more restricted func spec, but should be sound. *)
Definition hash_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH (data : list Val) (input : list bool)
      (_ : concat_tuple data = Some input),
      PRE
        (ARG [ValBaseEnumField "HashAlgorithm" "crc16";
              ValBaseBit (to_loptbool 32 BASE);
              eval_val_to_sval (ValBaseTuple data);
              ValBaseBit (to_loptbool 32 MAX)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [ValBaseBit (to_loptbool 32%N (CRC_Z input))] ValBaseNull
        (MEM []
        (EXT []))).

Lemma hash_body : forall targs,
    func_sound ge hash_fundef (TypBit 32%N :: targs) hash_spec.
Proof.
  intros. unfold hash_spec. simpl. split.
  - repeat intro. red. red in H. destruct H. do 2 red in H. inv H. inv H4.
    inv H6. inv H3. inv H5. inv H4. inv H7. inv H8. inv H5.
    apply Members.Forall2_bit_refine_Some_same' in H2, H4. subst. inv H0. inv H7.
    simpl in H. inv H. simpl. red. split; [|split]; auto.
    + Opaque to_lbool. inv H4. inv H6. inv H8. inv H4. apply ValueUtil.Forall2_ndetbit in H2.
      inv H7. inv H6. inv H10. inv H8. inv H6. apply ValueUtil.Forall2_ndetbit in H4. subst.
      inv H13. inv H7. constructor. 2: constructor. unfold bound_hash_output in H4.
      rewrite !bit_from_to_bool in H4. vm_compute in H5. inv H5.
      apply Forall2_bit_refine_eval_val_eq in H3. subst lv'.
      apply Forall2_ndetbit_eval_val_eq in H2. subst vs. rewrite x1 in H9. inv H9.
      unfold CRC_Z, CRC.
      replace (BitArith.mod_bound 32 BASE) with BASE in *
          by (unfold BASE; now vm_compute).
      replace (BitArith.mod_bound 32 MAX) with MAX in *
          by (unfold MAX; now vm_compute). unfold BitArith.from_lbool in H4.
      rewrite Zlength_correct in H4. rewrite Hash.length_compute_crc in H4.
      change (Z.to_N (Z.of_nat 16)) with 16%N in H4. rewrite N.max_id in H4.
      rewrite N.max_l in H4 by lia.
      unfold BitArith.modulo_mod, BitArith.plus_mod in H4.
      rewrite BitArith.mod_bound_double_add, to_lbool_bit_mod in H4.
      unfold to_loptbool. revert H4.
      generalize (to_lbool 32
                         (BASE +
                            BitArith.lbool_to_val
                              (Hash.compute_crc 16 0x8005 0 0 true true input) 1 0
                              mod MAX)). intros. inv H4. constructor.
      rewrite ForallMap.Forall2_forall in H0. destruct H0.
      rewrite <- ForallMap.Forall2_map_l, ForallMap.Forall2_forall. split; auto.
      intros. specialize (H0 _ _ H2). inv H0. constructor.
    + repeat intro. inv H. constructor.
  - repeat intro. unfold modifies. split; only 1 : (simpl; auto). repeat intro.
    inv H. simpl. inv H6. simpl in H. inv H. auto.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply hash_body) : func_specs.
#[local] Hint Extern 1 (list P4Type) => (exact (@nil _)) : func_specs.

(*
control Add(inout headers hdr, inout custom_metadata_t meta) {
    apply{
        hash(meta.index0, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD0}, HASH_MAX);
        hash(meta.index1, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD1}, HASH_MAX);
        hash(meta.index2, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD2}, HASH_MAX);

        bloom0.write(meta.index0, 1);
        bloom1.write(meta.index1, 1);
        bloom2.write(meta.index2, 1);
    }
}
*)

Definition myHeader_encode data :=
  ValBaseStruct
    [("myHeader",
      ValBaseHeader
        [("data", ValBaseBit (to_loptbool 16 data))]
         (Some true))].

Definition Add_spec : func_spec :=
  WITH p,
    PATH p
    MOD None bloomfilter_exts
    WITH (data : Z) (bf : bloomfilter_state),
      PRE
        (ARG [myHeader_encode data; havoc_typ custom_metadata_t]
        (MEM []
        (EXT [encode_bloomfilter_state bf])))
      POST
        (ARG_RET [myHeader_encode data; havoc_typ custom_metadata_t] ValBaseNull
        (MEM []
        (EXT [encode_bloomfilter_state (bloomfilter_add bf data)]))).

Lemma Add_body : func_sound ge Add_fundef nil Add_spec.
Proof.
  start_function.
  destruct bf as [bf ?H]. unfold NUM_ROW in *.
  do 3 (destruct bf; [exfalso; list_solve |]).
  destruct bf; [|exfalso; list_solve].
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 3 3)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad0 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 5 5)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad1 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 7 7)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad2 data) by reflexivity.
  simpl MEM.
  unfold encode_bloomfilter_state.
  normalize_EXT.
  step_call register_write_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step_call register_write_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step_call register_write_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step.
  entailer.
  { repeat constructor. }
  all: unfold blooms, bloomfilter_add, add, frame_insert, Utils.map2;
    cbn [map combine uncurry]; symmetry; apply update_bit.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Add_body) : func_specs.

Definition Query_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Query"; "apply"] (ge_func ge)).

Definition Query_spec : func_spec :=
  WITH p,
    PATH p
    MOD None []
    WITH (data : Z) (bf : bloomfilter_state),
      PRE
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        (ARG [hdr; force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)]
        (MEM []
        (EXT [encode_bloomfilter_state bf])))
      POST
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        let meta := update "member0"
          (ValBaseBit [Some (general_bf.query [CRC_pad0; CRC_pad1; CRC_pad2] bf data)])
          (force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)) in
        (ARG_RET [hdr; meta] ValBaseNull
        (MEM []
           (EXT []))).

Lemma Znth_0_3 {X: Type} {HX: Inhabitant X}: forall (r0 r1 r2: X), Znth 0 [r0; r1; r2] = r0.
Proof. intros. now vm_compute. Qed.

Lemma Znth_1_3 {X: Type} {HX: Inhabitant X}: forall (r0 r1 r2: X), Znth 1 [r0; r1; r2] = r1.
Proof. intros. now vm_compute. Qed.

Lemma Znth_2_3 {X: Type} {HX: Inhabitant X}: forall (r0 r1 r2: X), Znth 2 [r0; r1; r2] = r2.
Proof. intros. now vm_compute. Qed.

Lemma Query_body : func_sound ge Query_fundef nil Query_spec.
Proof.
  start_function.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 3 3)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad0 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 5 5)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad1 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 7 7)].
  { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad2 data) by reflexivity.
  simpl MEM.
  unfold encode_bloomfilter_state.
  normalize_EXT.
  step_call register_read_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step_call register_read_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step_call register_read_body.
  { entailer. }
  reflexivity. 2: simpl; lia.
  { apply CRC_range. }
  step.
  step.
  destruct bf as [bf ?H]. unfold NUM_ROW in *.
  do 3 (destruct bf; [exfalso; list_solve |]).
  destruct bf; [|exfalso; list_solve].
  destruct r as [r ?H]. destruct r0 as [r0 ?H]. destruct r1 as [r1 ?H].
  unfold blooms, map_listn. cbn [map proj1_sig]. rewrite Znth_0_3, Znth_1_3, Znth_2_3.
  rewrite !get_bit by apply CRC_range.
  entailer.
  { simpl build_abs_unary_op.
    unfold query, frame_query, Utils.fold_andb, Utils.map2, row_query.
    cbn [map combine uncurry fold_left proj1_sig andb].
    destruct (Znth (CRC_pad0 data) r);
      destruct (Znth (CRC_pad1 data) r0);
      destruct (Znth (CRC_pad2 data) r1);
      simpl; repeat constructor. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Query_body) : func_specs.

Definition MyIngress_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["MyIngress"; "apply"] (ge_func ge)).

Definition process (in_port data : Z) (bf : bloomfilter_state) : (bloomfilter_state * Z) :=
  if in_port =? 0 then
    (general_bf.add CRC_pads bf data, 1)
  else
    (bf, if general_bf.query (`CRC_pads) bf data then 0 else 511).

Definition bloomfilter_spec : func_spec :=
  WITH ,
    PATH ["main"; "ig"]
    MOD None bloomfilter_exts
    WITH in_port data bf (H : 0 <= in_port < 2),
      PRE
        (ARG [
          ValBaseStruct [("myHeader",
            ValBaseHeader [("data", ValBaseBit (to_loptbool 16 data))] (Some true))];
          force ValBaseNull (uninit_sval_of_typ None custom_metadata_t);
          update "ingress_port" (ValBaseBit (to_loptbool 9 in_port))
            (force ValBaseNull (uninit_sval_of_typ None standard_metadata_t))]
        (MEM []
        (EXT [encode_bloomfilter_state bf])))
      POST
        (* These two lines cannot be merged, because Coq doesn't destruct the pair automatically. *)
        let bf' := fst (process in_port data bf) in
        let out_port := snd (process in_port data bf) in
        (ARG_RET [
          ValBaseStruct [("myHeader",
            ValBaseHeader [("data", ValBaseBit (to_loptbool 16 data))] (Some true))];
          force ValBaseNull (uninit_sval_of_typ None custom_metadata_t);
          update "egress_spec" (ValBaseBit (to_loptbool 9 out_port))
            (force ValBaseNull (uninit_sval_of_typ None standard_metadata_t))]
          ValBaseNull
        (MEM []
        (EXT [encode_bloomfilter_state bf']))).

Lemma mod_bound_eq : forall w n,
  0 <= n < Z.pow 2 (Z.of_N w) ->
  BitArith.mod_bound w n = n.
Proof.
  intros.
  unfold BitArith.mod_bound, BitArith.upper_bound.
  rewrite Zmod_small; auto.
Qed.

Lemma bloomfilter_body : func_sound ge MyIngress_fundef nil bloomfilter_spec.
Proof.
  start_function.
  step_if.
  {
    (* clear up H0 *)
    fold abs_eq in H0.
    rewrite get_update_same in H0 by auto.
    change ((eval_val_to_sval
            (ValBaseBit [false; false; false; false; false; false; false; false; false])))
      with (P4Bit 9 0) in H0.
    change (ValBaseBit (to_loptbool 9 in_port)) with (P4Bit 9 in_port) in H0.
    rewrite abs_eq_bit in H0.
    rewrite !mod_bound_eq in H0 by lia.
    destruct (in_port =? 0) eqn:H_in_port; inv H0.
    assert (in_port = 0) by lia; subst. clear H_in_port.
    step.
    step.
    step_call Add_body. eauto.
    entailer.
    step.
    entailer.
    repeat constructor.
  }
  {
    (* clear up H0 *)
    fold abs_eq in H0.
    rewrite get_update_same in H0 by auto.
    change ((eval_val_to_sval
            (ValBaseBit [false; false; false; false; false; false; false; false; false])))
      with (P4Bit 9 0) in H0.
    change (ValBaseBit (to_loptbool 9 in_port)) with (P4Bit 9 in_port) in H0.
    rewrite abs_eq_bit in H0.
    rewrite !mod_bound_eq in H0 by lia.
    destruct (in_port =? 0) eqn:H_in_port; inv H0.
    assert (in_port = 1) by lia; subst. clear H_in_port.
    simpl (force empty_statement _).
    step.
    step.
    step_call Query_body. eauto.
    entailer.
    step_if.
    {
      rewrite get_update_same in H0 by auto.
      destruct (query [CRC_pad0; CRC_pad1; CRC_pad2] bf data) eqn:H_query; inv H0.
      step.
      step.
      step.
      entailer.
      - repeat constructor.
      - unfold process.
        unfold CRC_pads. cbn [proj1_sig].
        rewrite H_query.
        repeat constructor. }
    {
      rewrite get_update_same in H0 by auto.
      destruct (query [CRC_pad0; CRC_pad1; CRC_pad2] bf data) eqn:H_query; inv H0.
      simpl (force empty_statement _).
      step.
      step.
      entailer.
      - repeat constructor.
      - unfold process.
        unfold CRC_pads. cbn [proj1_sig].
        rewrite H_query.
        repeat constructor.
    }
  }
 Qed.
