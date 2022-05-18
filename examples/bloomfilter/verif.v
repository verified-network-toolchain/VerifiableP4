Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Coq.Program.Basics.
Open Scope string_scope.
Import ListNotations.

Require Import Poulet4.Utils.Maps.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Transformations.SimplExpr.
Require Import Poulet4.P4light.Architecture.V1Model.
Require Import Poulet4.Utils.P4Arith.

Require Import ProD3.core.Core.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.general_bf.

Instance target : @Target Info (@Expression Info) := V1Model.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Opaque PathMap.empty PathMap.set.

(* Global environment *)
Definition ge : genv := Eval compute in gen_ge prog.

(* Initial extern state *)
Definition instantiation := Eval compute in instantiate_prog ge prog.
Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition custom_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "custom_metadata_t" (ge_typ ge)).

Definition standard_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "standard_metadata_t" (ge_typ ge)).

Definition dummy_fundef : @fundef Info := FExternal "" "".
Opaque dummy_fundef.

Open Scope func_spec.

(* Bloom filter encoding *)

Notation Filter := row.

Definition bloomfilter_state : Type := frame.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Definition list_of_filter (f : Filter) : list Z := map bool_to_Z f.

Definition NUM_ENTRY : Z := 1024.

Definition blooms (bst: bloomfilter_state) : list (list Z) := map list_of_filter bst.

Definition reg_encode (l : list Z) : extern_object :=
  ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) l)).

(* list_of_filter lemmas *)

Lemma Zlength_seq : forall n start,
  0 <= n ->
  Zlength (seq start (Z.to_nat n)) = n.
Proof.
  intros.
  pose proof (seq_length (Z.to_nat n) start).
  rewrite Zlength_length; eauto.
Qed.

Hint Rewrite Zlength_seq using lia : Zlength.

Lemma Znth_seq : forall n i start,
  0 <= i < n ->
  Znth i (seq start (Z.to_nat n)) = (start + Z.to_nat i)%nat.
Proof.
  intros.
  rewrite <- nth_Znth by list_solve.
  rewrite seq_nth; lia.
Qed.

Hint Rewrite Znth_seq using lia : Znth.

Definition bf_wellformed (bst: bloomfilter_state) :=
  Zlength bst = 3 /\ Forall (fun r => Zlength r = NUM_ENTRY) bst.

Lemma Zlength_list_of_filter : forall filter,
  Zlength (list_of_filter filter) = Zlength filter.
Proof.
  intros.
  unfold list_of_filter.
  list_solve.
Qed.

Hint Rewrite Zlength_list_of_filter using lia : Zlength.

Lemma Znth_list_of_filter : forall filter i,
  0 <= i < Zlength filter ->
  Znth i (list_of_filter filter) = bool_to_Z (Znth i filter).
Proof.
  intros.
  unfold list_of_filter.
  list_simplify.
Qed.

Hint Rewrite Znth_list_of_filter using lia : Znth.

Lemma update_bit : forall filter hash,
  reg_encode (list_of_filter (row_insert filter hash)) =
  ObjRegister
    (upd_Znth hash (map ValBaseBit (map (to_lbool 1) (list_of_filter filter)))
       (ValBaseBit (to_lbool 1 (BitArith.mod_bound 1 1)))).
Proof.
  intros.
  unfold reg_encode.
  f_equal.
  unfold row_insert.
  list_simplify.
  - subst.
    rewrite Znth_list_of_filter; list_solve.
  - rewrite Znth_list_of_filter; list_solve.
Qed.

Lemma get_bit : forall (filter : Filter) hash,
  0 <= hash < Zlength filter ->
  Znth hash (map ValBaseBit (map (to_lbool 1) (list_of_filter filter)))
    = ValBaseBit [Znth hash filter].
Proof.
  intros.
  list_simplify.
  destruct (Znth hash filter); reflexivity.
Qed.

Definition Add_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Add"; "apply"] (ge_func ge)).

Definition havoc := uninit_sval_of_sval.

(* Section CRC.
Import Hexadecimal.

Definition CRC : list bool -> list bool := Hash.compute_crc 16%nat (D8 (D0 (D0 (D5 Nil)))) zero zero true true.

End CRC.

Definition BASE : Z := 0.
Definition MAX : Z := 1024.

Definition CRC_Z (data : list bool) : Z :=
  BASE + Z.modulo (BitArith.lbool_to_val (CRC data) 1 0) MAX. *)

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

Definition encode_bloomfilter_state bf : ext_pred :=
  ExtPred.and
    (ExtPred.singleton ["bloom0"] (reg_encode (Znth 0 (blooms bf))))
    (ExtPred.and
      (ExtPred.singleton ["bloom1"] (reg_encode (Znth 1 (blooms bf))))
      (ExtPred.singleton ["bloom2"] (reg_encode (Znth 2 (blooms bf))))).

Definition bloomfilter_add bf data :=
  general_bf.add [CRC_pad0; CRC_pad1; CRC_pad2] bf data.

Definition bloomfilter_query bf data :=
  general_bf.query [CRC_pad0; CRC_pad1; CRC_pad2] bf data.

Definition havoc_typ (typ : @P4Type Info) : Sval :=
  force ValBaseNull (uninit_sval_of_typ None typ).

Open Scope arg_ret_assr.

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
    WITH (data : Z) (bf : bloomfilter_state) (H_bf: bf_wellformed bf),
      PRE
        (ARG [myHeader_encode data; havoc_typ custom_metadata_t]
        (MEM []
        (EXT [encode_bloomfilter_state bf])))
      POST
        (ARG_RET [myHeader_encode data; havoc_typ custom_metadata_t] ValBaseNull
        (MEM []
        (EXT [encode_bloomfilter_state (bloomfilter_add bf data)]))).

Lemma Add_body : fundef_satisfies_spec ge Add_fundef nil Add_spec.
Proof.
  start_function.
  destruct H_bf. do 3 (destruct bf; [exfalso; list_solve |]).
  destruct bf; [|exfalso; list_solve].
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 3 3)].
  2 : entailer.
  reflexivity.
  replace (CRC_Z _) with (CRC_pad0 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 5 5)].
  2 : entailer.
  reflexivity.
  replace (CRC_Z _) with (CRC_pad1 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 7 7)].
  2 : entailer.
  reflexivity.
  replace (CRC_Z _) with (CRC_pad2 data) by reflexivity.
  simpl MEM.
  unfold encode_bloomfilter_state.
  normalize_EXT.
  step_call register_write_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
  { apply CRC_range. }
  step_call register_write_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
  { apply CRC_range. }
  step_call register_write_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
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
    WITH (data : Z) (bf : bloomfilter_state) (H_bf: bf_wellformed bf),
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

Lemma Query_body : fundef_satisfies_spec ge Query_fundef nil Query_spec.
Proof.
  start_function.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 3 3)].
  2 : { entailer. }
  reflexivity.
  replace (CRC_Z _) with (CRC_pad0 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 5 5)].
  2 : entailer.
  reflexivity.
  replace (CRC_Z _) with (CRC_pad1 data) by reflexivity.
  step_call hash_body [ValBaseBit (to_lbool 16 data); ValBaseBit (to_lbool 7 7)].
  2 : entailer.
  reflexivity.
  replace (CRC_Z _) with (CRC_pad2 data) by reflexivity.
  simpl MEM.
  unfold encode_bloomfilter_state.
  normalize_EXT.
  step_call register_read_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
  { apply CRC_range. }
  step_call register_read_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
  { apply CRC_range. }
  step_call register_read_body.
  reflexivity. 2: simpl; lia.
  2 : entailer.
  { apply CRC_range. }
  step.
  step.
  destruct H_bf. do 3 (destruct bf; [exfalso; list_solve |]).
  destruct bf; [|exfalso; list_solve]. rewrite Forall_forall in H0.
  assert (Zlength r = NUM_ENTRY) by (apply H0; now left).
  assert (Zlength r0 = NUM_ENTRY) by (apply H0; right; now left).
  assert (Zlength r1 = NUM_ENTRY) by (apply H0; right; right; now left).
  unfold blooms. cbn [map]. rewrite Znth_0_3, Znth_1_3, Znth_2_3.
  rewrite !get_bit by (first [rewrite H1 | rewrite H2 | rewrite H3]; apply CRC_range).
  entailer.
  { simpl build_abs_unary_op.
    replace (query [CRC_pad0; CRC_pad1; CRC_pad2] [r; r0; r1] data) with
      (Znth (CRC_pad0 data) r && Znth (CRC_pad1 data) r0 && Znth (CRC_pad2 data) r1).
    2: { unfold query, frame_query, Utils.fold_andb, Utils.map2, row_query.
         cbn [map combine uncurry fold_left]. auto. }
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
    (general_bf.add [CRC_pad0; CRC_pad1; CRC_pad2] bf data, 1)
  else
    (bf, if general_bf.query [CRC_pad0; CRC_pad1; CRC_pad2] bf data then 0 else 511).

Definition bloomfilter_spec : func_spec :=
  WITH ,
    PATH ["main"; "ig"]
    MOD None bloomfilter_exts
    WITH in_port data bf (H : 0 <= in_port < 2) (H_bf: bf_wellformed bf),
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

Lemma bloomfilter_body : fundef_satisfies_spec ge MyIngress_fundef nil bloomfilter_spec.
Proof.
  start_function.
  step_if.
  {
    (* clear up H0 *)
    fold abs_eq in H0.
    rewrite get_update_same in H0 by auto.
    change ((eval_val_to_sval
            (ValBaseBit [false; false; false; false; false; false; false; false; false])))
      with (ValBaseBit (to_loptbool 9 0)) in H0.
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
      with (ValBaseBit (to_loptbool 9 0)) in H0.
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
        rewrite H_query.
        repeat constructor.
    }
    {
      rewrite get_update_same in H0 by auto.
      destruct (query [CRC_pad0; CRC_pad1; CRC_pad2] bf data) eqn:H_query; inv H0.
      simpl (force empty_statement _).
      step.
      step.
      entailer.
      - repeat constructor.
      - unfold process.
        rewrite H_query.
        repeat constructor.
    }
  }
Qed.
