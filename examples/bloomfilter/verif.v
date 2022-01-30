Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Require Import Coq.Program.Basics.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.bloomfilter.bloomfilter.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Arith.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.ConcreteHoare.
Require Import ProD3.core.EvalExpr.
Require Import ProD3.core.Members.
(* Require Import ProD3.core.HoareSoundness. *)
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.Implies.
Require Import ProD3.core.Modifies.
Require Import ProD3.core.Tactics.
Require Import ProD3.core.V1ModelSpec.
Require Import ProD3.core.Coqlib.
Require Import Coq.micromega.Lia.

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

Notation Filter := (Filter Z).

Definition bloomfilter_state : Type := Filter * Filter * Filter.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Definition list_of_filter (size : Z) (f : Filter) : list Z :=
  map (compose bool_to_Z (compose f Z.of_nat)) (seq O (Z.to_nat size)).

Definition NUM_ENTRY : Z := 1024.

Definition bloom0 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (fst (fst bst)).

Definition bloom1 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (snd (fst bst)).

Definition bloom2 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (snd bst).

Definition reg_encode (l : list Z) : extern_object :=
  ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) l)).

(* list_of_filter lemmas *)

Lemma Zlength_list_of_filter : forall n filter,
  0 <= n ->
  Zlength (list_of_filter n filter) = n.
Proof.
  intros.
  unfold list_of_filter.
  rewrite Zlength_map.
  pose proof (seq_length (Z.to_nat n) 0).
  rewrite Zlength_length; eauto.
Qed.

Hint Rewrite Zlength_list_of_filter using lia : Zlength.

Lemma Znth_list_of_filter : forall n filter i,
  0 <= i < n ->
  Znth i (list_of_filter n filter) = bool_to_Z (filter i).
Proof.
Admitted.

Hint Rewrite Znth_list_of_filter using lia : Znth.

Lemma update_bit : forall filter hash,
  reg_encode (list_of_filter NUM_ENTRY (upd Z Z.eqb filter hash true)) =
  ObjRegister
    (upd_Znth hash (map ValBaseBit (map (to_lbool 1) (list_of_filter NUM_ENTRY filter)))
       (ValBaseBit (to_lbool 1 (BitArith.mod_bound 1 1)))).
Proof.
  intros.
  unfold reg_encode.
  f_equal.
  unfold upd.
  unfold NUM_ENTRY.
  list_simplify.
  - replace (hash =? i) with true by lia.
    reflexivity.
  - replace (hash =? i) with false by lia.
    reflexivity.
Qed.

Lemma get_bit : forall (filter : Filter) hash,
  0 <= hash < NUM_ENTRY ->
  Znth hash (map ValBaseBit (map (to_lbool 1) (list_of_filter NUM_ENTRY filter)))
    = ValBaseBit [filter hash].
Proof.
  intros.
  list_simplify.
  destruct (filter hash); reflexivity.
Qed.

Definition Add_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Add"; "apply"] (ge_func ge)).

Definition havoc := uninit_sval_of_sval.

Section CRC.
Import Hexadecimal.

Definition CRC : list bool -> list bool := Hash.compute_crc 16%nat (D8 (D0 (D0 (D5 Nil)))) zero zero true true.

(* This may be unnecessary. *)
Lemma CRC_length : forall data,
  List.length (CRC data) = 16%nat.
Proof.
Admitted.

End CRC.

Definition BASE : Z := 0.
Definition MAX : Z := 1024.

Definition CRC_Z (data : list bool) : Z :=
  BASE + Z.modulo (BitArith.lbool_to_val (CRC data) 1 0) MAX.

Axiom CRC_range : forall data, 0 <= CRC_Z data < NUM_ENTRY.

Definition CRC_pad (pad : list bool) (data : Z) : Z :=
  CRC_Z (List.concat [to_lbool 16%N data; pad]).

Definition CRC_pad0 := CRC_pad (to_lbool 3%N 3).
Definition CRC_pad1 := CRC_pad (to_lbool 5%N 5).
Definition CRC_pad2 := CRC_pad (to_lbool 7%N 7).

Definition hash_fundef :=
  force dummy_fundef (PathMap.get ["hash"] (ge_func ge)).

Open Scope arg_ret_assr.

(* A more restricted func spec, but should be sound. *)
Definition hash_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH (data : list Val) (input : list bool)
      (_ : concat_tuple data = Some input),
      PRE
        (ARG [ValBaseEnumField "HashAlgorithm" "crc16";
              ValBaseBit (to_loptbool 10 BASE);
              eval_val_to_sval (ValBaseTuple data);
              ValBaseBit (to_loptbool 10 MAX)]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [ValBaseBit (to_loptbool 32%N (CRC_Z input))] ValBaseNull
        (MEM []
        (EXT []))).

Axiom hash_body : forall targs,
  fundef_satisfies_spec ge hash_fundef targs hash_spec.

Hint Extern 5 (func_modifies _ _ _ _ _) => (apply hash_body) : func_specs.
Hint Extern 1 (list P4Type) => (exact (@nil _)) : func_specs.

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

Definition Add_spec : func_spec :=
  WITH p,
    PATH p
    MOD None [["bloom0"]; ["bloom1"]; ["bloom2"]]
    WITH (data : Z) (bf : bloomfilter_state),
      PRE
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        (ARG [hdr; force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)]
        (MEM []
        (EXT [(["bloom0"], reg_encode (bloom0 bf));
              (["bloom1"], reg_encode (bloom1 bf));
              (["bloom2"], reg_encode (bloom2 bf))])))
      POST
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        let bf' := bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf data in
        (ARG_RET [hdr; force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)] ValBaseNull
        (MEM []
        (EXT [(["bloom0"], reg_encode (bloom0 bf'));
              (["bloom1"], reg_encode (bloom1 bf'));
              (["bloom2"], reg_encode (bloom2 bf'))]))).

Lemma Add_body : fundef_satisfies_spec ge Add_fundef nil Add_spec.
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
  step_call register_write_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step_call register_write_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step_call register_write_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step.
  entailer.
  { repeat constructor. }
  destruct bf as [[] ?]. apply update_bit.
  destruct bf as [[] ?]. apply update_bit.
  destruct bf as [[] ?]. apply update_bit.
Qed.

Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Add_body) : func_specs.

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
        (EXT [(["bloom0"], reg_encode (bloom0 bf));
              (["bloom1"], reg_encode (bloom1 bf));
              (["bloom2"], reg_encode (bloom2 bf))])))
      POST
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        let meta := update "member0"
          (ValBaseBit [Some (bloomfilter.query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data)])
          (force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)) in
        (ARG_RET [hdr; meta] ValBaseNull
        (MEM []
        (EXT []))).

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
  step_call register_read_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step_call register_read_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step_call register_read_body.
  reflexivity.
  2 : entailer.
  { apply CRC_range. }
  step.
  step.
  destruct bf as [[f0 f1] f2].
  unfold bloom0.
  unfold bloom1.
  unfold bloom2.
  rewrite !get_bit by (apply CRC_range).
  entailer.
  { simpl build_abs_unary_op.
    unfold query, bloomfilter.get.
    simpl.
    destruct (f0 (CRC_pad0 data));
      destruct (f1 (CRC_pad1 data));
      destruct (f2 (CRC_pad2 data));
      repeat constructor.
  }
Qed.

Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Query_body) : func_specs.

Definition MyIngress_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["MyIngress"; "apply"] (ge_func ge)).

Definition process (in_port data : Z) (bf : bloomfilter_state) : (bloomfilter_state * Z) :=
  if in_port =? 0 then
    (bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf data, 1)
  else
    (bf, if bloomfilter.query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data then 0 else 511).

Definition bloomfilter_spec : func_spec :=
  WITH ,
    PATH ["main"; "ig"]
    MOD None [["bloom0"]; ["bloom1"]; ["bloom2"]]
    WITH in_port data bf (H : 0 <= in_port < 2),
      PRE
        (ARG [
          ValBaseStruct [("myHeader",
            ValBaseHeader [("data", ValBaseBit (to_loptbool 16 data))] (Some true))];
          force ValBaseNull (uninit_sval_of_typ None custom_metadata_t);
          update "ingress_port" (ValBaseBit (to_loptbool 9 in_port))
            (force ValBaseNull (uninit_sval_of_typ None standard_metadata_t))]
        (MEM []
        (EXT [
          (["bloom0"], reg_encode (bloom0 bf));
          (["bloom1"], reg_encode (bloom1 bf));
          (["bloom2"], reg_encode (bloom2 bf))
        ])))
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
        (EXT [
          (["bloom0"], reg_encode (bloom0 bf'));
          (["bloom1"], reg_encode (bloom1 bf'));
          (["bloom2"], reg_encode (bloom2 bf'))
        ]))).

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
    step_call Add_body.
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
    step_call Query_body.
    entailer.
    step_if.
    {
      rewrite get_update_same in H0 by auto.
      destruct (query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data) eqn:H_query; inv H0.
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
      destruct (query Z CRC_pad0 CRC_pad1 CRC_pad2 bf data) eqn:H_query; inv H0.
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
