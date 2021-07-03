Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.bloomfilter.p4ast.
Require Import ProD3.examples.bloomfilter.bloomfilter.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.HoareSoundness.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.V1ModelLang.
Require Import ProD3.core.ConcreteHoare.

Require Import mathcomp.ssreflect.fintype.

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := Eval compute in gen_ge prog.

Definition instantiation := Eval compute in instantiate_prog ge prog.

(* inst_m *)
Definition inst_m := Eval compute in fst instantiation.

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Notation ident := (P4String.t Info).
Notation path := (list ident).
Notation Val := (@ValueBase Info).

Notation assertion := (@assertion Info).
Notation arg_assertion := (@arg_assertion Info).
Notation ret_assertion := (@ret_assertion Info).
Notation ext_assertion := (@ext_assertion Info).

Module Experiment1.

Definition MyIngress_fundef := Eval compute in
  match PathMap.get [!"MyIngress"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Definition this : path := !["main"; "ig"].

Definition NUM_ENTRY : nat := 1024.

Notation Filter := (Filter 'I_NUM_ENTRY).

Definition bloomfilter_state : Type := Filter * Filter * Filter.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Program Fixpoint list_of_filter (size : 'I_(S NUM_ENTRY)) (f : Filter) {measure (nat_of_ord size)} : list Z :=
  match size with
  | Ordinal O _ => nil
  | Ordinal (S size') _ =>
      list_of_filter (@Ordinal (S NUM_ENTRY) size' _) f ++
          [bool_to_Z (f (@Ordinal _ size' _))]
  end.

Program Definition NUM_ENTRY_1 : 'I_(S NUM_ENTRY) := @Ordinal _ NUM_ENTRY _.

Definition bloom0 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY_1 (fst (fst bst)).

Definition bloom1 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY_1 (snd (fst bst)).

Definition bloom2 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY_1 (snd bst).

(* Definition filter_match (st : state) (p : path) (f : Filter) : Prop :=
  exists content,
  PathMap.get p (snd st) = Some (ObjRegister (mk_register 1%nat NUM_ENTRY content)) /\
  forall i : Z, Znth i content = bool_to_Z (f i). (* out-of-bounds indexing is used *) *)

(* Definition bst_match (st : state) (bst : bloomfilter_state) : Prop :=
  let (rest, bloom2) := bst in
  let (bloom0, bloom1) := rest in
  filter_match st !["bloom0"] bloom0
    /\ filter_match st !["bloom1"] bloom1
    /\ filter_match st !["bloom2"] bloom2. *)

Definition header_encodes (hdr : Val) (rw : Z) (data : Z) : Prop :=
  hdr = ValBaseStruct [(!"myHeader", ValBaseHeader [(!"rw", ValBaseBit 8%nat rw); (!"data", ValBaseBit 16%nat data)] true)].

Section Experiment1.

Variable rw : Z.
Variable data : Z.
(* Variable hdr : Val.
Variable meta : Val.
Variable standard_metadata : Val. *)
Variable bst : bloomfilter_state.

Definition pre_arg_assertion : arg_assertion :=
  [
    ArgVal (0%Z, ["myHeader"; "rw"]) (ValBaseBit 8%nat rw);
    ArgVal (0%Z, ["myHeader"; "data"]) (ValBaseBit 16%nat data)
  ].

Definition pre_ext_assertion : ext_assertion :=
  [
    (LGlobal !["bloom0"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom0 bst)));
    (LGlobal !["bloom1"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom1 bst)));
    (LGlobal !["bloom2"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom2 bst)))
  ].

Definition pre (args : list Val) (st : state) :=
  arg_to_shallow_assertion pre_arg_assertion args /\
    ext_to_shallow_assertion this pre_ext_assertion (snd st).

Axiom CRC : Z -> 'I_NUM_ENTRY.

Definition process (rw data : Z) (bst : bloomfilter_state) : (bloomfilter_state * Z) :=
  if rw =? 2 then
    (bloomfilter.add 'I_NUM_ENTRY (fun x y => Nat.eqb x y) CRC CRC CRC bst data, 2)
  else
    (bst, bool_to_Z (bloomfilter.query 'I_NUM_ENTRY CRC CRC CRC bst data)).

Definition post_arg_assertion : arg_assertion :=
  let (bst', rw') := process rw data bst in
  [
    ArgVal (0%Z, ["myHeader"; "rw"]) (ValBaseBit 8%nat rw');
    ArgVal (0%Z, ["myHeader"; "data"]) (ValBaseBit 16%nat data)
  ].

Definition post_ext_assertion : ext_assertion :=
  let (bst', rw') := process rw data bst in
  [
    (LGlobal !["bloom0"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom0 bst')));
    (LGlobal !["bloom1"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom1 bst')));
    (LGlobal !["bloom2"], ObjRegister (mk_register 1%nat (Z.of_nat NUM_ENTRY) (bloom2 bst')))
  ].

Definition post (args : list Val) (ret : Val) (st : state) :=
  arg_to_shallow_assertion post_arg_assertion args /\
    ext_to_shallow_assertion this post_ext_assertion (snd st).

Lemma body_bloomfilter : hoare_func ge inst_m this pre MyIngress_fundef nil post.
Proof.
  apply deep_hoare_func_sound.
  eapply deep_hoare_func_internal.
(* Qed. *)
Abort.

End Experiment1.

End Experiment1.
