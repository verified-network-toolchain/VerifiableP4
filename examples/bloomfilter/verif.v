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
(* Require Import ProD3.core.HoareSoundness. *)
Require Import ProD3.core.AssertionLang.
(* Require Import ProD3.core.V1ModelLang. *)
(* Require Import ProD3.core.ConcreteHoare. *)

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque (*IdentMap.empty IdentMap.set*) PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := Eval compute in gen_ge prog.

Definition instantiation := Eval compute in instantiate_prog ge prog.

(* inst_m *)
Definition inst_m := Eval compute in fst instantiation.

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Notation path := (list string).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

(* Notation assertion := (@assertion Info).
Notation arg_assertion := (@arg_assertion Info).
Notation ret_assertion := (@ret_assertion Info). *)
(* Notation ext_assertion := (@ext_assertion Info). *)

Module Experiment1.

Axiom dummy_fundef : (@fundef Info).

Definition MyIngress_fundef := Eval compute in
  match PathMap.get ["MyIngress"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

(* Definition header_type := Eval compute in
  match main with
  | DeclInstantiation _ _ 
      (_::_::(MkExpression _ _ (TypControl (MkControlType _ 
        [MkParameter _ _ htyp _ _; _; _])) _)::_) _ _ =>
          htyp
  | _ =>  dummy_type
  end.

Definition meta_type := Eval compute in
  match main with
  | DeclInstantiation _ _ 
      (_::_::(MkExpression _ _ (TypControl (MkControlType _ 
        [_; MkParameter _ _ mtyp _ _; _])) _)::_) _ _ =>
          mtyp
  | _ =>  dummy_type
  end.

Definition stdmeta_type := Eval compute in
  match main with
  | DeclInstantiation _ _ 
      (_::_::(MkExpression _ _ (TypControl (MkControlType _ 
        [_; _; MkParameter _ _ smtyp _ _])) _)::_) _ _ =>
          smtyp
  | _ =>  dummy_type
  end. *)

Definition this : path := ["main"; "ig"].

Definition NUM_ENTRY : Z := 1024.

Notation Filter := (Filter Z).

Definition bloomfilter_state : Type := Filter * Filter * Filter.

Definition bool_to_Z (b : bool) :=
  if b then 1 else 0.

Definition list_of_filter (size : Z) (f : Filter) : list Z :=
  map (compose bool_to_Z (compose f Z.of_nat)) (seq O (Z.to_nat size)).

Definition bloom0 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (fst (fst bst)).

Definition bloom1 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (snd (fst bst)).

Definition bloom2 (bst : bloomfilter_state) : list Z :=
  list_of_filter NUM_ENTRY (snd bst).

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

(* Definition header_encodes (hdr : Val) (rw : Z) (data : Z) : Prop :=
  hdr = ValBaseStruct [(!"myHeader", ValBaseHeader [(!"rw", ValBaseBit 8%nat rw); (!"data", ValBaseBit 16%nat data)] true)]. *)

Section Experiment1.

Variable rw : Z.
Variable data : Z.
(* Variable hdr : Val.
Variable meta : Val.
Variable standard_metadata : Val. *)
Variable bst : bloomfilter_state.

Definition myHeader := 
  ValBaseStruct
    [("myHeader",
      ValBaseHeader
        [("rw", ValBaseBit (to_loptbool 8 rw));
         ("data", ValBaseBit (to_loptbool 8 data))]
         (Some true))].

Axiom dummy_type : (@P4Type Info).

Definition custom_metadata_t := Eval compute in
  match IdentMap.get "custom_metadata_t" (ge_typ ge) with
  | Some typ => typ
  | None => dummy_type
  end.

Definition standard_metadata_t := Eval compute in
  match IdentMap.get "standard_metadata_t" (ge_typ ge) with
  | Some typ => typ
  | None => dummy_type
  end.

Axiom dummy_sval : Sval.

Definition meta := Eval compute in
  match gen_sval custom_metadata_t [] with
  | Some v => v
  | None => dummy_sval
  end.

Definition standard_metadata := Eval compute in
  match gen_sval standard_metadata_t [] with
  | Some v => v
  | None => dummy_sval
  end.

Definition pre_arg_assertion : assertion :=
  [ (["hdr"], myHeader);
    (["meta"], meta);
    (["standard_metadata"], standard_metadata)
  ].

(* Definition pre_ext_assertion : ext_assertion :=
  [
    (LGlobal !["bloom0"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom0 bst)));
    (LGlobal !["bloom1"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom1 bst)));
    (LGlobal !["bloom2"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom2 bst)))
  ].

Definition pre (args : list Val) (st : state) :=
  arg_to_shallow_assertion pre_arg_assertion args /\
    to_shallow_assertion_continue this ([], pre_ext_assertion) st. *)

Axiom CRC : Z -> Z.
Axiom CRC_range : forall data, 0 <= CRC data < NUM_ENTRY.

Definition process (rw data : Z) (bst : bloomfilter_state) : (bloomfilter_state * Z) :=
  if rw =? 2 then
    (bloomfilter.add Z Z.eqb CRC CRC CRC bst data, 2)
  else
    (bst, bool_to_Z (bloomfilter.query Z CRC CRC CRC bst data)).

Definition post_arg_assertion : assertion :=
  let (bst', rw') := process rw data bst in
  [
    (["hdr"], upd_sval myHeader [(["myHeader"; "rw"], ValBaseBit (to_loptbool 8 rw'))]); 
    (* The full specification of meta requires updates to all the six fields,
       which need to be computed from process. 
       Not sure if it is a good design. 
       Or maybe we should change meta's direction to In? *)
    (* (["meta"], upd_sval meta [(["index0"], ValBaseBit (to_loptbool 16 data))]); *)
    (["standard_metadata"], upd_sval standard_metadata [(["egress_spec"], ValBaseBit (to_loptbool 9 1))])
  ].

(* Definition post_ext_assertion : ext_assertion :=
  let (bst', rw') := process rw data bst in
  [
    (LGlobal !["bloom0"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom0 bst')));
    (LGlobal !["bloom1"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom1 bst')));
    (LGlobal !["bloom2"], ObjRegister (mk_register 1%nat NUM_ENTRY (bloom2 bst')))
  ].

Definition post (args : list Val) (ret : Val) (st : state) :=
  arg_to_shallow_assertion post_arg_assertion args /\
    to_shallow_assertion_continue this ([], post_ext_assertion) st. *)

Lemma body_bloomfilter : hoare_func ge inst_m this pre MyIngress_fundef nil post.
Proof.
  apply deep_hoare_func_sound.
  eapply deep_hoare_func_internal.
  { (* copy_in *)
    eapply hoare_copy_in_sound with (pre := (_, (_, _))).
    repeat constructor.
  }
  { (* init block *)
    simpl eval_copy_in.
    constructor. apply implies_sound, implies_refl.
  }
  {
    eapply deep_hoare_block_cons.
    eapply deep_hoare_stmt_if_true.
    { (* hdr.myHeader.isValid() == true *)
      admit.
    }
    eapply deep_hoare_stmt_block.
    eapply deep_hoare_block_cons with (mid := Hoare.mk_post_assertion _ _).
    eapply deep_hoare_stmt_method_call.
    eapply deep_hoare_call_sound.
    eapply deep_hoare_call_func.
    { (* deep_hoare_outargs *)
      eapply hoare_outargs_sound.
      repeat constructor.
    }
    { (* deep_hoare_inargs *)
      eapply hoare_inargs_sound.
      repeat constructor.
    }
    { (* lookup_func *)
      constructor.
    }
    { (* deep_hoare_func *)
      eapply deep_hoare_func_internal (* with
        (post := to_shallow_arg_ret_assertion this ([], [], ([
          AVal (LInstance !["hdr"], ["myHeader"; "rw"]) (ValBaseBit 8 rw);
          AVal (LInstance !["hdr"], ["myHeader"; "data"]) (ValBaseBit 16 data);
          AVal (LInstance !["standard_metadata"], ["egress_spec"]) (ValBaseBit 9 (P4Arith.BitArith.mod_bound 9 1));
          AType (LInstance !["hdr"], []) (TypTypeName (BareName !"headers"));
          AType (LInstance !["meta"], []) (TypTypeName (BareName !"custom_metadata_t"));
          AType (LInstance !["standard_metadata"], []) (TypTypeName (BareName !"standard_metadata_t"))]
          ,
          pre_ext_assertion))) *).
      { (* copy_in *)
        eapply hoare_copy_in_sound.
        repeat constructor.
      }
      { (* init block *)
        simpl eval_copy_in.
        constructor. apply implies_sound, implies_refl.
      }
      { (* body block *)
        eapply deep_hoare_block_cons with (mid := Hoare.mk_post_assertion _ _).
        eapply hoare_stmt_sound with (post := mk_post_assertion _ _).
        { (* wellformed *)
          constructor.
        }
        eapply hoare_stmt_assignment.
        { (* hoare_lexpr *)
          constructor.
        }
        { (* hoare_expr *)
          constructor.
        }
        { (* hoare_write *)
          constructor.
          { (* is_writable_lval *)
            admit. (* from type *)
          }
          constructor.
        }
        eapply deep_hoare_block_nil.
        eapply Hoare.implies_trans.
        {
          eapply hoare_copy_out_sound.
          repeat constructor.
        }
        apply Hoare.implies_refl.
      }
    }
    { (* deep_hoare_write_copy_out *)
      simpl fst. simpl snd.
      eapply hoare_write_copy_out_sound.
      repeat constructor.
    }
    { (* ret_assertion_to_assertion *)
      simpl fold_left.
      eapply ret_assertion_to_assertion_sound.
      constructor.
    }
    {
(* Qed. *)
Abort.

End Experiment1.

End Experiment1.
