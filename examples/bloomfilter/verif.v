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
Require Import ProD3.core.Tactics.
Require Import ProD3.core.V1ModelSpec.

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque (*IdentMap.empty IdentMap.set*) PathMap.empty PathMap.set.

(* Global environment *)
Definition ge : genv := Eval compute in gen_ge prog.

Definition instantiation := Eval compute in instantiate_prog ge prog.

(* inst_m *)
(* Definition inst_m := Eval compute in fst instantiation. *)

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

(* Notation assertion := (@assertion Info).
Notation arg_assertion := (@arg_assertion Info).
Notation ret_assertion := (@ret_assertion Info). *)
(* Notation ext_assertion := (@ext_assertion Info). *)

Axiom dummy_fundef : (@fundef Info).

Module Experiment1.

Definition MyIngress_do_forward_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["MyIngress"; "do_forward"] (ge_func ge)).

Open Scope func_spec.

Definition MyIngress_do_forward_spec : func_spec :=
  WITH (p : path),
    PATH p
    MOD (Some [["do_forward"; "port"]; ["standard_metadata"]]) []
    WITH (port : Z) (standard_metadata : Sval),
      PRE
        (ARG [ValBaseBit (to_loptbool 9%N port)]
        (MEM [(["standard_metadata"], standard_metadata)]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["standard_metadata"], (update "egress_spec" (ValBaseBit (to_loptbool 9%N port)) standard_metadata))]
        (EXT []))).

Lemma MyIngress_do_forward_body :
  fundef_satisfies_spec ge MyIngress_do_forward_fundef nil MyIngress_do_forward_spec.
Proof.
  start_function.
  step.
  step.
  entailer.
Admitted.

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

Definition Add_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Add"; "apply"] (ge_func ge)).

Definition reg_encode (l : list Z) : extern_object :=
  ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) l)).

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

Definition custom_metadata_t :=
  Eval compute in force dummy_type (IdentMap.get "custom_metadata_t" (ge_typ ge)).

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
    WITH (rw data : Z) (bf : bloomfilter_state),
      PRE
        let hdr := ValBaseStruct
        [("myHeader",
          ValBaseHeader
            [("rw", ValBaseBit (to_loptbool 8 rw));
             ("data", ValBaseBit (to_loptbool 16 data))]
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
            [("rw", ValBaseBit (to_loptbool 8 rw));
             ("data", ValBaseBit (to_loptbool 16 data))]
             (Some true))] in
        let bf' := bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf data in
        (ARG_RET [hdr; force ValBaseNull (uninit_sval_of_typ None custom_metadata_t)] ValBaseNull
        (MEM []
        (EXT [(["bloom0"], reg_encode (bloom0 bf'));
              (["bloom1"], reg_encode (bloom1 bf'));
              (["bloom2"], reg_encode (bloom2 bf'))]))).

Lemma update_bit : forall filter hash,
  reg_encode (list_of_filter NUM_ENTRY (upd Z Z.eqb filter hash true)) =
  ObjRegister
    (upd_Znth hash (map ValBaseBit (map (to_lbool 1) (list_of_filter NUM_ENTRY filter)))
       (ValBaseBit (to_lbool 1 (BitArith.mod_bound 1 1)))).
Admitted.

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
(* Qed. *)
Admitted.

Definition Query_fundef := Eval compute in
  force dummy_fundef (PathMap.get ["Query"; "apply"] (ge_func ge)).

Definition MyIngress_fundef := Eval compute in
  match PathMap.get ["MyIngress"; "apply"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Definition this : path := ["main"; "ig"].



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
         ("data", ValBaseBit (to_loptbool 16 data))]
         (Some true))].

Axiom dummy_type : (@P4Type Info).

Definition standard_metadata_t := Eval compute in
  match IdentMap.get "standard_metadata_t" (ge_typ ge) with
  | Some typ => typ
  | None => dummy_type
  end.

Axiom dummy_sval : Sval.

Variable (meta : Sval).

(* Definition meta := Eval compute in
  match gen_sval custom_metadata_t [] with
  | Some v => v
  | None => dummy_sval
  end. *)

Variable (standard_metadata : Sval).

(* Definition standard_metadata := Eval compute in
  match gen_sval standard_metadata_t [] with
  | Some v => v
  | None => dummy_sval
  end. *)

(* Definition pre_arg_assertion : assertion :=
  [ (["hdr"], myHeader);
    (["meta"], meta);
    (["standard_metadata"], standard_metadata)
  ]. *)

Definition pre_arg_assertion : arg_assertion :=
  [myHeader; meta; standard_metadata].

Definition pre_ext_assertion : ext_assertion :=
  [
    (["bloom0"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom0 bst))));
    (["bloom1"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom1 bst))));
    (["bloom2"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom2 bst))))
  ].

Definition pre :=
  ARG pre_arg_assertion (MEM [] (EXT pre_ext_assertion)).

Definition process (rw data : Z) (bst : bloomfilter_state) : (bloomfilter_state * Z) :=
  if rw =? 2 then
    (bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bst data, 2)
  else
    (bst, bool_to_Z (bloomfilter.query Z CRC_pad0 CRC_pad1 CRC_pad2 bst data)).

Definition bst' := fst (process rw data bst).
Definition rw' := snd (process rw data bst).

Definition post_arg_assertion : arg_assertion :=
  [
    upd_sval myHeader [(["myHeader"; "rw"], ValBaseBit (to_loptbool 8 rw'))];
    (* The full specification of meta requires updates to all the six fields,
       which need to be computed from process. 
       Not sure if it is a good design. 
       Or maybe we should change meta's direction to In? *)
    (upd_sval meta [(["index0"], ValBaseBit (to_loptbool 16 data))]);
    upd_sval standard_metadata [(["egress_spec"], ValBaseBit (to_loptbool 9 1))]
  ].

Definition post_ext_assertion : ext_assertion :=
  [
    (["bloom0"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom0 bst'))));
    (["bloom1"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom1 bst'))));
    (["bloom2"], ObjRegister (map ValBaseBit (map (P4Arith.to_lbool 1) (bloom2 bst'))))
  ].

Definition post :=
  ARG_RET post_arg_assertion ValBaseNull (MEM [] (EXT post_ext_assertion)).

Definition bloomfilter_spec : func_spec :=
  fs_base (mk_func_spec this (fsh_base pre post) None [["bloom0"]; ["bloom1"]; ["bloom2"]]).

Lemma body_bloomfilter : fundef_satisfies_spec ge MyIngress_fundef nil bloomfilter_spec.
Proof.
  (* remove AType and represent everything as Sval
  To make it easier for structs, add a strucuture to represent structs with updated fields
    (type soundness may be neeeded here)
  struct rec has value rec_v
  rec.x := 1
  struct rec has value (update "x" 1 rec_v)
  Return value as a special out parameter called "return"
  Make function call reusable
  Then we will need a frame rule
  Extern objects
  After generating an assertion from the symbolic executor, we need to evaluate the computational function.
    But in this procedure, we should keep the user-defined Coq expressions untouched.
  We need to face goals like
    [("x", val_to_sval (Int v)), ("y", val_to_sval (Int (v + 1)))]
    sval_add (val_to_sval (Int v)) (val_to_sval (Int 1)) = val_to_sval (Int (v + 1))
    *)
  start_function.
  step.
  eapply hoare_block_cons.
  {
    eapply hoare_stmt_if_true'.
    { (* eval_expr *)
      reflexivity.
    }
    apply hoare_stmt_block.
    {
      simpl eval_write_var.
      step_call MyIngress_do_forward_body.
      { entailer. }
      (* A possible simpl: *)
        (* Opaque pre_ext_assertion post_ext_assertion.
        simpl MEM. *)
      step_if (MEM
         (eval_write_vars []
            (filter_out [(["hdr"], InOut); (["meta"], InOut); (["standard_metadata"], InOut)])
            post_arg_assertion) (EXT post_ext_assertion)).
      { (* true branch *)
        change (is_true (BitArith.lbool_to_val (to_lbool 8%N rw) 1 0 =? 0)) in H.
        (* step_call. *)
        admit.
      }
      { (* false branch *)
        change (is_true (negb (BitArith.lbool_to_val (to_lbool 8%N rw) 1 0 =? 0))) in H.
        (* step_call. *)
        admit.
      }
      step.
      simpl. (* This simpl generates better assertion for the next step. *)
      eapply implies_refl.
    }
  }
  step.
  entailer.
Abort.

End Experiment1.

End Experiment1.

Module Experiment2.

Section Experiment2.

Definition this := ["main"; "ig"; "Query"].

Definition Query_fundef := Eval compute in
  match PathMap.get ["Query"; "apply"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Axiom dummy_stmt : (@Statement Info).

Definition assign_stmt := Eval compute in
  match Query_fundef with
  | FInternal _ (BlockCons _ (BlockCons _ (BlockCons _ (BlockCons _ (BlockCons _ (BlockCons _ (BlockCons stat _))))))) =>
    stat
  | _ => dummy_stmt
  end.

Variable hdr : Sval.
Variable meta : Sval.
Hypothesis H_member0 : Members.get "member0" meta = (ValBaseBit [Some true]).
Hypothesis H_member1 : Members.get "member1" meta = (ValBaseBit [Some true]).
Hypothesis H_member2 : Members.get "member2" meta = (ValBaseBit [Some true]).

Definition pre :=
  MEM [(["hdr"], hdr); (["meta"], meta)] (EXT []).

Axiom post : post_assertion.

Lemma body_assign : hoare_block ge this pre (BlockCons assign_stmt BlockNil) post.
Proof.
  unfold pre. unfold assign_stmt.
  step.
  simpl str. rewrite H_member0, H_member1, H_member2.
  change (build_abs_unary_op _ _)
   (* (build_abs_binary_op (Ops.eval_binary_op BitAnd)
      (build_abs_binary_op (Ops.eval_binary_op BitAnd) (ValBaseBit [Some true])
         (ValBaseBit [Some true])) (ValBaseBit [Some true]))) *) with
  (ltac: (let x := eval cbv in (build_abs_unary_op (fun oldv : Val => Ops.bit_of_val 8 oldv)
   (build_abs_binary_op (Ops.eval_binary_op BitAnd)
      (build_abs_binary_op (Ops.eval_binary_op BitAnd) (ValBaseBit [Some true])
         (ValBaseBit [Some true])) (ValBaseBit [Some true]))) in exact x)).
(* Qed. *)
Abort.

End Experiment2.

End Experiment2.
