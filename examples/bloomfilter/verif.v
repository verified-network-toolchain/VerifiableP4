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
  WITH (p : path) (port : Z) (standard_metadata : Sval),
    mk_func_spec
      p
      (ARG [ValBaseBit (to_loptbool 9%N port)]
      (MEM [(["standard_metadata"], standard_metadata)]
      (EXT [])))
      (ARG_RET [] ValBaseNull
      (MEM [(["standard_metadata"], (update "egress_spec" (ValBaseBit (to_loptbool 9%N port)) standard_metadata))]
      (EXT [])))
      (Some [["do_forward"; "port"]; ["standard_metadata"]]) [].

Lemma MyIngress_do_forward_body :
  fundef_satisfies_spec ge MyIngress_do_forward_fundef nil MyIngress_do_forward_spec.
  start_function.
  forward.
  forward.
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
  intros.
(* This lemma needs property about CRC. *)
Admitted.

End CRC.

Definition CRC_Z (data : list bool) : Z :=
  BitArith.lbool_to_val (CRC data) 1 0.

Axiom CRC_range : forall data, 0 <= CRC_Z data < NUM_ENTRY.

Definition CRC_pad (pad : list bool) (data : Z) : Z :=
  CRC_Z (((to_lbool 16%N data) ++ pad)).

Definition CRC_pad0 := CRC_pad (to_lbool 3%N 3).
Definition CRC_pad1 := CRC_pad (to_lbool 5%N 5).
Definition CRC_pad2 := CRC_pad (to_lbool 7%N 7).

Definition hash_fundef :=
  force dummy_fundef (PathMap.get ["hash"] (ge_func ge)).

(* (* fake function spec *)
Definition hash_spec : func_spec :=
  WITH (data : Z) (algo base fake_data max : Sval),
    mk_func_spec
      []
      (ARG [algo; base; fake_data; max]
      (MEM []
      (EXT [])))
      (ARG_RET [ValBaseBit (to_loptbool 16%N (CRC_Z data))] ValBaseNull
      (MEM []
      (EXT [])))
      None [].

Axiom hash_body : forall targs,
  fundef_satisfies_spec ge hash_fundef targs hash_spec. *)


Definition Add_spec : func_spec :=
  WITH p (rw data : Z) (meta : Sval) (bf : bloomfilter_state),
    let hdr := ValBaseStruct
      [("myHeader",
        ValBaseHeader
          [("rw", ValBaseBit (to_loptbool 8 rw));
           ("data", ValBaseBit (to_loptbool 16 data))]
           (Some true))] in
    mk_func_spec
      p
      (ARG [hdr; meta]
      (MEM []
      (EXT [(["bloom0"], reg_encode (bloom0 bf));
            (["bloom1"], reg_encode (bloom1 bf));
            (["bloom2"], reg_encode (bloom2 bf))])))
      (ARG_RET [hdr; havoc None meta] ValBaseNull
      (MEM []
      (EXT (let bf' := bloomfilter.add Z Z.eqb CRC_pad0 CRC_pad1 CRC_pad2 bf data in
           [(["bloom0"], reg_encode (bloom0 bf'));
            (["bloom1"], reg_encode (bloom1 bf'));
            (["bloom2"], reg_encode (bloom2 bf'))]))))
      None [["bloom0"]; ["bloom1"]; ["bloom2"]].

Lemma Add_body : fundef_satisfies_spec ge Add_fundef nil Add_spec.
Proof.
  start_function.
  (* forward_call hash_body.
  entailer.
  instantiate (1 := data).
  forward_call hash_body.
  entailer.
  instantiate (1 := data).
  forward_call hash_body.
  entailer.
  instantiate (1 := data).
  simpl MEM.
  forward_call uconstr:(register_write_body _ _ _ _ _).
  2 : {
    entailer.
    rewrite get_update_diff.
    2 : admit.
    2 : discriminate.
    rewrite get_update_diff.
    2 : admit.
    2 : discriminate.
    rewrite get_update_same.
    2 : admit.
    eapply SvalRefine.sval_refine_refl.
     }
  Unshelve. all : shelve_unifiable.
  3 : reflexivity.
  admit. *)

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
  fs_base (mk_func_spec this pre post None [["bloom0"]; ["bloom1"]; ["bloom2"]]).

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
  forward.
  eapply hoare_block_cons.
  {
    eapply hoare_stmt_if_true'.
    { (* eval_expr *)
      reflexivity.
    }
    apply hoare_stmt_block.
    {
      simpl eval_write_var.
      forward_call MyIngress_do_forward_body.
      { entailer. }
      (* A possible simpl: *)
        (* Opaque pre_ext_assertion post_ext_assertion.
        simpl MEM. *)
      forward_if (MEM
         (eval_write_vars []
            (filter_out [(["hdr"], InOut); (["meta"], InOut); (["standard_metadata"], InOut)])
            post_arg_assertion) (EXT post_ext_assertion)).
      { (* true branch *)
        change (is_true (BitArith.lbool_to_val (to_lbool 8%N rw) 1 0 =? 0)) in H.
        (* forward_call. *)
        admit.
      }
      { (* false branch *)
        change (is_true (negb (BitArith.lbool_to_val (to_lbool 8%N rw) 1 0 =? 0))) in H.
        (* forward_call. *)
        admit.
      }
      forward.
      simpl. (* This simpl generates better assertion for the next step. *)
      eapply implies_refl.
    }
  }
  forward.
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
  forward.
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
