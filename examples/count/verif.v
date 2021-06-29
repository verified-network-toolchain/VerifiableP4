Require Import Poulet4.P4defs.
Require Import Poulet4.P4Notations.
Open Scope string_scope.

Import ListNotations.
Require Import ProD3.examples.count.p4ast.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Psatz.

Require Import Poulet4.Maps.
Require Import Poulet4.Semantics.
Require Import Poulet4.SimplExpr.
Require Import Poulet4.V1Model.
Require Import Poulet4.P4Arith.
Require Import Poulet4.P4String.
Require Import Poulet4.Ops.
Require Import ProD3.core.Hoare.
(* Require Import ProD3.core.AssertionLang. *)

Instance target : @Target Info (@Expression Info) := V1Model.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

(* Global environment *)
Definition ge := Eval compute in gen_ge prog.

Definition instantiation := Eval compute in instantiate_prog ge prog.

(* inst_m *)
Definition inst_m := Eval compute in fst instantiation.

(* Initial extern state *)
Definition init_es := Eval compute in snd instantiation.

Notation ident := (P4String.t Info).
Notation path := (list ident).

Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set.

Definition this : path := [!"main"; !"ig"].
Definition init_st : state := (PathMap.empty, init_es).

(* 
new_register *)

Definition myFundef := Eval compute in
  match PathMap.get [!"MyIngress"] (ge_func ge) with
  | Some x => x
  | None => dummy_fundef
  end.

Module Experiment.

Definition v1 : @ValueBase Info := ValBaseHeader [(!"firstBit", ValBaseBit 1%nat 0)] true.
Definition v2 : @ValueBase Info := ValBaseStruct [(!"myHeader", v1)].
Definition v3 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 10)].
Definition v4 : @ValueBase Info := ValBaseStruct [(!"counter", ValBaseBit 4%nat 0)].
Definition v5 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 10)].
Definition v6 : @ValueBase Info := ValBaseStruct [(!"egress_spec", ValBaseBit 9%nat 0)].

(* 
Lemma test: (0 <= P4Arith.BitArith.mod_bound 32 0)%Z.
Proof.
  apply Zlt_succ_le.
  simpl. reflexivity.
Qed. *)

(* Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
Print init_es. *)

(* {st' signal | exec_block [] inst_mem init_st myBlock st' signal }. *)
Lemma eval_func: { st' & { signal | exec_func ge this inst_m init_st myFundef
    [] [v2; v3; v5] st' [v2; v4; v6] signal} }.
Proof.
  solve [repeat econstructor].
Defined.

Opaque IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Definition st' := Eval compute in (projT1 eval_func).
Print st'.

End Experiment.

(* Functional model *)
Notation Val := (@ValueBase Info).
Notation P4String := (P4String.t Info).


Module BitArray.
  Definition t := (list Z).

  Section Operations.
    Variable (width : positive).

    Definition incr (ast: t) (i: Z) : t :=
      upd_Znth i ast (BitArith.plus_mod width (Znth i ast) 1).

    Definition incr_sat (ast: t) (i: Z) : t :=
      upd_Znth i ast (BitArith.plus_sat width (Znth i ast) 1).

  End Operations.
End BitArray.


Definition NUM_ENTRY := 2.
Definition WIDTH : positive := 4.

Definition ast_match (st : state) (ast : BitArray.t) : Prop :=
  exists content,
  PathMap.get !["main"; "ig"; "myCounter"] (snd st) = Some (ObjRegister (mk_register 4%nat NUM_ENTRY content)) /\
  content = ast.

Definition field_contains (v : Val) (name : P4String) (data: Val) : Prop :=
  match v with
  | ValBaseStruct fields => AList.get fields name = Some data
  | ValBaseHeader fields true => AList.get fields name = Some data
  | _ => False
  end.

Definition process (width : positive) (fbit : Z) (ast : BitArray.t) : (BitArray.t * Z) :=
  if fbit =? 1 then
    (BitArray.incr width ast 1, 48)
  else
    (BitArray.incr width ast 0, 0).

Section Experiment1.
Variable fbit : Z.
Variable hdr : Val.
Variable meta : Val.
Variable standard_metadata : Val.
Variable ast : BitArray.t.

Definition pre (* (fbit : Z) (hdr meta standard_metadata : Val) *) (in_args : list Val) (st : state) :=
  in_args = [ValBaseStruct [(!"myHeader", hdr)]; meta; standard_metadata]
  /\ (exists hdr_fields, hdr = ValBaseHeader hdr_fields true)
  /\ (exists meta_fields, meta = ValBaseStruct meta_fields)
  /\ (exists std_meta_fields, standard_metadata = ValBaseStruct std_meta_fields)
  /\ field_contains hdr !"firstBit" (ValBaseBit 1%nat fbit)
  /\ (exists counter, field_contains meta !"counter" (ValBaseBit (Z.to_nat (Z.pos WIDTH)) counter))
  /\ (exists eport, field_contains standard_metadata !"egress_spec" (ValBaseBit 9%nat eport))
  /\ ast_match st ast.

Definition post (* (fbit : Z) (hdr meta standard_metadata : Val) *) (out_args : list Val) (st : state) :=
  let (ast', eport) := process WIDTH fbit ast in
  exists standard_metadata' std_meta_fields std_meta_fields' meta_fields meta_fields' meta',
  out_args = [ValBaseStruct [(!"myHeader", hdr)]; meta'; standard_metadata']
    /\ meta = ValBaseStruct meta_fields 
    /\ meta' = ValBaseStruct meta_fields'
    /\ field_contains meta' !"counter" (ValBaseBit (Z.to_nat (Z.pos WIDTH)) (Znth (if fbit =? 1 then 1 else 0) ast))
    /\ Ops.eval_binary_op_eq (ValBaseStruct (AList.filter meta_fields (P4String.equivb !"counter" )))
                             (ValBaseStruct (AList.filter meta_fields' (P4String.equivb !"counter" )))
       = Some true
    /\ standard_metadata = ValBaseStruct std_meta_fields 
    /\ standard_metadata' = ValBaseStruct std_meta_fields'
    /\ field_contains standard_metadata' !"egress_spec" (ValBaseBit 9%nat eport)
    /\ Ops.eval_binary_op_eq (ValBaseStruct (AList.filter std_meta_fields (P4String.equivb !"egress_spec" )))
                             (ValBaseStruct (AList.filter std_meta_fields' (P4String.equivb !"egress_spec" )))
       = Some true
    /\ ast_match st ast'.

(* Lemma body_counter : hoare_func ge inst_m this pre myFundef nil post.
Abort. *)

End Experiment1.


Section Experiment2.

(*Assumption argsassertion:= (in_args : list Val) (st : state)*)
Definition ArgAssertion (T:Type) := forall (t:T), arg_assertion.

Definition ArgRetAssertion (T:Type) := forall (t:T), arg_ret_assertion.

Record FunSpec := {
  WITHtype : Type;
  preCond: ArgAssertion WITHtype ;
  postCond: ArgRetAssertion WITHtype ;
}.

Definition withType3 := ((Z * (P4String.AList Info Val) * (P4String.AList Info Val) 
                           * (P4String.AList Info Val) * BitArray.t)%type).

(* As general as possible *)
Definition pre2 : ArgAssertion (Z * Val * Val * Val * BitArray.t) :=
 fun t in_args st =>
   match t with (fbit, hdr, meta, standard_metadata, ast) =>
    in_args = [ValBaseStruct [(!"myHeader", hdr)]; meta; standard_metadata]
   /\ (exists hdr_fields, hdr = ValBaseHeader hdr_fields true)
   /\ (exists meta_fields, meta = ValBaseStruct meta_fields)
   /\ (exists std_meta_fields, standard_metadata = ValBaseStruct std_meta_fields)
   /\ field_contains hdr !"firstBit" (ValBaseBit 1%nat fbit)
   /\ (exists counter, field_contains meta !"counter" (ValBaseBit (Z.to_nat (Z.pos WIDTH)) counter))
   /\ (exists eport, field_contains standard_metadata !"egress_spec" (ValBaseBit 9%nat eport))
   /\ ast_match st ast
 end.

Definition pre3 : ArgAssertion withType3 :=
 fun t in_args st =>
   match t with (fbit, hdr_fields, meta_fields, std_meta_fields, ast) =>
    in_args = [ValBaseStruct [(!"myHeader", ValBaseHeader hdr_fields true)];
               ValBaseStruct meta_fields;
               ValBaseStruct std_meta_fields]
   /\ field_contains (ValBaseHeader hdr_fields true) !"firstBit" (ValBaseBit 1%nat fbit)
   /\ (exists counter, field_contains (ValBaseStruct meta_fields) !"counter" (ValBaseBit (Z.to_nat (Z.pos WIDTH)) counter))
   /\ (exists eport, field_contains (ValBaseStruct std_meta_fields) !"egress_spec" (ValBaseBit 9%nat eport))
   /\ ast_match st ast
 end.


(* As precise as possible *)
Definition post2 : ArgRetAssertion (Z * Val * Val * Val * BitArray.t) :=
  fun t out_args retv st =>
  match t with (fbit, hdr, meta, standard_metadata, ast) =>
  let (ast', eport) := process WIDTH fbit ast in
  exists standard_metadata' std_meta_fields std_meta_fields' meta_fields meta_fields' meta',
  out_args = [ValBaseStruct [(!"myHeader", hdr)]; meta'; standard_metadata']
    /\ meta = ValBaseStruct meta_fields 
    /\ meta' = ValBaseStruct meta_fields'
    /\ field_contains meta' !"counter" (ValBaseBit (Z.to_nat (Z.pos WIDTH)) (Znth (if fbit =? 1 then 1 else 0) ast))
    /\ (AList.filter meta_fields (P4String.nequivb !"counter" )) = 
       (AList.filter meta_fields' (P4String.nequivb !"counter" ))
    /\ standard_metadata = ValBaseStruct std_meta_fields 
    /\ standard_metadata' = ValBaseStruct std_meta_fields'
    /\ field_contains standard_metadata' !"egress_spec" (ValBaseBit 9%nat eport)
    /\ (AList.filter std_meta_fields (P4String.nequivb !"egress_spec" )) =
       (AList.filter std_meta_fields' (P4String.nequivb !"egress_spec" ))
    /\ ast_match st ast'
    /\ retv = ValBaseNull
  end.


Definition post3_prop meta_fields meta_fields' std_meta_fields std_meta_fields' counter_val eport_val ret_val:=
  field_contains (ValBaseStruct meta_fields') !"counter" counter_val
  /\ (AList.filter meta_fields (P4String.nequivb !"counter" )) = 
     (AList.filter meta_fields' (P4String.nequivb !"counter" ))
  /\ field_contains (ValBaseStruct std_meta_fields') !"egress_spec" (ValBaseBit 9%nat eport_val)
  /\ (AList.filter std_meta_fields (P4String.nequivb !"egress_spec" )) =
     (AList.filter std_meta_fields' (P4String.nequivb !"egress_spec" ))
  /\ ret_val = @ValBaseNull Info.

(* As precise as possible *)
Definition post3 : ArgRetAssertion withType3 :=
  fun t out_args retv st =>
  match t with (fbit, hdr_fields, meta_fields, std_meta_fields, ast) =>
  let (ast', eport) := process WIDTH fbit ast in
  exists std_meta_fields' meta_fields',
  out_args = [ValBaseStruct [(!"myHeader", ValBaseHeader hdr_fields true)];
              ValBaseStruct meta_fields';
              ValBaseStruct std_meta_fields']
    /\ post3_prop meta_fields meta_fields' std_meta_fields std_meta_fields' 
              (ValBaseBit (Z.to_nat (Z.pos WIDTH)) (Znth (if fbit =? 1 then 1 else 0) ast))
              eport retv
    /\ ast_match st ast'
  end.

Definition countFunspec : FunSpec := {| WITHtype := withType3;
                                       preCond := pre3;
                                       postCond := post3 |}.

Definition statement := Eval compute in
  match myFundef with
  | FInternal vals init (BlockCons stmt' rest') => stmt'
  | _ => empty_statement
  end.

Ltac inv H := inversion H; subst; clear H.
Transparent IdentMap.empty IdentMap.set PathMap.empty PathMap.set PathMap.sets.
Set Printing Notations.

Require Import Coq.Classes.Morphisms.

Lemma nequivb_proper: forall p4str, Morphisms.Proper (Morphisms.respectful (@P4String.equiv Info) eq) (nequivb p4str).
Proof.
  repeat intro. unfold nequivb. unfold equiv in H. rewrite H. now simpl.
Qed.

Lemma body_counter : forall t : WITHtype countFunspec,
     hoare_func ge inst_m this (preCond countFunspec t) myFundef nil (postCond countFunspec t).
Proof.
  intros t.
  unfold countFunspec in t.
  simpl in t.
  destruct t as [[[[fbit hdr_fields] meta_fields] std_meta_fields] ast].
  simpl.
  unfold pre3.
  unfold hoare_func.
  intros.
  destruct st, st'.
  (* +[H16] exec_func on ingress.apply() *)
  inv H0.
  destruct H as [A [B [[counter C] [[eport D] [content [E F]]]]]].
  unfold default, Inhabitant_Info in *.
  (* Opaque Ops.eval_binary_op_eq. *)
  simpl in *.
  rewrite A in H4.
  inv H4. inv H5. inv H6. 
  (* +[H7] exec_block*)
  inv H10. inv H4. inv H11. inv H9. inv H8.
  inv H9. inv H8. inv H14. inv H0.
  inv H11. inv H4.
  rewrite B in H.
  inv H. inv H10. inv H8. inv H9. inv H11.
  inversion H13. clear H13.
  destruct b.
  (* true: forward packets *)
  - inv H12. 
    (* +[H10] exec_block *)
    inv H9. inv H5.
    (* +[H18] exec_call on do_forward() *)
    inv H12. inv H14. inv H9. inv H3.
    inv H12. inv H13. inv H14.
    inv H11. inv H15. 
    (* +[H20] exec_func on do_forward() *)
    inv H17. inv H3. inv H4. inv H5. 
    (* +[H9] exec_block *)
    inv H11. inv H5.
    (* +[H21] exec_call on register.read() *)
    inv H13. inv H15. 
    inv H11. inv H3. inv H14. inv H15.
    inv H12. inv H11. inv H3.
    inv H12. inv H14. inv H15.
    inv H13. inv H17. inv H19.
    inv H14. inv H.
    rewrite E in H2. inv H2. clear H4.
    (* -[H21] *)
    inv H21. inv H8. inv H3. inv H5. inv H6.
    inv H12. apply AList.get_some_set with 
              (v2:=(ValBaseBit 4 (Znth (BitArith.mod_bound 32 1) ast))) in C.
    rewrite C in H1. inv H1.
    inv H13. inv H11.
    (* -[H9] *)
    (* +[H11]: exec_block *)
    simpl in *. inv H9. inv H5.
    (* +[H21]: exec_call on register.write() *)
    inv H13. inv H15. inv H9. inv H3.
    inv H13. inv H14. inv H15. inv H12.
    inv H9. inv H3. inv H14. inv H9.
    inv H14. inv H12. rewrite AList.set_some_get in H1.
    inv H1. inv H15. inv H9. inv H12. inv H14. inv H22.
    inv H13. inv H17. inv H19. inv H14.
    inv H. rewrite E in H4. inv H4. clear H8. clear H9.
    (* -[H21] *)
    inv H21.
    (* -[H11] *)
    (* +[H9]: exec_block *)
    inv H11. inv H5.
    2: inv H11.
    inv H13. inv H11. inv H14. inv H12.
    inv H13. inv H15. inv H11. inv H4.
    inv H6. inv H8. apply AList.get_some_set with 
                  (v2:=(ValBaseBit 9 (BitArith.mod_bound 9 48))) in D.
    rewrite D in H1. inv H1.
    (* -[H9] *)
    inv H9.
    (* -[H20] *)
    inv H20.
    (* -[H18] *)
    inv H18.
    (* -[H10] *)
    inv H10.
    (* -[H7] *)
    inv H7. 
    (* -[H16] *)
    inv H16. clear dirs. clear dirs0. clear dirs1.
    simpl.
    unfold process.
    apply Z.eqb_eq in H0.
    subst. simpl. do 2 eexists.
    split. f_equal.
    split. unfold post3_prop.
    split. apply AList.set_some_get.
    split. symmetry. apply AList.filter_set_some_false. apply nequivb_proper.
    reflexivity. 
    split. apply AList.set_some_get.
    split. symmetry. apply AList.filter_set_some_false. apply nequivb_proper.
    reflexivity.
    reflexivity.
    unfold ast_match.
    eexists. simpl.
    split. 2: reflexivity.
    unfold PathMap.get, PathMap.set, FuncAsMap.get, FuncAsMap.set.
    simpl. unfold BitArray.incr. reflexivity.
  - inv H12. 
    (* +[H10] exec_block *)
    inv H9. inv H5.
    (* +[H18] exec_call on do_forward() *)
    inv H12. inv H14. inv H15. 
    (* +[H20] exec_func on do_forward() *)
    inv H17. inv H3. inv H4. inv H5. 
    (* +[H9] exec_block *)
    inv H11. inv H5.
    (* +[H21] exec_call on register.read() *)
    inv H13. inv H15. 
    inv H11. inv H3. inv H14. inv H15.
    inv H12. inv H11. inv H3.
    inv H12. inv H14. inv H15.
    inv H13. inv H17. inv H19.
    inv H14. inv H.
    rewrite E in H2. inv H2. clear H4.
    (* -[H21] *)
    inv H21. inv H8. inv H3. inv H5. inv H6.
    inv H12. apply AList.get_some_set with 
              (v2:=(ValBaseBit 4 (Znth (BitArith.mod_bound 32 0) ast))) in C.
    rewrite C in H1. inv H1.
    inv H13. inv H11.
    (* -[H9] *)
    (* +[H11]: exec_block *)
    simpl in *. inv H9. inv H5.
    (* +[H21]: exec_call on register.write() *)
    inv H13. inv H15. inv H9. inv H3.
    inv H13. inv H14. inv H15. inv H12.
    inv H9. inv H3. inv H14. inv H9.
    inv H14. inv H12. rewrite AList.set_some_get in H1.
    inv H1. inv H15. inv H9. inv H12. inv H14. inv H22.
    inv H13. inv H17. inv H19. inv H14.
    inv H. rewrite E in H4. inv H4. clear H8. clear H9.
    (* -[H21] *)
    inv H21.
    (* -[H11] *)
    (* +[H9]: exec_block *)
    inv H11. inv H5.
    2: inv H11.
    inv H13. inv H11. inv H12. inv H17.
    inv H14. inv H12. inv H13.
    inv H15. inv H4. inv H6.
    inv H8.
    apply AList.get_some_set with 
          (v2:=(ValBaseBit 9 (BitArith.mod_bound 9 0))) in D.
    rewrite D in H1. inv H1. inv H11.
    (* -[H9] *)
    inv H9.
    (* -[H20] *)
    inv H20.
    (* -[H18] *)
    inv H18.
    (* -[H10] *)
    inv H10.
    (* -[H7] *)
    inv H7. 
    (* -[H16] *)
    inv H16. clear dirs. clear dirs0. clear dirs1.
    simpl.
    unfold process.
    assert (BitArith.mod_bound 1 1 = 1). { reflexivity. }
    rewrite H in H0.
    rewrite H0. do 2 eexists.
    split. f_equal.
    split. unfold post3_prop.
    split. apply AList.set_some_get.
    split. symmetry. apply AList.filter_set_some_false. apply nequivb_proper.
    reflexivity. 
    split. apply AList.set_some_get.
    split. symmetry. apply AList.filter_set_some_false. apply nequivb_proper.
    reflexivity.
    reflexivity.
    unfold ast_match.
    eexists. simpl.
    split. 2: reflexivity.
    unfold PathMap.get, PathMap.set, FuncAsMap.get, FuncAsMap.set.
    simpl. unfold BitArray.incr. reflexivity.
Qed.

End Experiment2.

