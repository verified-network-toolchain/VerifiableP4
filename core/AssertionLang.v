Require Import Coq.Strings.String.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import Poulet4.Value.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.SvalRefine.
Require Import Coq.Numbers.BinNums.
Require Import Hammer.Plugin.Hammer.
Open Scope type_scope.

Section AssertionLang.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := ValueLvalue.

Notation ident := (string).
Notation path := (list ident).
Notation P4Int := (P4Int.t tags_t).
Notation P4String := (P4String.t tags_t).
Notation P4Type := (@P4Type tags_t).
Notation mem := Semantics.mem.

Context `{@Target tags_t (@Expression tags_t)}.

Definition mem_unit := path * Sval.

Definition mem_assertion := list mem_unit.

Definition mem_satisfies_unit (m : mem) (a_unit : mem_unit) : Prop :=
  let (p, sv) := a_unit in
  match PathMap.get p m with
  | Some sv' => sval_refine sv sv'
  | None => False
  end.

Definition mem_satisfies (m : mem) (a : mem_assertion) : Prop :=
  fold_right and True (map (mem_satisfies_unit m) a).

Definition mem_denote (a : mem_assertion) : mem -> Prop :=
  fun m => mem_satisfies m a.

Definition arg_assertion := list Sval.

Definition arg_satisfies (args : list Sval) (a : arg_assertion) : Prop :=
  Forall2 sval_refine a args.

Definition arg_denote (a : arg_assertion) : list Sval -> Prop :=
  fun args => arg_satisfies args a.

Definition ret_assertion := Sval.

Definition ret_satisfies (retv : Val) (a : ret_assertion) : Prop :=
  (forall sv', val_to_sval retv sv' -> sval_refine a sv').

Definition ret_denote (a : ret_assertion) : Val -> Prop :=
  fun retv => ret_satisfies retv a.

Definition ext_unit := path * extern_object.

Definition ext_assertion := list ext_unit.

Definition ext_satisfies_unit (es : extern_state) (a_unit : ext_unit) : Prop :=
  let (p, eo) := a_unit in
  match PathMap.get p es with
  | Some eo' => eo = eo'
  | None => False
  end.

Definition ext_satisfies (es : extern_state) (a : ext_assertion) : Prop :=
  fold_right and True (map (ext_satisfies_unit es) a).

Definition ext_denote (a : ext_assertion) : extern_state -> Prop :=
  fun es => ext_satisfies es a.

(* A lemma to handle assertion representations. *)

Lemma fold_right_and_True : forall l,
  fold_right and True l <-> Forall id l.
Proof.
  intros; induction l; only 2 : destruct IHl; split; intros.
  - constructor.
  - constructor.
  - constructor; sfirstorder.
  - inv H2; sfirstorder.
Qed.

Lemma mem_denote_app : forall a a' m,
  mem_denote (a ++ a') m <-> mem_denote a m /\ mem_denote a' m.
Proof.
  intros.
  unfold mem_denote, mem_satisfies.
  rewrite !fold_right_and_True.
  rewrite map_app.
  rewrite Forall_app.
  reflexivity.
Qed.

Lemma ext_denote_app : forall a a' es,
  ext_denote (a ++ a') es <-> ext_denote a es /\ ext_denote a' es.
Proof.
  intros.
  unfold ext_denote, ext_satisfies.
  rewrite !fold_right_and_True.
  rewrite map_app.
  rewrite Forall_app.
  reflexivity.
Qed.

(* Assertion language properties *)

Lemma path_eqb_eq : forall (p1 p2 : path), path_eqb p1 p2 -> p1 = p2.
Proof.
  induction p1; intros.
  - destruct p2; auto. unfold path_eqb in H0. simpl in H0. now exfalso.
  - destruct p2.
    + unfold path_eqb in H0. simpl in H0. now exfalso.
    + unfold path_eqb in H0. simpl in H0. apply andb_prop in H0.
      destruct H0. apply eqb_eq in H0. subst. f_equal. apply IHp1. apply H1.
Qed.

Fixpoint alist_get' {A} (a : list (path * A)) (p : path) : option A :=
  match a with
  | (p', v) :: tl =>
      if path_eqb p p' then Some v else alist_get' tl p
  | [] => None
  end.

Lemma alist_get'_spec : forall {A} a p,
  @alist_get' A a p = AList.get a p.
Proof.
  induction a; intros.
  - auto.
  - destruct a. simpl.
    destruct (path_eqb p l) eqn:?.
    + symmetry. apply AList.get_eq_cons. auto.
      apply path_eqb_eq. auto.
    + replace (AList.get ((l, a) :: a0) p) with (AList.get a0 p). 2 : {
        symmetry. apply AList.get_neq_cons.
        intro. red in H0. subst.
        rewrite path_eqb_refl in Heqb.
        inv Heqb.
      }
      apply IHa.
Qed.

Lemma mem_denote_get : forall (a : mem_assertion) p sv,
  AList.get a p = Some sv ->
  forall m, mem_denote a m ->
  mem_satisfies_unit m (p, sv).
Proof.
  intros.
  rewrite <- alist_get'_spec in H0.
  induction a.
  - inv H0.
  - destruct a as [p' sv']. simpl in H0.
    destruct (path_eqb p p') eqn:H_p.
    + apply path_eqb_eq in H_p; subst.
      inv H0. inv H1. auto.
    + inv H1; apply IHa; auto.
Qed.

Lemma ext_denote_get : forall (a : ext_assertion) p eo,
  AList.get a p = Some eo ->
  forall es, ext_denote a es ->
  ext_satisfies_unit es (p, eo).
Proof.
  intros.
  rewrite <- alist_get'_spec in H0.
  induction a.
  - inv H0.
  - destruct a as [p' sv']. simpl in H0.
    destruct (path_eqb p p') eqn:H_p.
    + apply path_eqb_eq in H_p; subst.
      inv H0. inv H1. auto.
    + inv H1; apply IHa; auto.
Qed.

(** * Update and Get *)

(* Current behavior:
    validate a header regardless of the sucess of writing *)
Fixpoint upd_sval_once (v: Sval) (p: path) (f: Sval) : Sval :=
  match v, p with
  | _, [] => f
  | ValBaseStruct fields, hd :: tl =>
      match AList.get fields hd with
      | Some v' =>
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseStruct fields'
          | None => v (* Impossible *)
          end
      | None => v
      end
  | ValBaseUnion fields, hd :: tl =>
      match AList.get fields hd with
      | Some v' =>
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseUnion fields'
          | None => v (* Impossible *)
          end
      | None => v
      end
  | ValBaseHeader fields vbit, hd :: tl =>
      match AList.get fields hd with
      | Some v' =>
          match AList.set fields hd (upd_sval_once v' tl f) with
          | Some fields' => ValBaseHeader fields' (Some true)
          | None => v (* Impossible *)
          end
      | None => v
      end
  | _, _ => v
  end.

Definition upd_sval (v: Sval) (upds: list (path * Sval)): Sval :=
  List.fold_left (fun v pf => upd_sval_once v (fst pf) (snd pf)) upds v.

Definition gen_sval (typ: P4Type) (upds: list (path * Sval)): option Sval :=
  match uninit_sval_of_typ (Some false) typ with
  | Some v =>
      Some (List.fold_left (fun v pf => upd_sval_once v (fst pf) (snd pf)) upds v)
  | None =>
      None
  end.

End AssertionLang.
