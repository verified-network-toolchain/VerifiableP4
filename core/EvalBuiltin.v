Require Import Coq.Strings.String.
Require Import Poulet4.Utils.
Require Import Poulet4.Typed.
Require Import Poulet4.Syntax.
Require Import Poulet4.Semantics.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Members.
Require Import ProD3.core.SvalRefine.
Require Import ProD3.core.AssertionLang.
Require Import ProD3.core.AssertionNotations.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.EvalExpr.
Require Import Coq.ZArith.BinInt.
Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer.

Local Open Scope string_scope.

Section EvalBuiltin.

Context {tags_t: Type} {tags_t_inhabitant : Inhabitant tags_t}.
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Lval := (@ValueLvalue tags_t).

Notation ident := string.

Context {target : @Target tags_t (@Expression tags_t)}.

Definition header_isValid (sv : Sval) : option bool :=
  match sv with
  | ValBaseHeader _ is_valid => is_valid
  | _ => None
  end.

Definition isValid (sv : Sval) : option bool :=
  match sv with
  | ValBaseHeader _ is_valid => is_valid
  | ValBaseUnion fields =>
      match lift_option (map header_isValid (map snd fields)) with
      | Some valid_bits => Some (fold_left orb valid_bits false)
      | None => None
      end
  | _ => None
  end.

Lemma header_isValid_sound : forall sv sv' b,
  sval_refine sv sv' ->
  exec_isValid read_ndetbit sv b ->
  bit_refine (header_isValid sv) (Some b).
Proof.
  intros.
  inv H0.
  - inv H; inv H3; inv H1; constructor.
  - constructor.
Qed.

Lemma lift_option_some_inv : forall {A : Type} (ol : list (option A)) (al : list A),
  lift_option ol = Some al ->
  ol = map Some al.
Proof.
  induction ol; intros; inv H.
  - auto.
  - destruct a. 2 : inv H1.
    destruct (lift_option ol). 2 : inv H1.
    inv H1. erewrite IHol by eauto. auto.
Qed.

Lemma Forall2_map : forall {A B C D : Type} (R : A -> B -> Prop) (f : C -> A) (g : D -> B) cl dl,
  Forall2 (fun c d => R (f c) (g d)) cl dl <-> Forall2 R (map f cl) (map g dl).
Proof.
  intros.
  change (fun (c : C) (d : D) => _) with (fun c d => (fun a d => R a (g d)) (f c) d).
  rewrite Forall2_map_l, Forall2_map_r.
  reflexivity.
Qed.

Lemma Forall2_bit_refine_Some_inv : forall al bl,
  Forall2 bit_refine (map Some al) (map Some bl) ->
  al = bl.
Proof.
  induction al; intros.
  - destruct bl; inv H; auto.
  - destruct bl; inv H; inv H3; f_equal; auto.
Qed.

Lemma isValid_sound : forall sv sv' b,
  sval_refine sv sv' ->
  exec_isValid read_ndetbit sv' b ->
  bit_refine (isValid sv) (Some b).
Proof.
  intros.
  inv H0.
  - inv H; inv H4; inv H1; constructor.
  - simpl.
    inv H.
      clear H3.
      assert (Forall2 sval_refine (map snd kvs) (map snd fields)) as H3. { admit. (* use list_solve *) }
    (* use list_solve *)
    admit.
    (* destruct (lift_option (map header_isValid (map snd fields))) eqn:H_lift_option. 2 : constructor.
    apply lift_option_some_inv in H_lift_option.
    eapply Forall2_impl with (Q := (fun sv b => bit_refine (header_isValid sv) (Some b))) in H0.
     2 : {
      apply ListUtil.Forall2_duh.
      - apply header_isValid_sound.
      - eapply Forall2_length, H0.
    }
    rewrite Forall2_map in H0.
    rewrite H_lift_option in H0.
    apply Forall2_bit_refine_Some_inv in H0.
    subst; constructor. *)
Admitted.

Definition setValid (sv : Sval) : Sval :=
  match sv with
  | ValBaseHeader fields _ =>
      ValBaseHeader fields (Some true)
  | _ => sv
  end.

Definition setInvalid (sv : Sval) : Sval :=
  match sv with
  | ValBaseHeader fields _ =>
      ValBaseHeader fields (Some false)
  | _ => sv
  end.

Definition push_front (sv : Sval) (count : Z) : Sval :=
  match sv with
  | ValBaseStack headers next =>
      push_front headers next count
  | _ => sv
  end.

Lemma push_front_sound : forall sv headers next count,
  sval_refine sv (ValBaseStack headers next) ->
  sval_refine (push_front sv count) (Semantics.push_front headers next count).
Proof.
  (* use list_solve *)
Admitted.

Definition pop_front (sv : Sval) (count : Z) : Sval :=
  match sv with
  | ValBaseStack headers next =>
      pop_front headers next count
  | _ => sv
  end.

Lemma pop_front_sound : forall sv headers next count,
  sval_refine sv (ValBaseStack headers next) ->
  sval_refine (pop_front sv count) (Semantics.pop_front headers next count).
Proof.
  (* use list_solve *)
Admitted.

Definition eval_builtin (a : mem_assertion) (lv : Lval) (fname : ident) (args : list Sval) : option (mem_assertion * Sval) :=
  if fname =? "isValid" then
    match eval_read a lv with
    | Some hdr =>
        Some (a, ValBaseBool (isValid hdr))
    | None => None
    end
  else if fname =? "setValid" then
    match eval_read a lv with
    | Some hdr =>
        match eval_write a lv (setValid hdr) with
        | Some a' => Some (a', ValBaseNull)
        | None => None
        end
    | None => None
    end
  else if fname =? "setInvalid" then
    match eval_read a lv with
    | Some hdr =>
        match eval_write a lv (setInvalid hdr) with
        | Some a' => Some (a', ValBaseNull)
        | None => None
        end
    | None => None
    end
  else if fname =? "push_front" then
    match args with
    | [ValBaseInteger count] =>
      match eval_read a lv with
      | Some hdr =>
          match eval_write a lv (push_front hdr count) with
          | Some a' => Some (a', ValBaseNull)
          | None => None
          end
      | None => None
      end
    | _ => None
    end
  else if fname =? "pop_front" then
    match args with
    | [ValBaseInteger count] =>
      match eval_read a lv with
      | Some hdr =>
          match eval_write a lv (pop_front hdr count) with
          | Some a' => Some (a', ValBaseNull)
          | None => None
          end
      | None => None
      end
    | _ => None
    end
  else
    None.

Lemma eval_builtin_sound : forall ge p a_mem a_ext lv fname args a_mem' retv,
  NoDup (map fst a_mem) ->
  eval_builtin a_mem lv fname args = Some (a_mem', retv) ->
  hoare_builtin ge p (ARG args (MEM a_mem (EXT a_ext))) lv fname (RET retv (MEM a_mem' (EXT a_ext))).
Proof.
  unfold hoare_builtin; intros * H_NoDup; intros.
  inv H1.
  - unfold eval_builtin in H. simpl in H.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H0) H2).
    pose proof (isValid_sound _ _ _ H_eval_read H3).
    inv H.
    split. 2 : apply H0.
    intros.
    inv H. constructor. inv H5. auto.
  - unfold eval_builtin in H. simpl in H.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H0) H2).
    destruct (eval_write a_mem lv (setValid v)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    assert (sval_refine (setValid v) (ValBaseHeader fields (Some true))). {
      inv H_eval_read.
      constructor; [constructor | auto].
    }
    specialize (H_eval_write _ _ _ ltac:(apply H0) ltac:(eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intros. inv H. constructor.
  - unfold eval_builtin in H. simpl in H.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H0) H2).
    destruct (eval_write a_mem lv (setInvalid v)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    assert (sval_refine (setInvalid v) (ValBaseHeader fields (Some false))). {
      inv H_eval_read.
      constructor; [constructor | auto].
    }
    specialize (H_eval_write _ _ _ ltac:(apply H0) ltac:(eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intros. inv H. constructor.
  - unfold eval_builtin in H. simpl in H.
    destruct H0. inv H0; inv H7; inv H8.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H1) H2).
    destruct (eval_write a_mem lv (push_front v count)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    specialize (H_eval_write _ _ _ ltac:(apply H1) ltac:(eapply push_front_sound; eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intros. inv H. constructor.
  - unfold eval_builtin in H. simpl in H.
    destruct H0. inv H0; inv H7; inv H8.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H1) H2).
    destruct (eval_write a_mem lv (pop_front v count)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    specialize (H_eval_write _ _ _ ltac:(apply H1) ltac:(eapply pop_front_sound; eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intros. inv H. constructor.
Qed.

End EvalBuiltin.
