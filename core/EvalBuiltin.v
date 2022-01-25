Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import VST.zlist.Zlist.
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
  exec_isValid read_ndetbit sv' b ->
  bit_refine (header_isValid sv) (Some b).
Proof.
  intros.
  inv H0.
  - inv H; inv H4; inv H1; constructor.
  - inv H. constructor.
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
  rewrite ForallMap.Forall2_map_l, ForallMap.Forall2_map_r.
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

Global Instance Inhabitant_string : Inhabitant string := "".

Lemma Forall2_forall_range2 : forall {A B : Type} {da : Inhabitant A} {db : Inhabitant B} al bl (P : A -> B -> Prop),
  Forall2 P al bl <->
    (Zlength al = Zlength bl /\ forall_range2 0 (Zlength al) 0 al bl P).
Proof.
  intros; split; intro.
  - induction H.
    + unfold forall_range2, forall_i. list_solve.
    + unfold forall_range2, forall_i. destruct IHForall2. list_solve.
  - generalize dependent bl; induction al; intros.
    + assert (bl = []) by list_solve; subst.
      constructor.
    + destruct bl. 1 : list_solve.
      constructor. {
        destruct (H).
        specialize (H1 0%Z ltac:(list_solve)).
        list_solve.
      }
      apply IHal. unfold forall_range2, forall_i. destruct H. list_solve.
Qed.

Hint Rewrite @Forall2_forall_range2 : list_prop_rewrite.

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
    assert (Forall2 sval_refine (map snd kvs) (map snd fields)) as H3'. {
      unfold AList.all_values in H3.
      range_form. destruct H1. destruct H3.
      list_simplify.
      intro; intros.
      list_simplify.
      clear -H13.
      hauto use: Z.add_0_r unfold: sval_refine.
    }
    clear H3. rename H3' into H3.
    assert (Forall2 bit_refine (map header_isValid (map snd kvs)) (map Some valid_bits)). {
      range_form.
      list_simplify.
      intro; intros.
      destruct H1; destruct H3; list_simplify.
      rewrite Z.add_0_r in H13, H14.
      eapply header_isValid_sound; eassumption.
    }
    clear -H.
    simpl.
    destruct (lift_option (map header_isValid (map snd kvs))) eqn:H_list_option.
    2 : constructor.
    apply lift_option_some_inv in H_list_option.
    rewrite H_list_option in H. clear H_list_option.
    assert (l = valid_bits). {
      list_simplify.
      destruct H.
      list_simplify.
      inv H8. list_solve.
    }
    rewrite H0.
    constructor.
Qed.

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
  (count >= 0)%Z ->
  sval_refine sv (ValBaseStack headers next) ->
  sval_refine (push_front sv count) (Semantics.push_front headers next count).
Proof.
  intros.
  inv H0.
  unfold push_front, Semantics.push_front.
  constructor.
  range_form. destruct H3. rewrite H0.
  destruct (count <=? Zlength headers)%Z eqn:?.
  - list_simplify.
    + intro; intros.
      list_simplify. apply sval_refine_uninit_sval_of_sval_trans. auto.
    + intro; intros.
      list_solve.
  - list_simplify.
    + intro; intros.
      list_simplify. apply sval_refine_uninit_sval_of_sval_trans. auto.
    + intro; intros.
      list_solve.
Qed.

Definition pop_front (sv : Sval) (count : Z) : Sval :=
  match sv with
  | ValBaseStack headers next =>
      pop_front headers next count
  | _ => sv
  end.

Lemma pop_front_sound : forall sv headers next count,
  (count >= 0)%Z ->
  sval_refine sv (ValBaseStack headers next) ->
  sval_refine (pop_front sv count) (Semantics.pop_front headers next count).
Proof.
  intros.
  inv H0.
  unfold pop_front, Semantics.pop_front.
  constructor.
  range_form. destruct H3. rewrite H0.
  destruct (count <=? Zlength headers)%Z eqn:?.
  - list_simplify.
    + intro; intros.
      list_simplify. apply sval_refine_uninit_sval_of_sval_trans. auto.
    + intro; intros.
      list_solve.
  - list_simplify.
    + intro; intros.
      list_simplify. apply sval_refine_uninit_sval_of_sval_trans. auto.
    + intro; intros.
      list_solve.
Qed.

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
    intro; intros.
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
    intro; intros. inv H. constructor.
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
    intro; intros. inv H. constructor.
  - unfold eval_builtin in H. simpl in H.
    destruct H0. inv H0; inv H8; inv H9.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H1) H3).
    destruct (eval_write a_mem lv (push_front v count)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    specialize (H_eval_write _ _ _ ltac:(apply H1) ltac:(eapply push_front_sound; eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intro; intros. inv H. constructor.
  - unfold eval_builtin in H. simpl in H.
    destruct H0. inv H0; inv H8; inv H9.
    destruct (eval_read a_mem lv) eqn:H_eval_read. 2 : inv H.
    eapply eval_read_sound in H_eval_read; eauto.
    specialize (H_eval_read _ _ ltac:(apply H1) H3).
    destruct (eval_write a_mem lv (pop_front v count)) eqn:H_eval_write. 2 : inv H.
    eapply eval_write_sound in H_eval_write; eauto.
    specialize (H_eval_write _ _ _ ltac:(apply H1) ltac:(eapply pop_front_sound; eassumption) ltac:(eassumption)).
    inv H.
    split. 2 : auto.
    intro; intros. inv H. constructor.
Qed.

End EvalBuiltin.

#[export] Hint Resolve eval_builtin_sound : hoare.
