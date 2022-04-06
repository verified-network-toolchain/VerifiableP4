Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Poulet4.P4light.Syntax.Typed.
Require Import Poulet4.P4light.Syntax.Syntax.
Require Import Poulet4.P4light.Syntax.Value.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Poulet4.P4light.Architecture.V1Model.
Require Import Poulet4.P4light.Syntax.P4Notations.
Require Import Poulet4.Utils.P4Arith.
Require Import ProD3.core.Coqlib.
Require Import ProD3.core.Hoare.
Require Import ProD3.core.Modifies.
Require Import ProD3.core.FuncSpec.
Require Import ProD3.core.AssertionNotations.
Require Import BinNat.
Require Import BinInt.
Open Scope Z_scope.
(* Require Import Hammer.Tactics.Tactics.
Require Import Hammer.Plugin.Hammer. *)

Section V1ModelSpec.

Context [tags_t: Type] [tags_t_inhabitant : Inhabitant tags_t].
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
(* Notation ValSet := (@ValueSet tags_t). *)
Notation Lval := ValueLvalue.

Notation ident := string.
Notation path := (list ident).
Notation Expression := (@Expression tags_t).
Notation argument := (@argument tags_t).

Instance target : @Target tags_t Expression := V1Model.

Variable ge : genv.

Open Scope func_spec.

Definition register_read_spec (p : path) (reg_s : register_static) : func_spec :=
  WITH,
    PATH p
    MOD None []
    WITH (reg : register) (i : Z) (H : (0 <= i < snd reg_s)%Z)
    (HR: snd reg_s <= 2 ^ 32),
      PRE
        (ARG [ValBaseBit (to_loptbool 32%N i)]
        (MEM []
        (EXT [(p, ObjRegister reg)])))
      POST
        (ARG_RET [eval_val_to_sval (Znth i reg)] ValBaseNull
        (MEM []
        (EXT []))).

Lemma register_read_body : forall (p : path) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  fundef_satisfies_spec ge (FExternal "register" "read") nil (register_read_spec p reg_s).
Proof.
  intros. unfold register_read_spec. simpl. split; repeat intro.
  - red in H0. destruct H0. do 2 red in H0. inv H0. inv H7. inv H5. red. inv H1.
    inv H5. inv H7. inv H4. inv H8. simpl in H0. inv H0. simpl. red.
    split; [|split]; auto.
    + inv H14. inv H10. apply SvalRefine.Forall2_bit_refine_Some_same' in H3.
      subst. apply Forall2_ndetbit in H1. subst. rewrite bit_from_to_bool in H7.
      constructor. 2: constructor. destruct H2. red in H1. red in H1. simpl in H1.
      destruct H1. rewrite H6 in H1. inv H1. simpl in H. rewrite H in H5. inv H5.
      simpl in x1. assert ((-1 <? index) && (index <? size) = true). {
        apply andb_true_intro. pose proof (BitArith.upper_bound_ge_1 32). split.
        - rewrite Z.ltb_lt. cut (0 <= index < BitArith.upper_bound 32).
          1: intros; lia. inv H7. unfold BitArith.mod_bound. apply Zdiv.Z_mod_lt. lia.
        - rewrite Z.ltb_lt. cut (index <= x0). 1: lia. inv H7.
          unfold BitArith.mod_bound. apply Zdiv.Zmod_le; lia. } rewrite H1 in H11.
      subst. rewrite val_to_sval_iff in H8. inversion H7. subst index. simpl in x2.
      clear -H8 x1 x2. unfold BitArith.mod_bound, BitArith.upper_bound in H8.
      change (2 ^ Z.of_N 32) with (Z.pow_pos 2 32) in H8.
      rewrite Zdiv.Zmod_small in H8 by lia. rewrite H8.
      apply SvalRefine.sval_refine_refl.
    + repeat intro. inv H0. constructor.
    + destruct H2; split; auto.
  - red. split; auto. repeat intro. inv H0. simpl. inv H7. simpl in H0. inv H0. auto.
Qed.

(* We need to say v is a definite value, right? *)
Definition register_write_spec (p : path) (reg_s : register_static) : func_spec :=
  WITH,
    PATH p
    MOD None [p]
    WITH (reg : register) (i : Z) (v : Val) (H : (0 <= i < snd reg_s)%Z)
    (HR: snd reg_s <= 2 ^ 32),
      PRE
        (ARG [ValBaseBit (to_loptbool 32%N i); eval_val_to_sval v]
        (MEM []
        (EXT [(p, ObjRegister reg)])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM []
        (EXT [(p, ObjRegister (upd_Znth i reg v))]))).

Lemma register_write_body : forall (p : path) (reg_s : register_static),
  PathMap.get p (ge_ext ge) = Some (EnvRegister reg_s) ->
  fundef_satisfies_spec ge (FExternal "register" "write") nil (register_write_spec p reg_s).
Proof.
  intros. unfold register_write_spec. simpl. split; repeat intro.
  - red in H0. destruct H0. do 2 red in H0. inv H0. inv H7. inv H8. inv H5.
    inv H1. inv H6. inv H8. inv H10. inv H5. simpl in H9. inv H9. simpl in H0.
    inv H0. simpl in H. rewrite H in H8. clear H. inv H8. simpl in *. red.
    split; [|split].
    + inv H15. constructor.
    + repeat intro. inv H. constructor.
    + red. destruct H2. split; auto. red. red. simpl. split; auto.
      apply SvalRefine.Forall2_bit_refine_Some_same' in H3. subst.
      apply Forall2_ndetbit in H1. subst. rewrite bit_from_to_bool in H14.
      assert ((-1 <? index) && (index <? size) = true). {
        apply andb_true_intro. pose proof (BitArith.upper_bound_ge_1 32). split.
        - rewrite Z.ltb_lt. cut (0 <= index < BitArith.upper_bound 32).
          1: intros; lia. inv H14. unfold BitArith.mod_bound. apply Zdiv.Z_mod_lt. lia.
        - rewrite Z.ltb_lt. cut (index <= x0). 1: lia. inv H14.
          unfold BitArith.mod_bound. apply Zdiv.Zmod_le; lia. } rewrite H1 in H16.
      subst. rewrite PathMap.get_set_same. f_equal.
      apply exec_val_eval_val_to_sval_eq in H4. 2: intros s1 s2 Hs; now inv Hs.
      subst. apply sval_to_val_eval_val_to_sval_eq in H6.
      2: intros s1 s2 Hs; now inv Hs. subst x1. do 2 red in H0. simpl in H0.
      destruct H0 as [? _]. rewrite H9 in H0. inv H0. inv H14.
      unfold BitArith.mod_bound, BitArith.upper_bound.
      change (2 ^ Z.of_N 32) with (Z.pow_pos 2 32).
      rewrite Zdiv.Zmod_small by lia. auto.
  - red. split; auto. repeat intro. inv H0. simpl. inv H7. simpl in H0. inv H0.
    destruct ((-1 <? index) && (index <? size)); subst; auto.
    rewrite PathMap.get_set_diff; auto. intro. apply H1. now left.
Qed.

End V1ModelSpec.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (refine (proj2 (register_read_body _ _ _ _))) : func_specs.
#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (refine (proj2 (register_write_body _ _ _ _))) : func_specs.

(*
Several issues:
- out of bounds for i
- to_lbool/to_loptbool is N-to-1 mapping, diffcult to automate
=> also a problem in semantics.v
- are v and i assumed to be bounded in post_condition?
*)
