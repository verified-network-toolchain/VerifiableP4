Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.TofinoSpec.
Require Import ProD3.examples.sbf.UseTofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import ProD3.examples.sbf.verif_Row11.
Require Import ProD3.examples.sbf.verif_Row12.
Require Import ProD3.examples.sbf.verif_Row13.
Require Import Hammer.Plugin.Hammer.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p :=  ["pipe"; "ingress"; "bf2_ds"; "win_1"].

Definition Win_fundef :=
  ltac:(get_fd ["Bf2BloomFilterWin"; "apply"] ge).

Definition rows := ["row_1"; "row_2"; "row_3"].

Definition Win_noop_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : list Z)
      (_ : Zlength f = num_rows)
      (_ : Zlength is = num_rows)
      (_ : Forall (fun r => Zlength r = num_slots) f)
      (_ : Forall (fun i => 0 <= i < num_slots) is),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4NewBit 8);
                ("rw_2", P4NewBit 8);
                ("rw_3", P4NewBit 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4NewBit 8);
                ("rw_2", P4NewBit 8);
                ("rw_3", P4NewBit 8)
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))).

Lemma destruct_Zlength_3 : forall {A} (l : list A),
  Zlength l = 3 ->
  exists x1 x2 x3, l = [x1; x2; x3].
Proof.
  intros.
  destruct l as [ | x1 l]; only 1 : list_solve.
  destruct l as [ | x2 l]; only 1 : list_solve.
  destruct l as [ | x3 l]; only 1 : list_solve.
  destruct l as [ | x4 l]; only 2 : list_solve.
  eauto.
Qed.

Lemma Win_noop_body :
  func_sound ge Win_fundef nil Win_noop_spec.
Proof.
  start_function.
  unfold frame_repr.
  normalize_EXT.
  apply destruct_Zlength_3 in x.
  destruct x as [r1 [r2 [r3 ?]]]; subst.
  apply destruct_Zlength_3 in x0.
  destruct x0 as [i1 [i2 [i3 ?]]]; subst.
  inv x1. inv H2. inv H4.
  inv x2. inv H6. inv H8.
  step_call verif_Row11.Row_noop_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row12.Row_noop_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row13.Row_noop_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step.
  entailer.
Qed.

Definition Win_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : list Z)
      (_ : Zlength f = num_rows)
      (_ : Zlength is = num_rows)
      (_ : Forall (fun r => Zlength r = num_slots) f)
      (_ : Forall (fun i => 0 <= i < num_slots) is),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4NewBit 8);
                ("rw_2", P4NewBit 8);
                ("rw_3", P4NewBit 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4Bit 8 1);
                ("rw_2", P4Bit 8 1);
                ("rw_3", P4Bit 8 1)
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows (frame_insert f is)]))).

Lemma Win_insert_body :
  func_sound ge Win_fundef nil Win_insert_spec.
Proof.
  start_function.
  unfold frame_repr.
  normalize_EXT.
  apply destruct_Zlength_3 in x.
  destruct x as [r1 [r2 [r3 ?]]]; subst.
  apply destruct_Zlength_3 in x0.
  destruct x0 as [i1 [i2 [i3 ?]]]; subst.
  inv x1. inv H2. inv H4.
  inv x2. inv H6. inv H8.
  step_call verif_Row11.Row_insert_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row12.Row_insert_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row13.Row_insert_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step.
  entailer.
Qed.

Definition Win_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : list Z)
      (_ : Zlength f = num_rows)
      (_ : Zlength is = num_rows)
      (_ : Forall (fun r => Zlength r = num_slots) f)
      (_ : Forall (fun i => 0 <= i < num_slots) is),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4NewBit 8);
                ("rw_2", P4NewBit 8);
                ("rw_3", P4NewBit 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4Bit 8 (Z.b2z (row_query (Znth 0 f) (Znth 0 is))));
                ("rw_2", P4Bit 8 (Z.b2z (row_query (Znth 1 f) (Znth 1 is))));
                ("rw_3", P4Bit 8 (Z.b2z (row_query (Znth 2 f) (Znth 2 is))))
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))).

Lemma Win_query_body :
  func_sound ge Win_fundef nil Win_query_spec.
Proof.
  start_function.
  unfold frame_repr.
  normalize_EXT.
  apply destruct_Zlength_3 in x.
  destruct x as [r1 [r2 [r3 ?]]]; subst.
  apply destruct_Zlength_3 in x0.
  destruct x0 as [i1 [i2 [i3 ?]]]; subst.
  inv x1. inv H2. inv H4.
  inv x2. inv H6. inv H8.
  step_call verif_Row11.Row_query_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row12.Row_query_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row13.Row_query_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step.
  entailer.
Qed.

Definition Win_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : list Z)
      (_ : Zlength f = num_rows)
      (_ : Zlength is = num_rows)
      (_ : Forall (fun r => Zlength r = num_slots) f)
      (_ : Forall (fun i => 0 <= i < num_slots) is),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4NewBit 8);
                ("rw_2", P4NewBit 8);
                ("rw_3", P4NewBit 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit 18 (Znth 0 is));
                ("index_2", P4Bit 18 (Znth 1 is));
                ("index_3", P4Bit 18 (Znth 2 is));
                ("rw_1", P4Bit 8 0);
                ("rw_2", P4Bit 8 0);
                ("rw_3", P4Bit 8 0)
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows (frame_clear f is)]))).

Lemma Win_clear_body :
  func_sound ge Win_fundef nil Win_clear_spec.
Proof.
  start_function.
  unfold frame_repr.
  normalize_EXT.
  apply destruct_Zlength_3 in x.
  destruct x as [r1 [r2 [r3 ?]]]; subst.
  apply destruct_Zlength_3 in x0.
  destruct x0 as [i1 [i2 [i3 ?]]]; subst.
  inv x1. inv H2. inv H4.
  inv x2. inv H6. inv H8.
  step_call verif_Row11.Row_clear_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row12.Row_clear_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step_call verif_Row13.Row_clear_case_body.
  3 : { entailer. }
  { auto. }
  { list_solve. }
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Win_noop_body) : func_specs.
