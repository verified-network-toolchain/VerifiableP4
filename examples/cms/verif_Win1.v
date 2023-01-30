Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import ProD3.examples.cms.verif_Row11.
Require Import ProD3.examples.cms.verif_Row12.
Require Import ProD3.examples.cms.verif_Row13.
Require Import ProD3.examples.cms.verif_Row14.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "cm2_ds"; "win_1"].

Definition P4min a b := Z.min (P4Arith.BitArith.mod_bound value_w a) (P4Arith.BitArith.mod_bound value_w b).

Definition min_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH (a b : Z),
      PRE
        (ARG [P4Bit value_w a; P4Bit value_w b]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] (P4Bit value_w (P4min a b))
        (MEM []
        (EXT []))).

Lemma min_body :
  func_sound ge (FExternal "" "min") [TypBit value_w] min_spec.
Admitted.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply min_body) : func_specs.

Definition act_merge_rows_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "act_merge_rows_1"] ge).

Definition act_merge_rows_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_1 rw_2 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_3));
                ("rw_2", P4Bit value_w (P4min rw_2 rw_4));
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_1_body :
  func_sound ge act_merge_rows_1_fd nil act_merge_rows_1_spec.
Proof.
  start_function.
  step_call min_body.
  { entailer. }
  step_call min_body.
  { entailer. }
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_merge_rows_1_body) : func_specs.

Definition act_merge_rows_2_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "act_merge_rows_2"] ge).

Definition act_merge_rows_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_1 rw_2 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_2));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_2_body :
  func_sound ge act_merge_rows_2_fd nil act_merge_rows_2_spec.
Proof.
  start_function.
  step_call min_body.
  { entailer. }
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_merge_rows_2_body) : func_specs.

Definition tbl_merge_rows_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "tbl_merge_rows_1"; "apply"] ge).

Definition tbl_merge_rows_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_1 rw_2 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_3));
                ("rw_2", P4Bit value_w (P4min rw_2 rw_4));
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_1_body :
  func_sound ge tbl_merge_rows_1_fd nil tbl_merge_rows_1_spec.
Proof.
  start_function.
  table_action act_merge_rows_1_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_merge_rows_1_body) : func_specs.

Definition tbl_merge_rows_2_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "tbl_merge_rows_2"; "apply"] ge).

Definition tbl_merge_rows_2_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_1 rw_2 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_2));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_2_body :
  func_sound ge tbl_merge_rows_2_fd nil tbl_merge_rows_2_spec.
Proof.
  start_function.
  table_action act_merge_rows_2_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_merge_rows_2_body) : func_specs.

Definition min_undef_spec : func_spec :=
  WITH,
    PATH []
    MOD None []
    WITH,
      PRE
        (ARG [P4Bit_ value_w; P4Bit_ value_w]
        (MEM []
        (EXT [])))
      POST
        (ARG_RET [] (P4Bit_ value_w)
        (MEM []
        (EXT []))).

Lemma min_undef_body :
  func_sound ge (FExternal "" "min") [TypBit value_w] min_undef_spec.
Admitted.

Definition act_merge_rows_1_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_1_undef_body :
  func_sound ge act_merge_rows_1_fd nil act_merge_rows_1_undef_spec.
Proof.
  start_function.
  step_call min_undef_body.
  { entailer. }
  step_call min_undef_body.
  { entailer. }
  step.
  entailer.
Qed.

Definition act_merge_rows_2_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_2_undef_body :
  func_sound ge act_merge_rows_2_fd nil act_merge_rows_2_undef_spec.
Proof.
  start_function.
  step_call min_undef_body.
  { entailer. }
  step.
  entailer.
Qed.

Definition tbl_merge_rows_1_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_1_undef_body :
  func_sound ge tbl_merge_rows_1_fd nil tbl_merge_rows_1_undef_spec.
Proof.
  start_function.
  table_action act_merge_rows_1_undef_body.
  { entailer. }
  { entailer. }
Qed.

Definition tbl_merge_rows_2_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api_call index_1 index_2 index_3 index_4 rw_3 rw_4,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api_call", api_call);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_2_undef_body :
  func_sound ge tbl_merge_rows_2_fd nil tbl_merge_rows_2_undef_spec.
Proof.
  start_function.
  table_action act_merge_rows_2_undef_body.
  { entailer. }
  { entailer. }
Qed.

Definition Win_fundef :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "apply"] ge).

Definition Win_noop_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api_call", P4Bit 32 NOOP);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api_call", P4Bit 32 NOOP);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))).

Lemma Win_noop_body :
  func_sound ge Win_fundef nil Win_noop_spec.
Proof.
  start_function.
  unfold frame_repr.
  normalize_EXT.
  destruct f as [f ?H]. destruct is as [is ?H].
  cbn [proj1_sig] in *.
  destruct_list f.
  destruct_list is.
  repeat lazymatch goal with
  | H : Forall _ _ |- _ => inv H
  end.
  step_call verif_Row11.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row12.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row13.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row14.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_undef_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_2_undef_body.
  { entailer. }
  Intros _.
  step.
  entailer.
Qed.

Definition Win_insert_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api_call", P4Bit 32 INSERT);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api_call", P4Bit 32 INSERT);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
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
  destruct f as [f ?H]. destruct is as [is ?H].
  cbn [proj1_sig frame_insert] in *.
  destruct_list f.
  destruct_list is.
  repeat lazymatch goal with
  | H : Forall _ _ |- _ => inv H
  end.
  step_call verif_Row11.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row12.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row13.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row14.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_undef_body.
  { entailer.
    repeat constructor.
  }
  Intros _.
  step_call tbl_merge_rows_2_undef_body.
  { entailer. }
  Intros _.
  step.
  entailer.
Qed.

Definition Win_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api_call", P4Bit 32 QUERY);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api_call", P4Bit 32 QUERY);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit value_w (frame_query f (`is)));
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
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
  destruct f as [f ?H]. destruct is as [is ?H].
  cbn [proj1_sig] in *.
  destruct_list f.
  destruct_list is.
  repeat lazymatch goal with
  | H : Forall _ _ |- _ => inv H
  end.
  step_call verif_Row11.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row12.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row13.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row14.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_2_body.
  { entailer. }
  Intros _.
  step.
  entailer.
  constructor.
  repeat first [
    apply Forall2_nil
  | apply Forall2_cons; only 1 : (split; only 1 : reflexivity);
    try apply sval_refine_refl
  ].
  2-4 : repeat constructor.
  apply sval_refine_refl'. repeat f_equal.
  admit. (* arith *)
(* Qed. *)
Admitted.

Definition Win_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api_call", P4Bit 32 CLEAR);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api_call", P4Bit 32 CLEAR);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
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
  destruct f as [f ?H]. destruct is as [is ?H].
  cbn [proj1_sig frame_clear] in *.
  destruct_list f.
  destruct_list is.
  repeat lazymatch goal with
  | H : Forall _ _ |- _ => inv H
  end.
  step_call verif_Row11.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row12.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row13.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row14.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_undef_body.
  { entailer.
    repeat constructor.
  }
  Intros _.
  step_call tbl_merge_rows_2_undef_body.
  { entailer. }
  Intros _.
  step.
  entailer.
Qed.

#[export] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply Win_noop_body) : func_specs.

Definition Win_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (op : Z) (f : frame) (is : listn Z num_rows)
      (_ : In op [NOOP; CLEAR; INSERT; QUERY])
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api_call", P4Bit 32 op);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [
          if op =? NOOP then
            ValBaseStruct
              [("api_call", P4Bit 32 NOOP);
               ("index_1", P4Bit index_w (Znth 0 (`is)));
               ("index_2", P4Bit index_w (Znth 1 (`is)));
               ("index_3", P4Bit index_w (Znth 2 (`is)));
               ("index_4", P4Bit index_w (Znth 3 (`is)));
               ("rw_1", P4Bit_ value_w);
               ("rw_2", P4Bit_ value_w);
               ("rw_3", P4Bit_ value_w);
               ("rw_4", P4Bit_ value_w)
              ]
          else if op =? CLEAR then
            ValBaseStruct
              [("api_call", P4Bit 32 CLEAR);
               ("index_1", P4Bit index_w (Znth 0 (`is)));
               ("index_2", P4Bit index_w (Znth 1 (`is)));
               ("index_3", P4Bit index_w (Znth 2 (`is)));
               ("index_4", P4Bit index_w (Znth 3 (`is)));
               ("rw_1", P4Bit_ value_w);
               ("rw_2", P4Bit_ value_w);
               ("rw_3", P4Bit_ value_w);
               ("rw_4", P4Bit_ value_w)
              ]
          else if op =? INSERT then
            ValBaseStruct
              [("api_call", P4Bit 32 INSERT);
               ("index_1", P4Bit index_w (Znth 0 (`is)));
               ("index_2", P4Bit index_w (Znth 1 (`is)));
               ("index_3", P4Bit index_w (Znth 2 (`is)));
               ("index_4", P4Bit index_w (Znth 3 (`is)));
               ("rw_1", P4Bit_ value_w);
               ("rw_2", P4Bit_ value_w);
               ("rw_3", P4Bit_ value_w);
               ("rw_4", P4Bit_ value_w)
              ]
          else
            ValBaseStruct
              [("api_call", P4Bit 32 QUERY);
               ("index_1", P4Bit index_w (Znth 0 (`is)));
               ("index_2", P4Bit index_w (Znth 1 (`is)));
               ("index_3", P4Bit index_w (Znth 2 (`is)));
               ("index_4", P4Bit index_w (Znth 3 (`is)));
               ("rw_1", P4Bit value_w (frame_query f (`is)));
               ("rw_2", P4Bit_ value_w);
               ("rw_3", P4Bit_ value_w);
               ("rw_4", P4Bit_ value_w)
              ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows (
          if op =? NOOP then
            f
          else if op =? CLEAR then
            frame_clear f is
          else if op =? INSERT then
            frame_insert f is
          else
            f
        )]))).

Lemma Win_body :
  func_sound ge Win_fundef nil Win_spec.
Proof.
  intros_fs_bind.
  split; only 2 : solve_modifies.
  intros_fsh_bind.
  destruct H.
  { subst.
    apply Win_noop_body; auto.
  }
  destruct H.
  { subst.
    apply Win_clear_body; auto.
  }
  destruct H.
  { subst.
    apply Win_insert_body; auto.
  }
  destruct H.
  { subst.
    apply Win_query_body; auto.
  }
  destruct H.
Qed.
