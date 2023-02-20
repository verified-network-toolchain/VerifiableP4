Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import ProD3.examples.cms.verif_Row21.
Require Import ProD3.examples.cms.verif_Row22.
Require Import ProD3.examples.cms.verif_Row23.
Require Import ProD3.examples.cms.verif_Row24.
Require Import ProD3.examples.cms.verif_Row25.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "cm2_ds"; "win_2"].

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
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4);
                ("rw_5", P4Bit value_w rw_5)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_4));
                ("rw_2", P4Bit value_w (P4min rw_2 rw_5));
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4);
                ("rw_5", P4Bit value_w rw_5)
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
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_3));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
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

Definition act_merge_rows_3_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "act_merge_rows_3"] ge).

Definition act_merge_rows_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_2));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_3_body :
  func_sound ge act_merge_rows_3_fd nil act_merge_rows_3_spec.
Proof.
  start_function.
  step_call min_body.
  { entailer. }
  step.
  entailer.
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply act_merge_rows_3_body) : func_specs.

Definition tbl_merge_rows_1_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "tbl_merge_rows_1"; "apply"] ge).

Definition tbl_merge_rows_1_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4);
                ("rw_5", P4Bit value_w rw_5)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_4));
                ("rw_2", P4Bit value_w (P4min rw_2 rw_5));
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", P4Bit value_w rw_4);
                ("rw_5", P4Bit value_w rw_5)
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
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_3));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", P4Bit value_w rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
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

Definition tbl_merge_rows_3_fd :=
  ltac:(get_fd ["Cm2CountMinSketchWin"; "tbl_merge_rows_3"; "apply"] ge).

Definition tbl_merge_rows_3_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api index_1 index_2 index_3 index_4 index_5 rw_1 rw_2 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w rw_1);
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit value_w (P4min rw_1 rw_2));
                ("rw_2", P4Bit value_w rw_2);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_3_body :
  func_sound ge tbl_merge_rows_3_fd nil tbl_merge_rows_3_spec.
Proof.
  start_function.
  table_action act_merge_rows_3_body.
  { entailer. }
  { entailer. }
Qed.

#[local] Hint Extern 5 (func_modifies _ _ _ _ _) => (apply tbl_merge_rows_3_body) : func_specs.

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
    WITH api index_1 index_2 index_3 index_4 index_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
    WITH api index_1 index_2 index_3 index_4 index_5 rw_2 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", rw_2);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", rw_2);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
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

Definition act_merge_rows_3_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api index_1 index_2 index_3 index_4 index_5 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (ARG_RET [] ValBaseNull
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT []))).

Lemma act_merge_rows_3_undef_body :
  func_sound ge act_merge_rows_3_fd nil act_merge_rows_3_undef_spec.
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
    WITH api index_1 index_2 index_3 index_4 index_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
    WITH api index_1 index_2 index_3 index_4 index_5 rw_2 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", rw_2);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", rw_2);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
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

Definition tbl_merge_rows_3_undef_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD (Some [["win_md"]]) []
    WITH api index_1 index_2 index_3 index_4 index_5 rw_3 rw_4 rw_5,
      PRE
        (ARG []
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT [])))
      POST
        (EX retv,
        (ARG_RET [] retv
        (MEM [(["win_md"], ValBaseStruct
               [("api", api);
                ("index_1", index_1);
                ("index_2", index_2);
                ("index_3", index_3);
                ("index_4", index_4);
                ("index_5", index_5);
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", rw_3);
                ("rw_4", rw_4);
                ("rw_5", rw_5)
               ])
             ]
        (EXT []))))%arg_ret_assr.

Lemma tbl_merge_rows_3_undef_body :
  func_sound ge tbl_merge_rows_3_fd nil tbl_merge_rows_3_undef_spec.
Proof.
  start_function.
  table_action act_merge_rows_3_undef_body.
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
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
  step_call verif_Row21.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row22.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row23.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row24.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row25.Row_noop_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_undef_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_2_undef_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_3_undef_body.
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
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
  step_call verif_Row21.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row22.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row23.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row24.Row_insert_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row25.Row_insert_case_body.
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
  step_call tbl_merge_rows_3_undef_body.
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
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit value_w (Z.min (frame_query f (`is)) (2 ^ 32 - 1)));
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))).

(* A very slow test case in "apply" unless makeing row_repr opaque. *)
(* Lemma test : forall (x x0 : row), exists p0,
  ext_implies [row_repr (p ++ ["row_1"]) x] [row_repr p0 x0].
Proof.
  intros. eexists.
  apply ext_implies_refl. *)

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

Ltac pose_row_query_bound r i :=
  P4assert (row_query r i >= 0);
  only 1 : (
    eapply ext_implies_trans;
    only 2 : (apply row_query_bound; auto);
    entailer
  ).

  Opaque row_repr.
  pose_row_query_bound x x4.
  pose_row_query_bound x0 x5.
  pose_row_query_bound x1 x6.
  pose_row_query_bound x2 x7.
  pose_row_query_bound x3 x8.
  Transparent row_repr.

  step_call verif_Row21.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row22.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row23.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row24.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row25.Row_query_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_2_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_3_body.
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
  2-5 : repeat constructor.
  apply sval_refine_refl'. do 3 f_equal.
  unfold P4min.
  change (Znth 0 [x4; x5; x6; x7; x8]) with x4.
  change (Znth 1 [x4; x5; x6; x7; x8]) with x5.
  change (Znth 2 [x4; x5; x6; x7; x8]) with x6.
  change (Znth 3 [x4; x5; x6; x7; x8]) with x7.
  change (Znth 4 [x4; x5; x6; x7; x8]) with x8.
  unfold value_w.
  rewrite_strat bottomup mod_bound_small.
  2-9 : lia.
  unfold frame_query.
  simpl Utils.list_min.
  repeat rewrite Zmin_shrink.
  f_equal.
  lia.
Qed.

Definition Win_clear_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit value_w 0);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
  step_call verif_Row21.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row22.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row23.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row24.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call verif_Row25.Row_clear_case_body.
  { entailer. }
  { auto. }
  step_call tbl_merge_rows_1_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_2_body.
  { entailer. }
  Intros _.
  step_call tbl_merge_rows_3_body.
  { entailer. }
  Intros _.
  step.
  entailer.
  constructor.
  repeat first [
    apply Forall2_nil
  | apply Forall2_cons; only 1 : (split; only 1 : reflexivity);
    try apply sval_refine_refl
  ];
  repeat constructor.
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
               [("api", P4Bit 8 op);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [
          if op =? NOOP then
             ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
          else if op =? CLEAR then
             ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit value_w 0);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
          else if op =? INSERT then
             ValBaseStruct
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit_ value_w);
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
               ]
          else
             ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit index_w (Znth 0 (`is)));
                ("index_2", P4Bit index_w (Znth 1 (`is)));
                ("index_3", P4Bit index_w (Znth 2 (`is)));
                ("index_4", P4Bit index_w (Znth 3 (`is)));
                ("index_5", P4Bit index_w (Znth 4 (`is)));
                ("rw_1", P4Bit value_w (Z.min (frame_query f (`is)) (2 ^ 32 - 1)));
                ("rw_2", P4Bit_ value_w);
                ("rw_3", P4Bit_ value_w);
                ("rw_4", P4Bit_ value_w);
                ("rw_5", P4Bit_ value_w)
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
