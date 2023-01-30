Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.cms.ConModel.
Require Import ProD3.examples.cms.common.
Require Import ProD3.examples.cms.ModelRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "cm2_ds"; "win_1"].

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
Admitted.

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
Admitted.

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
Admitted.

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
