Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf.p4ast.
Require Import ProD3.examples.sbf.ConFilter.
Require Import ProD3.examples.sbf.common.
Require Import ProD3.examples.sbf.FilterRepr.
Require Import Hammer.Plugin.Hammer.
Require Export Coq.Program.Program.
Import ListNotations.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).

Definition p := ["pipe"; "ingress"; "bf2_ds"; "win_3"].

Definition Win_fundef :=
  ltac:(get_fd ["Bf2BloomFilterWin"; "apply"] ge).

Definition Win_noop_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 NOOP);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
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
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 INSERT);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
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
Admitted.

Definition Win_query_spec : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit 8 (Z.b2z (row_query (Znth 0 (`f)) (Znth 0 (`is)))));
                ("rw_2", P4Bit 8 (Z.b2z (row_query (Znth 1 (`f)) (Znth 1 (`is)))));
                ("rw_3", P4Bit 8 (Z.b2z (row_query (Znth 2 (`f)) (Znth 2 (`is)))))
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))).

Lemma Win_query_body :
  func_sound ge Win_fundef nil Win_query_spec.
Proof.
Admitted.

Definition Win_query_spec2 : func_spec :=
  WITH (* p *),
    PATH p
    MOD None [p]
    WITH (f : frame) (is : listn Z num_rows)
      (_ : Forall (fun i => 0 <= i < num_slots) (`is)),
      PRE
        (ARG [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST (EX r1 r2 r3
        (_ : r1 && r2 && r3 = frame_query f (`is)),
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 QUERY);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit 8 (Z.b2z r1));
                ("rw_2", P4Bit 8 (Z.b2z r2));
                ("rw_3", P4Bit 8 (Z.b2z r3))
               ]
        ] ValBaseNull
        (MEM []
        (EXT [frame_repr p rows f]))))%arg_ret_assr.

Lemma Win_query_body2 :
  func_sound ge Win_fundef nil Win_query_spec2.
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
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [ValBaseStruct
               [("api", P4Bit 8 CLEAR);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
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
               [("api", P4Bit 8 op);
                ("index_1", P4Bit 18 (Znth 0 (`is)));
                ("index_2", P4Bit 18 (Znth 1 (`is)));
                ("index_3", P4Bit 18 (Znth 2 (`is)));
                ("rw_1", P4Bit_ 8);
                ("rw_2", P4Bit_ 8);
                ("rw_3", P4Bit_ 8)
               ]
             ]
        (MEM []
        (EXT [frame_repr p rows f])))
      POST
        (ARG_RET [
          if op =? NOOP then
            ValBaseStruct
              [("api", P4Bit 8 NOOP);
               ("index_1", P4Bit 18 (Znth 0 (`is)));
               ("index_2", P4Bit 18 (Znth 1 (`is)));
               ("index_3", P4Bit 18 (Znth 2 (`is)));
               ("rw_1", P4Bit_ 8);
               ("rw_2", P4Bit_ 8);
               ("rw_3", P4Bit_ 8)
              ]
          else if op =? CLEAR then
            ValBaseStruct
              [("api", P4Bit 8 CLEAR);
               ("index_1", P4Bit 18 (Znth 0 (`is)));
               ("index_2", P4Bit 18 (Znth 1 (`is)));
               ("index_3", P4Bit 18 (Znth 2 (`is)));
               ("rw_1", P4Bit 8 0);
               ("rw_2", P4Bit 8 0);
               ("rw_3", P4Bit 8 0)
              ]
          else if op =? INSERT then
            ValBaseStruct
              [("api", P4Bit 8 INSERT);
               ("index_1", P4Bit 18 (Znth 0 (`is)));
               ("index_2", P4Bit 18 (Znth 1 (`is)));
               ("index_3", P4Bit 18 (Znth 2 (`is)));
               ("rw_1", P4Bit 8 1);
               ("rw_2", P4Bit 8 1);
               ("rw_3", P4Bit 8 1)
              ]
          else
            ValBaseStruct
              [("api", P4Bit 8 QUERY);
               ("index_1", P4Bit 18 (Znth 0 (`is)));
               ("index_2", P4Bit 18 (Znth 1 (`is)));
               ("index_3", P4Bit 18 (Znth 2 (`is)));
               ("rw_1", P4Bit 8 (Z.b2z (row_query (Znth 0 (`f)) (Znth 0 (`is)))));
               ("rw_2", P4Bit 8 (Z.b2z (row_query (Znth 1 (`f)) (Znth 1 (`is)))));
               ("rw_3", P4Bit 8 (Z.b2z (row_query (Znth 2 (`f)) (Znth 2 (`is)))))
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
