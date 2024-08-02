Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import Coq.Program.Program.
Require Import ProD3.core.PacketFormat.
Require Import ProD3.core.Core.
Require Import ProD3.core.Tofino.
Require Import ProD3.examples.sbf_gen.p4ast.
Require Import ProD3.examples.sbf_gen.ConFilter.

Open Scope func_spec.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation Val_eqb := (val_eqb Bool.eqb).


Definition am_ge := ltac:(get_am_ge prog).
(* Finished transaction in 4.375 secs (4.218u,0.156s) (successful) *)
Definition ge := ltac:(get_ge am_ge prog).

Definition tcp_h: P4Type := ltac:(get_type "tcp_h" ge).
Definition udp_h: P4Type := ltac:(get_type "udp_h" ge).
Definition ipv4_h: P4Type := ltac:(get_type "ipv4_h" ge).
Definition ethernet_h: P4Type := ltac:(get_type "ethernet_h" ge).

Record header_t_rec := {
    header_t_ethernet: Sval;
    header_t_ipv4: Sval;
    header_t_tcp: Sval;
    header_t_udp: Sval;
  }.

Definition hdr (hsample: header_t_rec) :=
  ValBaseStruct
    [("ethernet", header_t_ethernet hsample);
     ("ipv4", header_t_ipv4 hsample);
     ("tcp", header_t_tcp hsample);
     ("udp", header_t_udp hsample)].

Definition hdr_init: header_t_rec :=
  Build_header_t_rec
    (ValBaseHeader
       [("dst_addr", P4Bit_ 48);
        ("src_addr", P4Bit_ 48);
        ("ether_type", P4Bit_ 16)] (Some false))
    (ValBaseHeader
       [("version", P4Bit_ 4);
        ("ihl", P4Bit_ 4);
        ("diffserv", P4Bit_ 8);
        ("total_len", P4Bit_ 16);
        ("identification", P4Bit_ 16);
        ("flags", P4Bit_ 3);
        ("frag_offset", P4Bit_ 13);
        ("ttl", P4Bit_ 8);
        ("protocol", P4Bit_ 8);
        ("hdr_checksum", P4Bit_ 16);
        ("src_addr", P4Bit_ 32);
        ("dst_addr", P4Bit_ 32)]
       (Some false))
    (ValBaseHeader
       [("src_port", P4Bit_ 16);
        ("dst_port", P4Bit_ 16);
        ("seq_no", P4Bit_ 32);
        ("ack_no", P4Bit_ 32);
        ("data_offset", P4Bit_ 4);
        ("res", P4Bit_ 4);
        ("flags", P4Bit_ 8);
        ("window", P4Bit_ 16);
        ("checksum", P4Bit_ 16);
        ("urgent_ptr", P4Bit_ 16)]
       (Some false))
    (ValBaseHeader
        [("src_port", P4Bit_ 16);
         ("dst_port", P4Bit_ 16);
         ("hdr_length", P4Bit_ 16);
         ("checksum", P4Bit_ 16)]
        (Some false)).

Lemma ext_val_typ_ipv4: forall ipv4, ⊫ᵥ ipv4_repr_val ipv4 \: ipv4_h.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.

Lemma force_cast_P4BitV_eq: forall w v,
    force ValBaseNull (@Ops.eval_cast Info (TypBit w) (P4BitV w v)) = P4BitV w v.
Proof.
  intros. unfold P4BitV. simpl. f_equal. rewrite P4Arith.bit_to_lbool_back.
  unfold P4Arith.BitArith.mod_bound. rewrite Zmod_mod.
  change (v mod _) with (P4Arith.BitArith.mod_bound w v).
  rewrite P4Arith.to_lbool_bit_mod. reflexivity.
Qed.

Lemma abs_ipv4_hdr_eq_eq: forall ipv4 hsample w v,
    abs_eq
      (get "protocol"
         (get "ipv4"
            (update "ipv4" (eval_val_to_sval (ipv4_repr_val ipv4))
               (hdr hsample))))
      (build_abs_unary_op (@Ops.eval_cast Info (TypBit w))
         (eval_val_to_sval (P4BitV w v))) =
      eval_val_to_sval
        (force ValBaseNull
           (Ops.eval_binary_op Eq (P4BitV 8 (ipv4_protocol ipv4)) (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ipv4_repr_val.
  Opaque P4BitV. simpl get. Transparent P4BitV. unfold abs_eq.
  unfold build_abs_binary_op. rewrite !eval_sval_to_val_eq. reflexivity.
Qed.

Lemma ext_val_typ_ethernet: forall ether, ⊫ᵥ ethernet_repr_val ether \: ethernet_h.
Proof. intros. split; [repeat constructor | reflexivity]. Qed.

Lemma abs_ether_eq_eq: forall ether hsample w v,
    abs_eq
      (get "ether_type"
         (get "ethernet"
            (update "ethernet" (eval_val_to_sval (ethernet_repr_val ether))
               (hdr hsample))))
      (build_abs_unary_op (@Ops.eval_cast Info (TypBit w))
         (eval_val_to_sval (P4BitV w v))) =
      eval_val_to_sval
        (force ValBaseNull
           (Ops.eval_binary_op Eq (P4BitV 16 (ethernet_ether_type ether))
              (P4BitV w v))).
Proof.
  intros. rewrite get_update_same; auto.
  unfold build_abs_unary_op. rewrite eval_sval_to_val_eq.
  rewrite force_cast_P4BitV_eq. unfold ethernet_repr_val.
  Opaque P4BitV. simpl get. Transparent P4BitV. unfold abs_eq.
  unfold build_abs_binary_op. rewrite !eval_sval_to_val_eq. reflexivity.
Qed.


(* Constants *)

Definition NOOP := 0.
Definition CLEAR := 1.
Definition INSERT := 2.
Definition QUERY := 3.
Definition INSQUERY := 4.

Definition index_w := 18%N.
Definition num_slots := Eval compute in 2 ^ (Z.of_N index_w).
Definition num_rows := 3.
Definition num_frames := 4.
Definition frame_tick_tocks := 7034.
Definition tick_time := 2097152.
Definition frame_time := frame_tick_tocks * tick_time * 2.

Definition poly1 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 79764919;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash1 (v : Val) :=
  hash_Z 32 poly1 v mod 2 ^ (Z.of_N index_w).

Definition poly2 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 517762881;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash2 (v : Val) :=
  hash_Z 32 poly2 v mod 2 ^ Z.of_N index_w.


Definition poly3 : Tofino.CRC_polynomial :=
  {|
    Tofino.CRCP_width := 32;
    Tofino.CRCP_coeff := P4Arith.to_lbool 32 2821953579;
    Tofino.CRCP_reversed := true;
    Tofino.CRCP_msb := false;
    Tofino.CRCP_extended := false;
    Tofino.CRCP_init := P4Arith.to_lbool 32 0;
    Tofino.CRCP_xor := P4Arith.to_lbool 32 4294967295
  |}.

Definition hash3 (v : Val) :=
  hash_Z 32 poly3 v mod 2 ^ Z.of_N index_w.

Definition header_type : Set := Z * Z.

Definition header_to_val '((x, y) : header_type) : Val :=
  ValBaseBit ((P4Arith.to_lbool 32 y) ++ (P4Arith.to_lbool 32 x)).

Definition hashes := [hash1 ∘ header_to_val; hash2 ∘ header_to_val; hash3 ∘ header_to_val].

Lemma H_Zlength_hashes : Zlength hashes = num_rows.
Proof. auto. Qed.

Lemma b2z_range : forall b,
  0 <= Z.b2z b < 2.
Proof.
  destruct b; simpl; lia.
Qed.

Ltac add_b2z_range b :=
  assert_fails (assert (0 <= Z.b2z b < 2) by assumption);
  pose proof (b2z_range b).

Ltac saturate_b2z :=
  repeat match goal with
  | H : context [Z.b2z ?b] |- _ =>
      add_b2z_range b
  | |- context [Z.b2z ?b] =>
      add_b2z_range b
  end.

Ltac Zify.zify_pre_hook ::=
  unfold is_true, index_w, num_slots, num_rows, num_frames, frame_tick_tocks,
    NOOP, CLEAR, INSERT, QUERY, INSQUERY in *;
  saturate_b2z.

Definition rows := ["row_1"; "row_2"; "row_3"].
Definition panes := ["win_1"; "win_2"; "win_3"; "win_4"].

Definition H_num_slots : 0 < num_slots := eq_refl.
Definition H_num_rows : 0 < num_rows := eq_refl.
Definition H_num_frames : 1 < num_frames := eq_refl.

Notation row := (row num_slots).
Notation frame := (frame num_rows num_slots).

#[export] Instance Inhabitant_row : Inhabitant row :=
  Inhabitant_row H_num_slots.

#[export] Instance Inhabitant_frame : Inhabitant frame :=
  Inhabitant_frame H_num_rows H_num_slots.

Definition GENERATOR_PORT: Z := 196.

Definition is_gen (port: Z) : bool :=
  Val_eqb (P4BitV 9 port) (P4BitV 9 GENERATOR_PORT).
