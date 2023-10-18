Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.Queue.
Require Import Poulet4.P4light.Architecture.TrafficManager.
Require Import Poulet4.P4light.Semantics.Typing.ValueTyping.
Require Import ProD3.core.Tofino.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation P4Type := (@P4Type Info).
Notation packet := (list bool).
Notation fundef := (@fundef Info).

Section Pipeline.

  Variable ge : (@genv _ target).

  Inductive programmable_block :
    path -> ident -> fundef -> Prop :=
  | programmable_block_intro:
    forall name fd pipe_class_name pipe_inst_path pipe_targs class_name inst_path targs,
      PathMap.get ["main"; "pipe0"] (ge_inst ge) =
        Some {|iclass:=pipe_class_name;
               ipath:=pipe_inst_path; itargs:=pipe_targs|} ->
      PathMap.get (pipe_inst_path ++ [name]) (ge_inst ge) =
        Some {|iclass:=class_name; ipath:=inst_path; itargs:=targs|} ->
      PathMap.get ([class_name; "apply"]) (ge_func ge) = Some fd ->
      programmable_block inst_path name fd.

  Definition programmable_block_sem :=
    extern_state -> list Sval -> extern_state -> list Sval -> signal -> Prop.

  (*
  Inductive ingress_pipeline:
    extern_state -> packet_in -> extern_state -> packet_out -> Sval -> Prop :=
  | ingress_pipeline_intro:
    forall inprsr_path inprsr ingress_path ingress indeprsr_path indeprsr pin pout
      m1 m2 m3 m4 m5 m6 s0 s1 s2 s3 s4
      hdr1 hdr2 hdr3 ig_md1 ig_md2
      payload ig_intr_md ig_intr_md_from_prsr1 ig_intr_md_for_dprsr1
      ig_intr_md_for_dprsr2 ig_intr_md_for_tm1 ig_intr_md_for_tm2,
      PathMap.set ["packet_out"] (ObjPout [])
        (PathMap.set ["packet_in"] (ObjPin pin) s0) = s1 ->
      programmable_block inprsr_path "ingress_parser" inprsr ->
      exec_func ge read_ndetbit inprsr_path (m1, s1) inprsr nil [] (m2, s2)
        [hdr1; ig_md1; ig_intr_md; ig_intr_md_for_tm1; ig_intr_md_from_prsr1]
        SReturnNull ->
      PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
      programmable_block ingress_path "ingress" ingress ->
      exec_func ge read_ndetbit ingress_path (m3, s2) ingress []
        [hdr1; ig_md1; ig_intr_md; ig_intr_md_from_prsr1; ig_intr_md_for_dprsr1;
         ig_intr_md_for_tm1] (m4, s3)
        [hdr2; ig_md2; ig_intr_md_for_dprsr2; ig_intr_md_for_tm2] SReturnNull ->
      programmable_block indeprsr_path "ingress_deparser" indeprsr ->
      exec_func ge read_ndetbit indeprsr_path (m5, s3) indeprsr nil
        [hdr2; ig_md2; ig_intr_md_for_dprsr2; ig_intr_md] (m6, s4) [hdr3]
        SReturnNull ->
      PathMap.get ["packet_out"] s4 = Some (ObjPout pout) ->
      ingress_pipeline s0 pin s4 (pout ++ payload) ig_intr_md_for_tm2.

  Inductive egress_pipeline:
    extern_state -> packet_in -> extern_state -> packet_out -> Prop :=
  | egress_pipeline_intro:
    forall eprsr_path eprsr egress_path egress edeprsr_path edeprsr pin pout
      m1 m2 m3 m4 m5 m6 s0 s1 s2 s3 s4 hdr1 hdr2 hdr3 hdr4 eg_md1 eg_md2 eg_intr_md
      eg_intr_md_from_prsr payload eg_intr_md_for_dprsr1 eg_intr_md_for_dprsr2
      eg_intr_md_for_oport1 eg_intr_md_for_oport2,
      PathMap.set ["packet_out"] (ObjPout [])
        (PathMap.set ["packet_in"] (ObjPin pin) s0) = s1 ->
      programmable_block eprsr_path "ingress_parser" eprsr ->
      exec_func ge read_ndetbit eprsr_path (m1, s1) eprsr nil [] (m2, s2)
        [hdr1; eg_md1; eg_intr_md; eg_intr_md_from_prsr] SReturnNull ->
      PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
      programmable_block egress_path "ingress" egress ->
      exec_func ge read_ndetbit egress_path (m3, s2) egress nil
        [hdr1; eg_md1; eg_intr_md; eg_intr_md_from_prsr; eg_intr_md_for_dprsr1;
         eg_intr_md_for_oport1] (m4, s3)
        [hdr2; eg_md2; eg_intr_md_for_dprsr2; eg_intr_md_for_oport2] SReturnNull ->
      programmable_block edeprsr_path "ingress" edeprsr ->
      exec_func ge read_ndetbit edeprsr_path (m5, s3) edeprsr nil
        [hdr3; eg_md2; eg_intr_md_for_dprsr2; eg_intr_md; eg_intr_md_from_prsr]
        (m6, s4) [hdr4] SReturnNull ->
      PathMap.get ["packet_out"] s4 = Some (ObjPout pout) ->
      egress_pipeline s0 pin s4 (pout ++ payload).
*)

End Pipeline.

Inductive ingress_pipeline (inprsr ingress indeprsr: programmable_block_sem)
  (parser_ingress_cond ingress_deprsr_cond: list Sval -> list Sval -> Prop)
  (ingress_tm_cond: list Sval -> Sval -> Prop):
  extern_state -> packet_in -> extern_state -> packet_out -> Sval -> Prop :=
| ingress_pipeline_intro:
  forall pin pout s0 s1 s2 s3 s4 hdr1 hdr2 hdr3 ig_md1 ig_md2 payload
    rest1 rest2 rest3 rest4 for_tm,
    PathMap.set ["packet_out"] (ObjPout [])
      (PathMap.set ["packet_in"] (ObjPin pin) s0) = s1 ->
    inprsr s1 [] s2 (hdr1 :: ig_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_ingress_cond rest1 rest2 ->
    ingress s2 (hdr1 :: ig_md1 :: rest2) s3 (hdr2 :: ig_md2 :: rest3) SReturnNull ->
    ingress_deprsr_cond rest3 rest4 ->
    indeprsr s3 (hdr2 :: ig_md2 :: rest4) s4 [hdr3] SReturnNull ->
    PathMap.get ["packet_out"] s4 = Some (ObjPout pout) ->
    ingress_tm_cond rest3 for_tm ->
    ingress_pipeline inprsr ingress indeprsr parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond s0 pin s4 (pout ++ payload) for_tm.

Inductive egress_pipeline (eprsr egress edeprsr: programmable_block_sem)
  (parser_egress_cond egress_deprsr_cond: list Sval -> list Sval -> Prop) :
  extern_state -> packet_in -> extern_state -> packet_out -> Prop :=
| egress_pipeline_intro:
  forall pin pout s0 s1 s2 s3 s4 hdr1 hdr2 hdr3 hdr4 eg_md1 eg_md2 payload
    rest1 rest2 rest3 rest4,
    PathMap.set ["packet_out"] (ObjPout [])
      (PathMap.set ["packet_in"] (ObjPin pin) s0) = s1 ->
    eprsr s1 [] s2 (hdr1 :: eg_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_egress_cond rest1 rest2 ->
    egress s2 (hdr1 :: eg_md1 :: rest2) s3 (hdr2 :: eg_md2 :: rest3) SReturnNull ->
    egress_deprsr_cond rest3 rest4 ->
    edeprsr s3 (hdr3 :: eg_md2 :: rest4) s4 [hdr4] SReturnNull ->
    PathMap.get ["packet_out"] s4 = Some (ObjPout pout) ->
    egress_pipeline eprsr egress edeprsr parser_egress_cond egress_deprsr_cond
      s0 pin s4 (pout ++ payload).
