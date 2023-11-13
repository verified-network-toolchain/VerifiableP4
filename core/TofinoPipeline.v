Require Import Poulet4.P4light.Syntax.P4defs.
Require Import Poulet4.P4light.Semantics.Semantics.
Require Import ProD3.core.Core.
Require Import Poulet4.P4light.Architecture.Tofino.
Require Import Poulet4.P4light.Architecture.Queue.
Require Import Poulet4.P4light.Semantics.Typing.ValueTyping.
Require Import ProD3.core.Tofino.

Notation ident := string.
Notation path := (list ident).
Notation Val := (@ValueBase bool).
Notation Sval := (@ValueBase (option bool)).
Notation P4Type := (@P4Type Info).
Notation packet := (list bool).
Notation fundef := (@fundef Info).

Inductive programmable_block (ge : (@genv _ target)):
  path -> ident -> fundef -> Prop :=
| programmable_block_intro:
  forall name fd pipe_class_name pipe_inst_path pipe_targs class_name inst_path targs,
    PathMap.get ["main"; "pipe0"] (ge_inst ge) =
      Some {|iclass:=pipe_class_name;
             ipath:=pipe_inst_path; itargs:=pipe_targs|} ->
    PathMap.get (pipe_inst_path ++ [name]) (ge_inst ge) =
      Some {|iclass:=class_name; ipath:=inst_path; itargs:=targs|} ->
    PathMap.get ([class_name; "apply"]) (ge_func ge) = Some fd ->
    programmable_block ge inst_path name fd.

Definition programmable_block_sem :=
  extern_state -> list Sval -> extern_state -> list Sval -> signal -> Prop.

Record pipeline_state := mkPipeSt {
    parser_state: extern_state;
    control_state: extern_state;
    deparser_state: extern_state;
  }.

Inductive ingress_pipeline (inprsr ingress indeprsr: programmable_block_sem)
  (parser_ingress_cond ingress_deprsr_cond: list Sval -> list Sval -> Prop)
  (ingress_tm_cond: list Sval -> Sval -> Prop):
  pipeline_state -> packet -> pipeline_state -> packet -> Sval -> Prop :=
| ingress_pipeline_intro:
  forall pin pout s1 s2 s3 s4 s5 s6 hdr1 hdr2 hdr3 ig_md1 ig_md2 payload
    rest1 rest2 rest3 rest4 for_tm,
    inprsr (PathMap.set ["packet_in"] (ObjPin pin) s1) []
      s2 (hdr1 :: ig_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_ingress_cond rest1 rest2 ->
    ingress s3 (hdr1 :: ig_md1 :: rest2) s4 (hdr2 :: ig_md2 :: rest3) SReturnNull ->
    ingress_deprsr_cond rest3 rest4 ->
    indeprsr (PathMap.set ["packet_out"] (ObjPout []) s5)
      (hdr2 :: ig_md2 :: rest4) s6 [hdr3] SReturnNull ->
    PathMap.get ["packet_out"] s6 = Some (ObjPout pout) ->
    ingress_tm_cond rest3 for_tm ->
    ingress_pipeline inprsr ingress indeprsr parser_ingress_cond
      ingress_deprsr_cond ingress_tm_cond (mkPipeSt s1 s3 s5) pin
      (mkPipeSt s2 s4 s6) (pout ++ payload) for_tm.

Inductive egress_pipeline (eprsr egress edeprsr: programmable_block_sem)
  (parser_egress_cond egress_deprsr_cond: list Sval -> list Sval -> Prop) :
  pipeline_state -> packet -> pipeline_state -> packet -> Prop :=
| egress_pipeline_intro:
  forall pin pout s1 s2 s3 s4 s5 s6 hdr1 hdr2 hdr3 eg_md1 eg_md2 payload
    rest1 rest2 rest3 rest4,
    eprsr (PathMap.set ["packet_in"] (ObjPin pin) s1) [] s2
      (hdr1 :: eg_md1 :: rest1) SReturnNull ->
    PathMap.get ["packet_in"] s2 = Some (ObjPin payload) ->
    parser_egress_cond rest1 rest2 ->
    egress s3 (hdr1 :: eg_md1 :: rest2) s4 (hdr2 :: eg_md2 :: rest3) SReturnNull ->
    egress_deprsr_cond rest3 rest4 ->
    edeprsr (PathMap.set ["packet_out"] (ObjPout []) s5)
      (hdr2 :: eg_md2 :: rest4) s6 [hdr3] SReturnNull ->
    PathMap.get ["packet_out"] s6 = Some (ObjPout pout) ->
    egress_pipeline eprsr egress edeprsr parser_egress_cond egress_deprsr_cond
      (mkPipeSt s1 s3 s5) pin (mkPipeSt s2 s4 s6) (pout ++ payload).

Section SWITCH.

  Variable ingress_pipe: pipeline_state -> packet -> pipeline_state -> packet -> Sval -> Prop.
  Variable egress_pipe: pipeline_state -> packet -> pipeline_state -> packet -> Prop.
  Variable traffic_manager: Sval -> packet -> queue packet.

  Inductive process_ingress_packets :
    pipeline_state -> queue packet -> pipeline_state -> queue packet -> Prop :=
  | pip_nil: forall st, process_ingress_packets st empty_queue st empty_queue
  | pip_enque: forall st1 ps ps' md st2 p p' st3,
      process_ingress_packets st1 ps st2 ps' ->
      ingress_pipe st2 p st3 p' md ->
      process_ingress_packets st1 (enque p ps) st3 (concat_queue ps' (traffic_manager md p')).

  Inductive process_egress_packets :
    pipeline_state -> queue packet -> pipeline_state -> queue packet -> Prop :=
  | pep_nil: forall st, process_egress_packets st empty_queue st empty_queue
  | pep_enque: forall st1 ps ps' st2 p p' st3,
      process_egress_packets st1 ps st2 ps' ->
      egress_pipe st2 p st3 p' ->
      process_egress_packets st1 (enque p ps) st3 (enque p' ps').

End SWITCH.
