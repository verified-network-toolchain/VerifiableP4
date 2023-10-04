Require Import Poulet4.P4light.Syntax.P4defs.
Open Scope string_scope.

Import ListNotations.

Definition decl'1 := DeclError NoInfo
    [{| stags := NoInfo; str := "NoError" |};
     {| stags := NoInfo; str := "PacketTooShort" |};
     {| stags := NoInfo; str := "NoMatch" |};
     {| stags := NoInfo; str := "StackOutOfBounds" |};
     {| stags := NoInfo; str := "HeaderTooShort" |};
     {| stags := NoInfo; str := "ParserTimeout" |};
     {| stags := NoInfo; str := "ParserInvalidArgument" |}].

Definition packet_in := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_in" |} nil
    [(ProtoMethod NoInfo (TypBit 32%N) {| stags := NoInfo; str := "length" |}
          nil nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "advance" |} nil
          [(MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "sizeInBits" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T1" |})
          {| stags := NoInfo; str := "lookahead" |}
          [{| stags := NoInfo; str := "T1" |}] nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T0" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T0" |}) None
                {| stags := NoInfo; str := "variableSizeHeader" |});
           (MkParameter false In (TypBit 32%N) None
                {| stags := NoInfo; str := "variableFieldSizeInBits" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "extract" |}
          [{| stags := NoInfo; str := "T" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T" |}) None
                {| stags := NoInfo; str := "hdr" |})])].

Definition packet_out := DeclExternObject NoInfo
    {| stags := NoInfo; str := "packet_out" |} nil
    [(ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T2" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T2" |}) None
                {| stags := NoInfo; str := "hdr" |})])].

Definition verify'check'toSignal := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "verify" |} nil
    [(MkParameter false In TypBool None
          {| stags := NoInfo; str := "check" |});
     (MkParameter false In TypError None
          {| stags := NoInfo; str := "toSignal" |})].

Definition NoAction := DeclAction NoInfo
    {| stags := NoInfo; str := "NoAction" |} nil nil (BlockEmpty NoInfo).

Definition decl'2 := DeclMatchKind NoInfo
    [{| stags := NoInfo; str := "exact" |};
     {| stags := NoInfo; str := "ternary" |};
     {| stags := NoInfo; str := "lpm" |}].

Definition PortId_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "PortId_t" |} (inl (TypBit 9%N)).

Definition MulticastGroupId_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "MulticastGroupId_t" |} (inl (TypBit 16%N)).

Definition QueueId_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "QueueId_t" |} (inl (TypBit 5%N)).

Definition MirrorType_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "MirrorType_t" |} (inl (TypBit 3%N)).

Definition MirrorId_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "MirrorId_t" |} (inl (TypBit 10%N)).

Definition ResubmitType_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ResubmitType_t" |} (inl (TypBit 3%N)).

Definition DigestType_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "DigestType_t" |} (inl (TypBit 3%N)).

Definition ReplicationId_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ReplicationId_t" |} (inl (TypBit 16%N)).

Definition ParserError_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ParserError_t" |} (inl TypError).

Definition PORT_METADATA_SIZE := DeclConstant NoInfo (TypBit 32%N)
    {| stags := NoInfo; str := "PORT_METADATA_SIZE" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 64;
             width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N) In).

Definition PARSER_ERROR_OK := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_OK" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 0;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_NO_MATCH := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_NO_MATCH" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 1;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_PARTIAL_HDR := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_PARTIAL_HDR" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 2;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_CTR_RANGE := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_CTR_RANGE" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 4;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_TIMEOUT_USER := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_TIMEOUT_USER" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 8;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_TIMEOUT_HW := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_TIMEOUT_HW" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 16;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_SRC_EXT := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_SRC_EXT" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 32;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_DST_CONT := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_DST_CONT" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 64;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_PHV_OWNER := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_PHV_OWNER" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 128;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_MULTIWRITE := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_MULTIWRITE" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 256;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_ARAM_MBE := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_ARAM_MBE" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 1024;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition PARSER_ERROR_FCS := DeclConstant NoInfo (TypBit 16%N)
    {| stags := NoInfo; str := "PARSER_ERROR_FCS" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 2048;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition MeterType_t := DeclEnum NoInfo
    {| stags := NoInfo; str := "MeterType_t" |}
    [{| stags := NoInfo; str := "PACKETS" |};
     {| stags := NoInfo; str := "BYTES" |}].

Definition MeterColor_t := DeclSerializableEnum NoInfo
    (TypEnum {| stags := NoInfo; str := "MeterColor_t" |} (Some (TypBit 8%N))
         [{| stags := NoInfo; str := "GREEN" |};
          {| stags := NoInfo; str := "YELLOW" |};
          {| stags := NoInfo; str := "RED" |}])
    {| stags := NoInfo; str := "MeterColor_t" |}
    [( {| stags := NoInfo; str := "GREEN" |},
       (MkExpression NoInfo
            (ExpInt
             {| itags := NoInfo; value := 0;
                width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In) );
     ( {| stags := NoInfo; str := "YELLOW" |},
       (MkExpression NoInfo
            (ExpInt
             {| itags := NoInfo; value := 1;
                width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In) );
     ( {| stags := NoInfo; str := "RED" |},
       (MkExpression NoInfo
            (ExpInt
             {| itags := NoInfo; value := 3;
                width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In) )].

Definition CounterType_t := DeclEnum NoInfo
    {| stags := NoInfo; str := "CounterType_t" |}
    [{| stags := NoInfo; str := "PACKETS" |};
     {| stags := NoInfo; str := "BYTES" |};
     {| stags := NoInfo; str := "PACKETS_AND_BYTES" |}].

Definition SelectorMode_t := DeclEnum NoInfo
    {| stags := NoInfo; str := "SelectorMode_t" |}
    [{| stags := NoInfo; str := "FAIR" |};
     {| stags := NoInfo; str := "RESILIENT" |}].

Definition HashAlgorithm_t := DeclEnum NoInfo
    {| stags := NoInfo; str := "HashAlgorithm_t" |}
    [{| stags := NoInfo; str := "IDENTITY" |};
     {| stags := NoInfo; str := "RANDOM" |};
     {| stags := NoInfo; str := "CRC8" |};
     {| stags := NoInfo; str := "CRC16" |};
     {| stags := NoInfo; str := "CRC32" |};
     {| stags := NoInfo; str := "CRC64" |};
     {| stags := NoInfo; str := "CUSTOM" |}].

Definition decl'3 := DeclMatchKind NoInfo
    [{| stags := NoInfo; str := "range" |};
     {| stags := NoInfo; str := "selector" |};
     {| stags := NoInfo; str := "atcam_partition_index" |}].

Definition decl'4 := DeclError NoInfo
    [{| stags := NoInfo; str := "CounterRange" |};
     {| stags := NoInfo; str := "Timeout" |};
     {| stags := NoInfo; str := "PhvOwner" |};
     {| stags := NoInfo; str := "MultiWrite" |};
     {| stags := NoInfo; str := "IbufOverflow" |};
     {| stags := NoInfo; str := "IbufUnderflow" |}].

Definition ingress_intrinsic_metadata_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "resubmit_flag" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "_pad1" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "packet_version" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "_pad2" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "PortId_t" |})
          {| stags := NoInfo; str := "ingress_port" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "ingress_mac_tstamp" |})].

Definition ingress_intrinsic_metadata_for_tm_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "ingress_intrinsic_metadata_for_tm_t" |}
    [(MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "PortId_t" |})
          {| stags := NoInfo; str := "ucast_egress_port" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "bypass_egress" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "deflect_on_drop" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "ingress_cos" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "QueueId_t" |})
          {| stags := NoInfo; str := "qid" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "icos_for_copy_to_cpu" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "copy_to_cpu" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "packet_color" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "disable_ucast_cutthru" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "enable_mcast_cutthru" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "MulticastGroupId_t" |})
          {| stags := NoInfo; str := "mcast_grp_a" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "MulticastGroupId_t" |})
          {| stags := NoInfo; str := "mcast_grp_b" |});
     (MkDeclarationField NoInfo (TypBit 13%N)
          {| stags := NoInfo; str := "level1_mcast_hash" |});
     (MkDeclarationField NoInfo (TypBit 13%N)
          {| stags := NoInfo; str := "level2_mcast_hash" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "level1_exclusion_id" |});
     (MkDeclarationField NoInfo (TypBit 9%N)
          {| stags := NoInfo; str := "level2_exclusion_id" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "rid" |})].

Definition ingress_intrinsic_metadata_from_parser_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "ingress_intrinsic_metadata_from_parser_t" |}
    [(MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "global_tstamp" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "global_ver" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "parser_err" |})].

Definition ingress_intrinsic_metadata_for_deparser_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "ingress_intrinsic_metadata_for_deparser_t" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "drop_ctl" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "DigestType_t" |})
          {| stags := NoInfo; str := "digest_type" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ResubmitType_t" |})
          {| stags := NoInfo; str := "resubmit_type" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "MirrorType_t" |})
          {| stags := NoInfo; str := "mirror_type" |})].

Definition egress_intrinsic_metadata_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 7%N)
          {| stags := NoInfo; str := "_pad0" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "PortId_t" |})
          {| stags := NoInfo; str := "egress_port" |});
     (MkDeclarationField NoInfo (TypBit 5%N)
          {| stags := NoInfo; str := "_pad1" |});
     (MkDeclarationField NoInfo (TypBit 19%N)
          {| stags := NoInfo; str := "enq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 6%N)
          {| stags := NoInfo; str := "_pad2" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "enq_congest_stat" |});
     (MkDeclarationField NoInfo (TypBit 14%N)
          {| stags := NoInfo; str := "_pad3" |});
     (MkDeclarationField NoInfo (TypBit 18%N)
          {| stags := NoInfo; str := "enq_tstamp" |});
     (MkDeclarationField NoInfo (TypBit 5%N)
          {| stags := NoInfo; str := "_pad4" |});
     (MkDeclarationField NoInfo (TypBit 19%N)
          {| stags := NoInfo; str := "deq_qdepth" |});
     (MkDeclarationField NoInfo (TypBit 6%N)
          {| stags := NoInfo; str := "_pad5" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "deq_congest_stat" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "app_pool_congest_stat" |});
     (MkDeclarationField NoInfo (TypBit 14%N)
          {| stags := NoInfo; str := "_pad6" |});
     (MkDeclarationField NoInfo (TypBit 18%N)
          {| stags := NoInfo; str := "deq_timedelta" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "egress_rid" |});
     (MkDeclarationField NoInfo (TypBit 7%N)
          {| stags := NoInfo; str := "_pad7" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "egress_rid_first" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "_pad8" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "QueueId_t" |})
          {| stags := NoInfo; str := "egress_qid" |});
     (MkDeclarationField NoInfo (TypBit 5%N)
          {| stags := NoInfo; str := "_pad9" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "egress_cos" |});
     (MkDeclarationField NoInfo (TypBit 7%N)
          {| stags := NoInfo; str := "_pad10" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "deflection_flag" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "pkt_length" |})].

Definition egress_intrinsic_metadata_from_parser_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "egress_intrinsic_metadata_from_parser_t" |}
    [(MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "global_tstamp" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "global_ver" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "parser_err" |})].

Definition egress_intrinsic_metadata_for_deparser_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "egress_intrinsic_metadata_for_deparser_t" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "drop_ctl" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "MirrorType_t" |})
          {| stags := NoInfo; str := "mirror_type" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "coalesce_flush" |});
     (MkDeclarationField NoInfo (TypBit 7%N)
          {| stags := NoInfo; str := "coalesce_length" |})].

Definition egress_intrinsic_metadata_for_output_port_t := DeclStruct NoInfo
    {| stags := NoInfo;
       str := "egress_intrinsic_metadata_for_output_port_t" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "capture_tstamp_on_tx" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "update_delay_on_tx" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "force_tx_error" |})].

Definition pktgen_timer_header_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "pktgen_timer_header_t" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "_pad1" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "pipe_id" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "app_id" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "_pad2" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "batch_id" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "packet_id" |})].

Definition pktgen_port_down_header_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "pktgen_port_down_header_t" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "_pad1" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "pipe_id" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "app_id" |});
     (MkDeclarationField NoInfo (TypBit 15%N)
          {| stags := NoInfo; str := "_pad2" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "PortId_t" |})
          {| stags := NoInfo; str := "port_num" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "packet_id" |})].

Definition pktgen_recirc_header_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "pktgen_recirc_header_t" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "_pad1" |});
     (MkDeclarationField NoInfo (TypBit 2%N)
          {| stags := NoInfo; str := "pipe_id" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "app_id" |});
     (MkDeclarationField NoInfo (TypBit 24%N)
          {| stags := NoInfo; str := "key" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "packet_id" |})].

Definition ptp_metadata_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "ptp_metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "udp_cksum_byte_offset" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "cf_byte_offset" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "updated_cf" |})].

Definition Checksum := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Checksum" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Checksum" |} nil);
     (ProtoMethod NoInfo (TypBit 16%N) {| stags := NoInfo; str := "update" |}
          [{| stags := NoInfo; str := "T6" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T6" |}) None
                {| stags := NoInfo; str := "data" |});
           (MkParameter true In TypBool None
                {| stags := NoInfo; str := "zeros_as_ones" |})]);
     (ProtoMethod NoInfo (TypBit 16%N) {| stags := NoInfo; str := "get" |}
          nil nil);
     (ProtoMethod NoInfo TypVoid
          {| stags := NoInfo; str := "subtract_all_and_deposit" |}
          [{| stags := NoInfo; str := "T5" |}]
          [(MkParameter false Out
                (TypTypeName {| stags := NoInfo; str := "T5" |}) None
                {| stags := NoInfo; str := "residual" |})]);
     (ProtoMethod NoInfo TypBool {| stags := NoInfo; str := "verify" |} nil
          nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "subtract" |}
          [{| stags := NoInfo; str := "T4" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T4" |}) None
                {| stags := NoInfo; str := "data" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "add" |}
          [{| stags := NoInfo; str := "T3" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T3" |}) None
                {| stags := NoInfo; str := "data" |})])].

Definition ParserCounter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "ParserCounter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "ParserCounter" |}
          nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "decrement" |}
          nil
          [(MkParameter false In (TypBit 8%N) None
                {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "increment" |}
          nil
          [(MkParameter false In (TypBit 8%N) None
                {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo TypBool {| stags := NoInfo; str := "is_negative" |}
          nil nil);
     (ProtoMethod NoInfo TypBool {| stags := NoInfo; str := "is_zero" |} nil
          nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "set" |}
          [{| stags := NoInfo; str := "T8" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T8" |}) None
                {| stags := NoInfo; str := "field" |});
           (MkParameter false In (TypBit 8%N) None
                {| stags := NoInfo; str := "max" |});
           (MkParameter false In (TypBit 8%N) None
                {| stags := NoInfo; str := "rotate" |});
           (MkParameter false In (TypBit 3%N) None
                {| stags := NoInfo; str := "mask" |});
           (MkParameter false In (TypBit 8%N) None
                {| stags := NoInfo; str := "add" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "set" |}
          [{| stags := NoInfo; str := "T7" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T7" |}) None
                {| stags := NoInfo; str := "value" |})])].

Definition ParserPriority := DeclExternObject NoInfo
    {| stags := NoInfo; str := "ParserPriority" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "ParserPriority" |}
          nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "set" |} nil
          [(MkParameter false In (TypBit 3%N) None
                {| stags := NoInfo; str := "prio" |})])].

Definition CRCPolynomial := DeclExternObject NoInfo
    {| stags := NoInfo; str := "CRCPolynomial" |}
    [{| stags := NoInfo; str := "T9" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "CRCPolynomial" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T9" |}) None
                {| stags := NoInfo; str := "coeff" |});
           (MkParameter false Directionless TypBool None
                {| stags := NoInfo; str := "reversed" |});
           (MkParameter false Directionless TypBool None
                {| stags := NoInfo; str := "msb" |});
           (MkParameter false Directionless TypBool None
                {| stags := NoInfo; str := "extended" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T9" |}) None
                {| stags := NoInfo; str := "init" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T9" |}) None
                {| stags := NoInfo; str := "xor" |})])].

Definition Hash := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Hash" |} [{| stags := NoInfo; str := "W" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Hash" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "HashAlgorithm_t" |})
                None {| stags := NoInfo; str := "algo" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName
                      {| stags := NoInfo; str := "CRCPolynomial" |})
                     [(TypTypeName {| stags := NoInfo; str := "__wild" |})])
                None {| stags := NoInfo; str := "poly" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Hash" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "HashAlgorithm_t" |})
                None {| stags := NoInfo; str := "algo" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "W" |})
          {| stags := NoInfo; str := "get" |}
          [{| stags := NoInfo; str := "D" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "D" |}) None
                {| stags := NoInfo; str := "data" |})])].

Definition Random := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Random" |}
    [{| stags := NoInfo; str := "W10" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Random" |} nil);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "W10" |})
          {| stags := NoInfo; str := "get" |} nil nil)].

Definition max't1't2 := DeclExternFunction NoInfo
    (TypTypeName {| stags := NoInfo; str := "T11" |})
    {| stags := NoInfo; str := "max" |} [{| stags := NoInfo; str := "T11" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "T11" |})
          None {| stags := NoInfo; str := "t1" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T11" |})
          None {| stags := NoInfo; str := "t2" |})].

Definition min't1't2 := DeclExternFunction NoInfo
    (TypTypeName {| stags := NoInfo; str := "T12" |})
    {| stags := NoInfo; str := "min" |} [{| stags := NoInfo; str := "T12" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "T12" |})
          None {| stags := NoInfo; str := "t1" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T12" |})
          None {| stags := NoInfo; str := "t2" |})].

Definition funnel_shift_right'dst'src1'src2'shift_amount := DeclExternFunction
    NoInfo TypVoid {| stags := NoInfo; str := "funnel_shift_right" |}
    [{| stags := NoInfo; str := "T13" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "T13" |}) None
          {| stags := NoInfo; str := "dst" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T13" |})
          None {| stags := NoInfo; str := "src1" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "T13" |})
          None {| stags := NoInfo; str := "src2" |});
     (MkParameter false Directionless TypInteger None
          {| stags := NoInfo; str := "shift_amount" |})].

Definition invalidate'field := DeclExternFunction NoInfo TypVoid
    {| stags := NoInfo; str := "invalidate" |}
    [{| stags := NoInfo; str := "T14" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "T14" |})
          None {| stags := NoInfo; str := "field" |})].

Definition port_metadata_unpack'pkt := DeclExternFunction NoInfo
    (TypTypeName {| stags := NoInfo; str := "T15" |})
    {| stags := NoInfo; str := "port_metadata_unpack" |}
    [{| stags := NoInfo; str := "T15" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |})].

Definition sizeInBits'h := DeclExternFunction NoInfo (TypBit 32%N)
    {| stags := NoInfo; str := "sizeInBits" |}
    [{| stags := NoInfo; str := "H" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "H" |})
          None {| stags := NoInfo; str := "h" |})].

Definition sizeInBytes'h := DeclExternFunction NoInfo (TypBit 32%N)
    {| stags := NoInfo; str := "sizeInBytes" |}
    [{| stags := NoInfo; str := "H16" |}]
    [(MkParameter false In (TypTypeName {| stags := NoInfo; str := "H16" |})
          None {| stags := NoInfo; str := "h" |})].

Definition Counter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Counter" |}
    [{| stags := NoInfo; str := "W17" |}; {| stags := NoInfo; str := "I" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Counter" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "CounterType_t" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I" |}) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})])].

Definition DirectCounter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectCounter" |}
    [{| stags := NoInfo; str := "W18" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectCounter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "CounterType_t" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "count" |} nil
          [(MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})])].

Definition Meter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Meter" |}
    [{| stags := NoInfo; str := "I19" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Meter" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType_t" |})
                None {| stags := NoInfo; str := "type" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "red" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "yellow" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "green" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Meter" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType_t" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I19" |}) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I19" |}) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "MeterColor_t" |})
                None {| stags := NoInfo; str := "color" |});
           (MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})])].

Definition DirectMeter := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectMeter" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectMeter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType_t" |})
                None {| stags := NoInfo; str := "type" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "red" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "yellow" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "green" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectMeter" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MeterType_t" |})
                None {| stags := NoInfo; str := "type" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "MeterColor_t" |})
                None {| stags := NoInfo; str := "color" |});
           (MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "adjust_byte_count" |})])].

Definition Lpf := DeclExternObject NoInfo {| stags := NoInfo; str := "Lpf" |}
    [{| stags := NoInfo; str := "T20" |};
     {| stags := NoInfo; str := "I21" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Lpf" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T20" |})
          {| stags := NoInfo; str := "execute" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T20" |}) None
                {| stags := NoInfo; str := "val" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I21" |}) None
                {| stags := NoInfo; str := "index" |})])].

Definition DirectLpf := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectLpf" |}
    [{| stags := NoInfo; str := "T22" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectLpf" |} nil);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T22" |})
          {| stags := NoInfo; str := "execute" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T22" |}) None
                {| stags := NoInfo; str := "val" |})])].

Definition Wred := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Wred" |}
    [{| stags := NoInfo; str := "T23" |};
     {| stags := NoInfo; str := "I24" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Wred" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "drop_value" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "no_drop_value" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T23" |}) None
                {| stags := NoInfo; str := "val" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I24" |}) None
                {| stags := NoInfo; str := "index" |})])].

Definition DirectWred := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectWred" |}
    [{| stags := NoInfo; str := "T25" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectWred" |}
          [(MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "drop_value" |});
           (MkParameter false Directionless (TypBit 8%N) None
                {| stags := NoInfo; str := "no_drop_value" |})]);
     (ProtoMethod NoInfo (TypBit 8%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T25" |}) None
                {| stags := NoInfo; str := "val" |})])].

Definition Register := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Register" |}
    [{| stags := NoInfo; str := "T26" |};
     {| stags := NoInfo; str := "I27" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Register" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T26" |}) None
                {| stags := NoInfo; str := "initial_value" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Register" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "write" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I27" |}) None
                {| stags := NoInfo; str := "index" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T26" |}) None
                {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T26" |})
          {| stags := NoInfo; str := "read" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I27" |}) None
                {| stags := NoInfo; str := "index" |})])].

Definition DirectRegister := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectRegister" |}
    [{| stags := NoInfo; str := "T28" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectRegister" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T28" |}) None
                {| stags := NoInfo; str := "initial_value" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "DirectRegister" |}
          nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "write" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T28" |}) None
                {| stags := NoInfo; str := "value" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T28" |})
          {| stags := NoInfo; str := "read" |} nil nil)].

Definition RegisterParam := DeclExternObject NoInfo
    {| stags := NoInfo; str := "RegisterParam" |}
    [{| stags := NoInfo; str := "T29" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "RegisterParam" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "T29" |}) None
                {| stags := NoInfo; str := "initial_value" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T29" |})
          {| stags := NoInfo; str := "read" |} nil nil)].

Definition MathOp_t := DeclEnum NoInfo
    {| stags := NoInfo; str := "MathOp_t" |}
    [{| stags := NoInfo; str := "MUL" |};
     {| stags := NoInfo; str := "SQR" |};
     {| stags := NoInfo; str := "SQRT" |};
     {| stags := NoInfo; str := "DIV" |};
     {| stags := NoInfo; str := "RSQR" |};
     {| stags := NoInfo; str := "RSQRT" |}].

Definition MathUnit := DeclExternObject NoInfo
    {| stags := NoInfo; str := "MathUnit" |}
    [{| stags := NoInfo; str := "T30" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "MathUnit" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MathOp_t" |})
                None {| stags := NoInfo; str := "op" |});
           (MkParameter false Directionless TypInteger None
                {| stags := NoInfo; str := "A" |});
           (MkParameter false Directionless TypInteger None
                {| stags := NoInfo; str := "B" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "MathUnit" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MathOp_t" |})
                None {| stags := NoInfo; str := "op" |});
           (MkParameter false Directionless TypInteger None
                {| stags := NoInfo; str := "factor" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "MathUnit" |}
          [(MkParameter false Directionless TypBool None
                {| stags := NoInfo; str := "invert" |});
           (MkParameter false Directionless (TypInt 2%N) None
                {| stags := NoInfo; str := "shift" |});
           (MkParameter false Directionless (TypInt 6%N) None
                {| stags := NoInfo; str := "scale" |});
           (MkParameter false Directionless
                (TypTuple
                 [(TypBit 8%N); (TypBit 8%N); (TypBit 8%N); (TypBit 8%N);
                  (TypBit 8%N); (TypBit 8%N); (TypBit 8%N); (TypBit 8%N);
                  (TypBit 8%N); (TypBit 8%N); (TypBit 8%N); (TypBit 8%N);
                  (TypBit 8%N); (TypBit 8%N); (TypBit 8%N); (TypBit 8%N)])
                None {| stags := NoInfo; str := "data" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "T30" |})
          {| stags := NoInfo; str := "execute" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T30" |}) None
                {| stags := NoInfo; str := "x" |})])].

Definition RegisterAction := DeclExternObject NoInfo
    {| stags := NoInfo; str := "RegisterAction" |}
    [{| stags := NoInfo; str := "T31" |};
     {| stags := NoInfo; str := "I32" |}; {| stags := NoInfo; str := "U" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "RegisterAction" |}
          [(MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Register" |})
                     [(TypTypeName {| stags := NoInfo; str := "T31" |});
                      (TypTypeName {| stags := NoInfo; str := "I32" |})])
                None {| stags := NoInfo; str := "reg" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "U" |})
          {| stags := NoInfo; str := "predicate" |} nil
          [(MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmplo" |});
           (MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmphi" |})]);
     (ProtoAbstractMethod NoInfo TypVoid
          {| stags := NoInfo; str := "apply" |} nil
          [(MkParameter false InOut
                (TypTypeName {| stags := NoInfo; str := "T31" |}) None
                {| stags := NoInfo; str := "value" |});
           (MkParameter true Out
                (TypTypeName {| stags := NoInfo; str := "U" |}) None
                {| stags := NoInfo; str := "rv" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "U" |})
          {| stags := NoInfo; str := "execute_log" |} nil nil);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "U" |})
          {| stags := NoInfo; str := "execute" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "I32" |}) None
                {| stags := NoInfo; str := "index" |})])].

Definition DirectRegisterAction := DeclExternObject NoInfo
    {| stags := NoInfo; str := "DirectRegisterAction" |}
    [{| stags := NoInfo; str := "T33" |};
     {| stags := NoInfo; str := "U34" |}]
    [(ProtoConstructor NoInfo
          {| stags := NoInfo; str := "DirectRegisterAction" |}
          [(MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName
                      {| stags := NoInfo; str := "DirectRegister" |})
                     [(TypTypeName {| stags := NoInfo; str := "T33" |})])
                None {| stags := NoInfo; str := "reg" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "U34" |})
          {| stags := NoInfo; str := "predicate" |} nil
          [(MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmplo" |});
           (MkParameter true In TypBool None
                {| stags := NoInfo; str := "cmphi" |})]);
     (ProtoAbstractMethod NoInfo TypVoid
          {| stags := NoInfo; str := "apply" |} nil
          [(MkParameter false InOut
                (TypTypeName {| stags := NoInfo; str := "T33" |}) None
                {| stags := NoInfo; str := "value" |});
           (MkParameter true Out
                (TypTypeName {| stags := NoInfo; str := "U34" |}) None
                {| stags := NoInfo; str := "rv" |})]);
     (ProtoMethod NoInfo (TypTypeName {| stags := NoInfo; str := "U34" |})
          {| stags := NoInfo; str := "execute" |} nil nil)].

Definition ActionProfile := DeclExternObject NoInfo
    {| stags := NoInfo; str := "ActionProfile" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "ActionProfile" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |})])].

Definition ActionSelector := DeclExternObject NoInfo
    {| stags := NoInfo; str := "ActionSelector" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "ActionSelector" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Hash" |})
                     [(TypTypeName {| stags := NoInfo; str := "__wild77" |})])
                None {| stags := NoInfo; str := "hash" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "SelectorMode_t" |})
                None {| stags := NoInfo; str := "mode" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Register" |})
                     [(TypBit 1%N);
                      (TypTypeName {| stags := NoInfo; str := "__wild78" |})])
                None {| stags := NoInfo; str := "reg" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "ActionSelector" |}
          [(MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "size" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Hash" |})
                     [(TypTypeName {| stags := NoInfo; str := "__wild76" |})])
                None {| stags := NoInfo; str := "hash" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "SelectorMode_t" |})
                None {| stags := NoInfo; str := "mode" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "ActionSelector" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "ActionProfile" |})
                None {| stags := NoInfo; str := "action_profile" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Hash" |})
                     [(TypTypeName {| stags := NoInfo; str := "__wild74" |})])
                None {| stags := NoInfo; str := "hash" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "SelectorMode_t" |})
                None {| stags := NoInfo; str := "mode" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Register" |})
                     [(TypBit 1%N);
                      (TypTypeName {| stags := NoInfo; str := "__wild75" |})])
                None {| stags := NoInfo; str := "reg" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "max_group_size" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "num_groups" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "ActionSelector" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "ActionProfile" |})
                None {| stags := NoInfo; str := "action_profile" |});
           (MkParameter false Directionless
                (TypSpecializedType
                     (TypTypeName {| stags := NoInfo; str := "Hash" |})
                     [(TypTypeName {| stags := NoInfo; str := "__wild73" |})])
                None {| stags := NoInfo; str := "hash" |});
           (MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "SelectorMode_t" |})
                None {| stags := NoInfo; str := "mode" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "max_group_size" |});
           (MkParameter false Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "num_groups" |})])].

Definition SelectorAction := DeclExternObject NoInfo
    {| stags := NoInfo; str := "SelectorAction" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "SelectorAction" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "ActionSelector" |})
                None {| stags := NoInfo; str := "sel" |})]);
     (ProtoAbstractMethod NoInfo TypVoid
          {| stags := NoInfo; str := "apply" |} nil
          [(MkParameter false InOut (TypBit 1%N) None
                {| stags := NoInfo; str := "value" |});
           (MkParameter true Out (TypBit 1%N) None
                {| stags := NoInfo; str := "rv" |})]);
     (ProtoMethod NoInfo (TypBit 1%N) {| stags := NoInfo; str := "execute" |}
          nil
          [(MkParameter true In (TypBit 32%N) None
                {| stags := NoInfo; str := "index" |})])].

Definition Mirror := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Mirror" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Mirror" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "MirrorType_t" |})
                None {| stags := NoInfo; str := "mirror_type" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Mirror" |} nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T35" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "MirrorId_t" |})
                None {| stags := NoInfo; str := "session_id" |});
           (MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T35" |}) None
                {| stags := NoInfo; str := "hdr" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "MirrorId_t" |})
                None {| stags := NoInfo; str := "session_id" |})])].

Definition Resubmit := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Resubmit" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Resubmit" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "ResubmitType_t" |})
                None {| stags := NoInfo; str := "resubmit_type" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Resubmit" |} nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |}
          [{| stags := NoInfo; str := "T36" |}]
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T36" |}) None
                {| stags := NoInfo; str := "hdr" |})]);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "emit" |} nil
          nil)].

Definition Digest := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Digest" |}
    [{| stags := NoInfo; str := "T37" |}]
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Digest" |}
          [(MkParameter false Directionless
                (TypTypeName {| stags := NoInfo; str := "DigestType_t" |})
                None {| stags := NoInfo; str := "digest_type" |})]);
     (ProtoConstructor NoInfo {| stags := NoInfo; str := "Digest" |} nil);
     (ProtoMethod NoInfo TypVoid {| stags := NoInfo; str := "pack" |} nil
          [(MkParameter false In
                (TypTypeName {| stags := NoInfo; str := "T37" |}) None
                {| stags := NoInfo; str := "data" |})])].

Definition Atcam := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Atcam" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Atcam" |}
          [(MkParameter true Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "number_partitions" |})])].

Definition Alpm := DeclExternObject NoInfo
    {| stags := NoInfo; str := "Alpm" |} nil
    [(ProtoConstructor NoInfo {| stags := NoInfo; str := "Alpm" |}
          [(MkParameter true Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "number_partitions" |});
           (MkParameter true Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "subtrees_per_partition" |});
           (MkParameter true Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "atcam_subset_width" |});
           (MkParameter true Directionless (TypBit 32%N) None
                {| stags := NoInfo; str := "shift_granularity" |})])].

Definition IngressParserT := DeclParserType NoInfo
    {| stags := NoInfo; str := "IngressParserT" |}
    [{| stags := NoInfo; str := "H38" |}; {| stags := NoInfo; str := "M" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out (TypTypeName {| stags := NoInfo; str := "H38" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false Out (TypTypeName {| stags := NoInfo; str := "M" |})
          None {| stags := NoInfo; str := "ig_md" |});
     (MkParameter true Out
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |});
     (MkParameter true Out
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_tm_t" |}) None
          {| stags := NoInfo; str := "ig_intr_md_for_tm" |});
     (MkParameter true Out
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "ig_intr_md_from_prsr" |})].

Definition EgressParserT := DeclParserType NoInfo
    {| stags := NoInfo; str := "EgressParserT" |}
    [{| stags := NoInfo; str := "H39" |};
     {| stags := NoInfo; str := "M40" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out (TypTypeName {| stags := NoInfo; str := "H39" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false Out (TypTypeName {| stags := NoInfo; str := "M40" |})
          None {| stags := NoInfo; str := "eg_md" |});
     (MkParameter true Out
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |});
     (MkParameter true Out
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_from_prsr" |})].

Definition IngressT := DeclControlType NoInfo
    {| stags := NoInfo; str := "IngressT" |}
    [{| stags := NoInfo; str := "H41" |};
     {| stags := NoInfo; str := "M42" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H41" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M42" |}) None
          {| stags := NoInfo; str := "ig_md" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "ig_intr_md_from_prsr" |});
     (MkParameter true InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_deparser_t" |})
          None {| stags := NoInfo; str := "ig_intr_md_for_dprsr" |});
     (MkParameter true InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_tm_t" |}) None
          {| stags := NoInfo; str := "ig_intr_md_for_tm" |})].

Definition EgressT := DeclControlType NoInfo
    {| stags := NoInfo; str := "EgressT" |}
    [{| stags := NoInfo; str := "H43" |};
     {| stags := NoInfo; str := "M44" |}]
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H43" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "M44" |}) None
          {| stags := NoInfo; str := "eg_md" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_from_prsr" |});
     (MkParameter true InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_for_dprsr" |});
     (MkParameter true InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_output_port_t" |})
          None {| stags := NoInfo; str := "eg_intr_md_for_oport" |})].

Definition IngressDeparserT := DeclControlType NoInfo
    {| stags := NoInfo; str := "IngressDeparserT" |}
    [{| stags := NoInfo; str := "H45" |};
     {| stags := NoInfo; str := "M46" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H45" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "M46" |})
          None {| stags := NoInfo; str := "metadata" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_deparser_t" |})
          None {| stags := NoInfo; str := "ig_intr_md_for_dprsr" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |})].

Definition EgressDeparserT := DeclControlType NoInfo
    {| stags := NoInfo; str := "EgressDeparserT" |}
    [{| stags := NoInfo; str := "H47" |};
     {| stags := NoInfo; str := "M48" |}]
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "H47" |}) None
          {| stags := NoInfo; str := "hdr" |});
     (MkParameter false In (TypTypeName {| stags := NoInfo; str := "M48" |})
          None {| stags := NoInfo; str := "metadata" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_for_dprsr" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |});
     (MkParameter true In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_from_prsr" |})].

Definition Pipeline := DeclPackageType NoInfo
    {| stags := NoInfo; str := "Pipeline" |}
    [{| stags := NoInfo; str := "IH" |}; {| stags := NoInfo; str := "IM" |};
     {| stags := NoInfo; str := "EH" |}; {| stags := NoInfo; str := "EM" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "IH" |});
                (TypTypeName {| stags := NoInfo; str := "IM" |})]) None
          {| stags := NoInfo; str := "ingress_parser" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressT" |})
               [(TypTypeName {| stags := NoInfo; str := "IH" |});
                (TypTypeName {| stags := NoInfo; str := "IM" |})]) None
          {| stags := NoInfo; str := "ingress" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressDeparserT" |})
               [(TypTypeName {| stags := NoInfo; str := "IH" |});
                (TypTypeName {| stags := NoInfo; str := "IM" |})]) None
          {| stags := NoInfo; str := "ingress_deparser" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "EH" |});
                (TypTypeName {| stags := NoInfo; str := "EM" |})]) None
          {| stags := NoInfo; str := "egress_parser" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressT" |})
               [(TypTypeName {| stags := NoInfo; str := "EH" |});
                (TypTypeName {| stags := NoInfo; str := "EM" |})]) None
          {| stags := NoInfo; str := "egress" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressDeparserT" |})
               [(TypTypeName {| stags := NoInfo; str := "EH" |});
                (TypTypeName {| stags := NoInfo; str := "EM" |})]) None
          {| stags := NoInfo; str := "egress_deparser" |})].

Definition Switch := DeclPackageType NoInfo
    {| stags := NoInfo; str := "Switch" |}
    [{| stags := NoInfo; str := "IH0" |};
     {| stags := NoInfo; str := "IM0" |};
     {| stags := NoInfo; str := "EH0" |};
     {| stags := NoInfo; str := "EM0" |};
     {| stags := NoInfo; str := "IH1" |};
     {| stags := NoInfo; str := "IM1" |};
     {| stags := NoInfo; str := "EH1" |};
     {| stags := NoInfo; str := "EM1" |};
     {| stags := NoInfo; str := "IH2" |};
     {| stags := NoInfo; str := "IM2" |};
     {| stags := NoInfo; str := "EH2" |};
     {| stags := NoInfo; str := "EM2" |};
     {| stags := NoInfo; str := "IH3" |};
     {| stags := NoInfo; str := "IM3" |};
     {| stags := NoInfo; str := "EH3" |};
     {| stags := NoInfo; str := "EM3" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Pipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH0" |});
                (TypTypeName {| stags := NoInfo; str := "IM0" |});
                (TypTypeName {| stags := NoInfo; str := "EH0" |});
                (TypTypeName {| stags := NoInfo; str := "EM0" |})]) None
          {| stags := NoInfo; str := "pipe0" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Pipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH1" |});
                (TypTypeName {| stags := NoInfo; str := "IM1" |});
                (TypTypeName {| stags := NoInfo; str := "EH1" |});
                (TypTypeName {| stags := NoInfo; str := "EM1" |})]) None
          {| stags := NoInfo; str := "pipe1" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Pipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH2" |});
                (TypTypeName {| stags := NoInfo; str := "IM2" |});
                (TypTypeName {| stags := NoInfo; str := "EH2" |});
                (TypTypeName {| stags := NoInfo; str := "EM2" |})]) None
          {| stags := NoInfo; str := "pipe2" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Pipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH3" |});
                (TypTypeName {| stags := NoInfo; str := "IM3" |});
                (TypTypeName {| stags := NoInfo; str := "EH3" |});
                (TypTypeName {| stags := NoInfo; str := "EM3" |})]) None
          {| stags := NoInfo; str := "pipe3" |})].

Definition IngressParsers := DeclPackageType NoInfo
    {| stags := NoInfo; str := "IngressParsers" |}
    [{| stags := NoInfo; str := "H49" |};
     {| stags := NoInfo; str := "M50" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr0" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr1" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr2" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr3" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr4" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr5" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr6" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr7" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr8" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr9" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr10" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr11" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr12" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr13" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr14" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr15" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr16" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H49" |});
                (TypTypeName {| stags := NoInfo; str := "M50" |})]) None
          {| stags := NoInfo; str := "prsr17" |})].

Definition EgressParsers := DeclPackageType NoInfo
    {| stags := NoInfo; str := "EgressParsers" |}
    [{| stags := NoInfo; str := "H51" |};
     {| stags := NoInfo; str := "M52" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr0" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr1" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr2" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr3" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr4" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr5" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr6" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr7" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr8" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr9" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr10" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr11" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr12" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr13" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr14" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr15" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr16" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParserT" |})
               [(TypTypeName {| stags := NoInfo; str := "H51" |});
                (TypTypeName {| stags := NoInfo; str := "M52" |})]) None
          {| stags := NoInfo; str := "prsr17" |})].

Definition MultiParserPipeline := DeclPackageType NoInfo
    {| stags := NoInfo; str := "MultiParserPipeline" |}
    [{| stags := NoInfo; str := "IH53" |};
     {| stags := NoInfo; str := "IM54" |};
     {| stags := NoInfo; str := "EH55" |};
     {| stags := NoInfo; str := "EM56" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressParsers" |})
               [(TypTypeName {| stags := NoInfo; str := "IH53" |});
                (TypTypeName {| stags := NoInfo; str := "IM54" |})])
          None {| stags := NoInfo; str := "ig_prsr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressT" |})
               [(TypTypeName {| stags := NoInfo; str := "IH53" |});
                (TypTypeName {| stags := NoInfo; str := "IM54" |})])
          None {| stags := NoInfo; str := "ingress" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "IngressDeparserT" |})
               [(TypTypeName {| stags := NoInfo; str := "IH53" |});
                (TypTypeName {| stags := NoInfo; str := "IM54" |})])
          None {| stags := NoInfo; str := "ingress_deparser" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressParsers" |})
               [(TypTypeName {| stags := NoInfo; str := "EH55" |});
                (TypTypeName {| stags := NoInfo; str := "EM56" |})])
          None {| stags := NoInfo; str := "eg_prsr" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressT" |})
               [(TypTypeName {| stags := NoInfo; str := "EH55" |});
                (TypTypeName {| stags := NoInfo; str := "EM56" |})])
          None {| stags := NoInfo; str := "egress" |});
     (MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "EgressDeparserT" |})
               [(TypTypeName {| stags := NoInfo; str := "EH55" |});
                (TypTypeName {| stags := NoInfo; str := "EM56" |})])
          None {| stags := NoInfo; str := "egress_deparser" |})].

Definition MultiParserSwitch := DeclPackageType NoInfo
    {| stags := NoInfo; str := "MultiParserSwitch" |}
    [{| stags := NoInfo; str := "IH057" |};
     {| stags := NoInfo; str := "IM058" |};
     {| stags := NoInfo; str := "EH059" |};
     {| stags := NoInfo; str := "EM060" |};
     {| stags := NoInfo; str := "IH161" |};
     {| stags := NoInfo; str := "IM162" |};
     {| stags := NoInfo; str := "EH163" |};
     {| stags := NoInfo; str := "EM164" |};
     {| stags := NoInfo; str := "IH265" |};
     {| stags := NoInfo; str := "IM266" |};
     {| stags := NoInfo; str := "EH267" |};
     {| stags := NoInfo; str := "EM268" |};
     {| stags := NoInfo; str := "IH369" |};
     {| stags := NoInfo; str := "IM370" |};
     {| stags := NoInfo; str := "EH371" |};
     {| stags := NoInfo; str := "EM372" |}]
    [(MkParameter false Directionless
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "MultiParserPipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH057" |});
                (TypTypeName {| stags := NoInfo; str := "IM058" |});
                (TypTypeName {| stags := NoInfo; str := "EH059" |});
                (TypTypeName {| stags := NoInfo; str := "EM060" |})])
          None {| stags := NoInfo; str := "pipe0" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "MultiParserPipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH161" |});
                (TypTypeName {| stags := NoInfo; str := "IM162" |});
                (TypTypeName {| stags := NoInfo; str := "EH163" |});
                (TypTypeName {| stags := NoInfo; str := "EM164" |})])
          None {| stags := NoInfo; str := "pipe1" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "MultiParserPipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH265" |});
                (TypTypeName {| stags := NoInfo; str := "IM266" |});
                (TypTypeName {| stags := NoInfo; str := "EH267" |});
                (TypTypeName {| stags := NoInfo; str := "EM268" |})])
          None {| stags := NoInfo; str := "pipe2" |});
     (MkParameter true Directionless
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "MultiParserPipeline" |})
               [(TypTypeName {| stags := NoInfo; str := "IH369" |});
                (TypTypeName {| stags := NoInfo; str := "IM370" |});
                (TypTypeName {| stags := NoInfo; str := "EH371" |});
                (TypTypeName {| stags := NoInfo; str := "EM372" |})])
          None {| stags := NoInfo; str := "pipe3" |})].

Definition mac_addr_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "mac_addr_t" |} (inl (TypBit 48%N)).

Definition ipv4_addr_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ipv4_addr_t" |} (inl (TypBit 32%N)).

Definition ipv6_addr_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ipv6_addr_t" |} (inl (TypBit 128%N)).

Definition vlan_id_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "vlan_id_t" |} (inl (TypBit 12%N)).

Definition ether_type_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ether_type_t" |} (inl (TypBit 16%N)).

Definition ETHERTYPE_IPV4 := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ether_type_t" |})
    {| stags := NoInfo; str := "ETHERTYPE_IPV4" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 2048;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition ETHERTYPE_ARP := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ether_type_t" |})
    {| stags := NoInfo; str := "ETHERTYPE_ARP" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 2054;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition ETHERTYPE_IPV6 := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ether_type_t" |})
    {| stags := NoInfo; str := "ETHERTYPE_IPV6" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 34525;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition ETHERTYPE_VLAN := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ether_type_t" |})
    {| stags := NoInfo; str := "ETHERTYPE_VLAN" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 33024;
             width_signed := (Some ( 16%N, false )) |}) (TypBit 16%N) In).

Definition ip_protocol_t := DeclTypeDef NoInfo
    {| stags := NoInfo; str := "ip_protocol_t" |} (inl (TypBit 8%N)).

Definition IP_PROTOCOLS_ICMP := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ip_protocol_t" |})
    {| stags := NoInfo; str := "IP_PROTOCOLS_ICMP" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 1;
             width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In).

Definition IP_PROTOCOLS_TCP := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ip_protocol_t" |})
    {| stags := NoInfo; str := "IP_PROTOCOLS_TCP" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 6;
             width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In).

Definition IP_PROTOCOLS_UDP := DeclConstant NoInfo
    (TypTypeName {| stags := NoInfo; str := "ip_protocol_t" |})
    {| stags := NoInfo; str := "IP_PROTOCOLS_UDP" |}
    (MkExpression NoInfo
         (ExpInt
          {| itags := NoInfo; value := 17;
             width_signed := (Some ( 8%N, false )) |}) (TypBit 8%N) In).

Definition ethernet_h := DeclHeader NoInfo
    {| stags := NoInfo; str := "ethernet_h" |}
    [(MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "mac_addr_t" |})
          {| stags := NoInfo; str := "dst_addr" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "mac_addr_t" |})
          {| stags := NoInfo; str := "src_addr" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "ether_type" |})].

Definition vlan_tag_h := DeclHeader NoInfo
    {| stags := NoInfo; str := "vlan_tag_h" |}
    [(MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "pcp" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "cfi" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "vlan_id_t" |})
          {| stags := NoInfo; str := "vid" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "ether_type" |})].

Definition mpls_h := DeclHeader NoInfo {| stags := NoInfo; str := "mpls_h" |}
    [(MkDeclarationField NoInfo (TypBit 20%N)
          {| stags := NoInfo; str := "label" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "exp" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "bos" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "ttl" |})].

Definition ipv4_h := DeclHeader NoInfo {| stags := NoInfo; str := "ipv4_h" |}
    [(MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "version" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "ihl" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "diffserv" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "total_len" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "identification" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 13%N)
          {| stags := NoInfo; str := "frag_offset" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "ttl" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "protocol" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "hdr_checksum" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv4_addr_t" |})
          {| stags := NoInfo; str := "src_addr" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv4_addr_t" |})
          {| stags := NoInfo; str := "dst_addr" |})].

Definition ipv6_h := DeclHeader NoInfo {| stags := NoInfo; str := "ipv6_h" |}
    [(MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "version" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "traffic_class" |});
     (MkDeclarationField NoInfo (TypBit 20%N)
          {| stags := NoInfo; str := "flow_label" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "payload_len" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "next_hdr" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "hop_limit" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv6_addr_t" |})
          {| stags := NoInfo; str := "src_addr" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv6_addr_t" |})
          {| stags := NoInfo; str := "dst_addr" |})].

Definition tcp_h := DeclHeader NoInfo {| stags := NoInfo; str := "tcp_h" |}
    [(MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "src_port" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "dst_port" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "seq_no" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "ack_no" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "data_offset" |});
     (MkDeclarationField NoInfo (TypBit 4%N)
          {| stags := NoInfo; str := "res" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "window" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "checksum" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "urgent_ptr" |})].

Definition udp_h := DeclHeader NoInfo {| stags := NoInfo; str := "udp_h" |}
    [(MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "src_port" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "dst_port" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "hdr_length" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "checksum" |})].

Definition icmp_h := DeclHeader NoInfo {| stags := NoInfo; str := "icmp_h" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "type_" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "code" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "hdr_checksum" |})].

Definition arp_h := DeclHeader NoInfo {| stags := NoInfo; str := "arp_h" |}
    [(MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "hw_type" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "proto_type" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "hw_addr_len" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "proto_addr_len" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "opcode" |})].

Definition ipv6_srh_h := DeclHeader NoInfo
    {| stags := NoInfo; str := "ipv6_srh_h" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "next_hdr" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "hdr_ext_len" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "routing_type" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "seg_left" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "last_entry" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "tag" |})].

Definition vxlan_h := DeclHeader NoInfo
    {| stags := NoInfo; str := "vxlan_h" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 24%N)
          {| stags := NoInfo; str := "reserved" |});
     (MkDeclarationField NoInfo (TypBit 24%N)
          {| stags := NoInfo; str := "vni" |});
     (MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "reserved2" |})].

Definition gre_h := DeclHeader NoInfo {| stags := NoInfo; str := "gre_h" |}
    [(MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "C" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "R" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "K" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "S" |});
     (MkDeclarationField NoInfo (TypBit 1%N)
          {| stags := NoInfo; str := "s" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "recurse" |});
     (MkDeclarationField NoInfo (TypBit 5%N)
          {| stags := NoInfo; str := "flags" |});
     (MkDeclarationField NoInfo (TypBit 3%N)
          {| stags := NoInfo; str := "version" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "proto" |})].

Definition header_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "header_t" |}
    [(MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ethernet_h" |})
          {| stags := NoInfo; str := "ethernet" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv4_h" |})
          {| stags := NoInfo; str := "ipv4" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "tcp_h" |})
          {| stags := NoInfo; str := "tcp" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "udp_h" |})
          {| stags := NoInfo; str := "udp" |})].

Definition empty_header_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "empty_header_t" |} nil.

Definition empty_metadata_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "empty_metadata_t" |} nil.

Definition TofinoIngressParser := DeclParser NoInfo
    {| stags := NoInfo; str := "TofinoIngressParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "resubmit_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "packet_version" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "ingress_mac_tstamp" |},
                          (TypBit 48%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo; str := "ig_intr_md" |})
                             (LInstance ["ig_intr_md"]))
                            (TypTypeName
                             {| stags := NoInfo;
                                str := "ingress_intrinsic_metadata_t" |})
                            Out))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo; str := "ig_intr_md" |})
                                (LInstance ["ig_intr_md"]))
                               (TypTypeName
                                {| stags := NoInfo;
                                   str := "ingress_intrinsic_metadata_t" |})
                               Out)
                          {| stags := NoInfo; str := "resubmit_flag" |})
                     (TypBit 1%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 1%N)) (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 1;
                                                           width_signed :=
                                                           None |})
                                                       TypInteger
                                                       Directionless))
                           (TypBit 1%N))]
                     {| stags := NoInfo; str := "parse_resubmit" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 1%N)) (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 0;
                                                           width_signed :=
                                                           None |})
                                                       TypInteger
                                                       Directionless))
                           (TypBit 1%N))]
                     {| stags := NoInfo; str := "parse_port_metadata" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_resubmit" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "advance" |})
                          (TypFunction
                           (MkFunctionType nil
                                [(MkParameter false In (TypBit 32%N)
                                      None
                                      {| stags := NoInfo;
                                         str := "sizeInBits" |})] FunExtern
                                TypVoid)) Directionless) nil
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo;
                                 str := "PORT_METADATA_SIZE" |})
                             (LGlobal ["PORT_METADATA_SIZE"])) (TypBit 32%N)
                            Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "reject" |}));
     (MkParserState NoInfo
          {| stags := NoInfo; str := "parse_port_metadata" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "advance" |})
                          (TypFunction
                           (MkFunctionType nil
                                [(MkParameter false In (TypBit 32%N)
                                      None
                                      {| stags := NoInfo;
                                         str := "sizeInBits" |})] FunExtern
                                TypVoid)) Directionless) nil
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo;
                                 str := "PORT_METADATA_SIZE" |})
                             (LGlobal ["PORT_METADATA_SIZE"])) (TypBit 32%N)
                            Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition TofinoEgressParser := DeclParser NoInfo
    {| stags := NoInfo; str := "TofinoEgressParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "_pad0" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "enq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad3" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "enq_tstamp" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "_pad4" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad5" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "deq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo;
                             str := "app_pool_congest_stat" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "_pad6" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "_pad7" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_rid_first" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad8" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "egress_qid" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "_pad9" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "egress_cos" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "_pad10" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "deflection_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "pkt_length" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo; str := "eg_intr_md" |})
                             (LInstance ["eg_intr_md"]))
                            (TypTypeName
                             {| stags := NoInfo;
                                str := "egress_intrinsic_metadata_t" |}) Out))])
                StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition BypassEgress := DeclControl NoInfo
    {| stags := NoInfo; str := "BypassEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_tm_t" |}) None
          {| stags := NoInfo; str := "ig_tm_md" |})] nil
    [(DeclAction NoInfo {| stags := NoInfo; str := "set_bypass_egress" |} nil
          nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "ig_tm_md" |})
                                         (LInstance ["ig_tm_md"]))
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "ingress_intrinsic_metadata_for_tm_t" |})
                                        InOut)
                                   {| stags := NoInfo;
                                      str := "bypass_egress" |}) (TypBit 1%N)
                              Directionless)
                         (MkExpression NoInfo
                              (ExpInt
                               {| itags := NoInfo; value := 1;
                                  width_signed := (Some ( 1%N, false )) |})
                              (TypBit 1%N) Directionless)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclTable NoInfo {| stags := NoInfo; str := "bypass_egress" |} nil
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "set_bypass_egress" |}) nil)
                (TypAction nil nil))] (Some nil)
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName
                      {| stags := NoInfo; str := "set_bypass_egress" |}) nil)
                (TypAction nil nil))) None nil)]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo;
                                       str := "bypass_egress" |})
                                   (LInstance ["bypass_egress"]))
                                  (TypTable
                                   {| stags := NoInfo;
                                      str := "apply_result_bypass_egress" |})
                                  Directionless)
                             {| stags := NoInfo; str := "apply" |})
                        (TypFunction
                         (MkFunctionType nil nil FunTable
                              (TypTypeName
                               {| stags := NoInfo;
                                  str := "apply_result_bypass_egress" |})))
                        Directionless) nil nil) StmUnit) (BlockEmpty NoInfo)).

Definition EmptyEgressParser := DeclParser NoInfo
    {| stags := NoInfo; str := "EmptyEgressParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "empty_header_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "empty_metadata_t" |})
          None {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false Out
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |})] nil nil
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |} nil
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition EmptyEgressDeparser := DeclControl NoInfo
    {| stags := NoInfo; str := "EmptyEgressDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "empty_header_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "empty_metadata_t" |})
          None {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "ig_intr_dprs_md" |})] nil nil
    (BlockEmpty NoInfo).

Definition EmptyEgress := DeclControl NoInfo
    {| stags := NoInfo; str := "EmptyEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "empty_header_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "empty_metadata_t" |})
          None {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_from_prsr" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "ig_intr_dprs_md" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_output_port_t" |})
          None {| stags := NoInfo; str := "eg_intr_oport_md" |})] nil nil
    (BlockEmpty NoInfo).

Definition bridge_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "bridge_t" |}
    [(MkDeclarationField NoInfo (TypBit 8%N)
          {| stags := NoInfo; str := "contains_sample" |})].

Definition sample_t := DeclHeader NoInfo
    {| stags := NoInfo; str := "sample_t" |}
    [(MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "dmac" |});
     (MkDeclarationField NoInfo (TypBit 48%N)
          {| stags := NoInfo; str := "smac" |});
     (MkDeclarationField NoInfo (TypBit 16%N)
          {| stags := NoInfo; str := "etype" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "srcip" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "dstip" |});
     (MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "num_pkts" |})].

Definition header_sample_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "header_sample_t" |}
    [(MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "bridge_t" |})
          {| stags := NoInfo; str := "bridge" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "sample_t" |})
          {| stags := NoInfo; str := "sample" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ethernet_h" |})
          {| stags := NoInfo; str := "ethernet" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "ipv4_h" |})
          {| stags := NoInfo; str := "ipv4" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "tcp_h" |})
          {| stags := NoInfo; str := "tcp" |});
     (MkDeclarationField NoInfo
          (TypTypeName {| stags := NoInfo; str := "udp_h" |})
          {| stags := NoInfo; str := "udp" |})].

Definition metadata_t := DeclStruct NoInfo
    {| stags := NoInfo; str := "metadata_t" |}
    [(MkDeclarationField NoInfo (TypBit 32%N)
          {| stags := NoInfo; str := "num_pkts" |})].

Definition SwitchIngressParser := DeclParser NoInfo
    {| stags := NoInfo; str := "SwitchIngressParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "ig_md" |});
     (MkParameter false Out
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "TofinoIngressParser" |}) nil) nil
          {| stags := NoInfo; str := "tofino_parser" |} nil)]
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo;
                                         str := "tofino_parser" |})
                                     (LInstance ["tofino_parser"]))
                                    (TypParser
                                     (MkControlType nil
                                          [(MkParameter false Directionless
                                                (TypExtern
                                                 {| stags := NoInfo;
                                                    str := "packet_in" |})
                                                None
                                                {| stags := NoInfo;
                                                   str := "pkt" |});
                                           (MkParameter false Out
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "resubmit_flag" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad1" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "packet_version" |},
                                                    (TypBit 2%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad2" |},
                                                    (TypBit 3%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ingress_port" |},
                                                    (TypBit 9%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "ingress_mac_tstamp" |},
                                                    (TypBit 48%N) )])
                                                None
                                                {| stags := NoInfo;
                                                   str := "ig_intr_md" |})]))
                                    Directionless)
                               {| stags := NoInfo; str := "apply" |})
                          (TypFunction
                           (MkFunctionType nil
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_in" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false Out
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "resubmit_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_version" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_mac_tstamp" |},
                                          (TypBit 48%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md" |})] FunParser
                                TypVoid)) Directionless) nil
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName {| stags := NoInfo; str := "pkt" |})
                             (LInstance ["pkt"]))
                            (TypTypeName
                             {| stags := NoInfo; str := "packet_in" |})
                            Directionless));
                      (Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo; str := "ig_intr_md" |})
                             (LInstance ["ig_intr_md"]))
                            (TypTypeName
                             {| stags := NoInfo;
                                str := "ingress_intrinsic_metadata_t" |})
                            Out))]) StmUnit);
           (MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "hdr" |})
                                               (LInstance ["hdr"]))
                                              (TypTypeName
                                               {| stags := NoInfo;
                                                  str := "header_sample_t" |})
                                              Out)
                                         {| stags := NoInfo;
                                            str := "bridge" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "contains_sample" |},
                                        (TypBit 8%N) )]) Directionless)
                               {| stags := NoInfo; str := "setValid" |})
                          (TypFunction
                           (MkFunctionType nil nil FunBuiltin TypVoid))
                          Directionless) nil nil) StmUnit);
           (MkStatement NoInfo
                (StatAssignment
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpExpressionMember
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "hdr" |})
                                               (LInstance ["hdr"]))
                                              (TypTypeName
                                               {| stags := NoInfo;
                                                  str := "header_sample_t" |})
                                              Out)
                                         {| stags := NoInfo;
                                            str := "bridge" |})
                                    (TypHeader
                                     [( {| stags := NoInfo;
                                           str := "contains_sample" |},
                                        (TypBit 8%N) )]) Directionless)
                               {| stags := NoInfo;
                                  str := "contains_sample" |}) (TypBit 8%N)
                          Directionless)
                     (MkExpression NoInfo
                          (ExpCast (TypBit 8%N)
                               (MkExpression NoInfo
                                    (ExpInt
                                     {| itags := NoInfo; value := 0;
                                        width_signed := None |}) TypInteger
                                    Directionless)) (TypBit 8%N)
                          Directionless)) StmUnit)]
          (ParserDirect NoInfo
               {| stags := NoInfo; str := "parse_ethernet" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ethernet" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "dst_addr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "src_addr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "ether_type" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "ethernet" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "dst_addr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "src_addr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "ether_type" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |})
                                          (LInstance ["hdr"]))
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "header_sample_t" |})
                                         Out)
                                    {| stags := NoInfo; str := "ethernet" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) Directionless)
                          {| stags := NoInfo; str := "ether_type" |})
                     (TypBit 16%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 16%N)) (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "ETHERTYPE_IPV4" |})
                                                         (LGlobal
                                                              ["ETHERTYPE_IPV4"]))
                                                        (TypTypeName
                                                         {| stags := NoInfo;
                                                            str := "ether_type_t" |})
                                                        Directionless))
                           (TypBit 16%N))]
                     {| stags := NoInfo; str := "parse_ipv4" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 16%N))]
                     {| stags := NoInfo; str := "reject" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ipv4" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "version" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "diffserv" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "total_len" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "identification" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "frag_offset" |},
                          (TypBit 13%N) );
                        ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "protocol" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "hdr_checksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "src_addr" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "dst_addr" |},
                          (TypBit 32%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "ipv4" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "version" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "ihl" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "diffserv" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "total_len" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo;
                                   str := "identification" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 3%N) );
                              ( {| stags := NoInfo; str := "frag_offset" |},
                                (TypBit 13%N) );
                              ( {| stags := NoInfo; str := "ttl" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "protocol" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "hdr_checksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "src_addr" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "dst_addr" |},
                                (TypBit 32%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |})
                                          (LInstance ["hdr"]))
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "header_sample_t" |})
                                         Out)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "protocol" |})
                     (TypBit 8%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "IP_PROTOCOLS_TCP" |})
                                                        (LGlobal
                                                             ["IP_PROTOCOLS_TCP"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "ip_protocol_t" |})
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_tcp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "IP_PROTOCOLS_UDP" |})
                                                        (LGlobal
                                                             ["IP_PROTOCOLS_UDP"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "ip_protocol_t" |})
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_udp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 8%N))]
                     {| stags := NoInfo; str := "accept" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_tcp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "src_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dst_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "seq_no" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "ack_no" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "data_offset" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "window" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "urgent_ptr" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "tcp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "src_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dst_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "seq_no" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "ack_no" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "data_offset" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "res" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "window" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "urgent_ptr" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_udp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "src_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dst_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "hdr_length" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "udp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "src_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dst_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "hdr_length" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition SwitchIngress := DeclControl NoInfo
    {| stags := NoInfo; str := "SwitchIngress" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "ig_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo; str := "ingress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "ig_intr_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "ig_intr_prsr_md" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_deparser_t" |})
          None {| stags := NoInfo; str := "ig_intr_dprsr_md" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_tm_t" |}) None
          {| stags := NoInfo; str := "ig_intr_tm_md" |})] nil
    [(DeclAction NoInfo {| stags := NoInfo; str := "act_set_egress_port" |}
          nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "ig_intr_tm_md" |})
                                         (LInstance ["ig_intr_tm_md"]))
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "ingress_intrinsic_metadata_for_tm_t" |})
                                        InOut)
                                   {| stags := NoInfo;
                                      str := "ucast_egress_port" |})
                              (TypBit 9%N) Directionless)
                         (MkExpression NoInfo
                              (ExpCast (TypBit 9%N)
                                   (MkExpression NoInfo
                                        (ExpInt
                                         {| itags := NoInfo; value := 128;
                                            width_signed := None |})
                                        TypInteger Directionless))
                              (TypBit 9%N) Directionless)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "Register" |})
               [(TypBit 32%N); (TypBit 1%N)])
          [(MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 1;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless);
           (MkExpression NoInfo
                (ExpInt
                 {| itags := NoInfo; value := 0;
                    width_signed := (Some ( 32%N, false )) |}) (TypBit 32%N)
                Directionless)] {| stags := NoInfo; str := "reg_count" |}
          nil);
     (DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName {| stags := NoInfo; str := "RegisterAction" |})
               [(TypBit 32%N); (TypBit 1%N); (TypBit 32%N)])
          [(MkExpression NoInfo
                (ExpName (BareName {| stags := NoInfo; str := "reg_count" |})
                 (LGlobal ["missing_locator"]))
                (TypSpecializedType
                     (TypExtern {| stags := NoInfo; str := "Register" |})
                     [(TypBit 32%N); (TypBit 1%N)]) Directionless)]
          {| stags := NoInfo; str := "regact_count" |}
          [(DeclFunction NoInfo TypVoid {| stags := NoInfo; str := "apply" |}
                nil
                [(MkParameter false InOut (TypBit 32%N) None
                      {| stags := NoInfo; str := "value" |});
                 (MkParameter false Out (TypBit 32%N) None
                      {| stags := NoInfo; str := "rv" |})]
                (BlockCons
                     (MkStatement NoInfo
                          (StatAssignment
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "value" |})
                                     (LInstance ["apply"; "value"]))
                                    (TypBit 32%N) InOut)
                               (MkExpression NoInfo
                                    (ExpBinaryOp Plus
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "value" |})
                                               (LInstance ["apply"; "value"]))
                                              (TypBit 32%N) InOut)
                                         (MkExpression NoInfo
                                              (ExpInt
                                               {| itags := NoInfo;
                                                  value := 1;
                                                  width_signed := (Some
                                                                   (
                                                                   32%N,
                                                                   false )) |})
                                              (TypBit 32%N) Directionless))
                                    (TypBit 32%N) Directionless)) StmUnit)
                     (BlockCons
                          (MkStatement NoInfo
                               (StatAssignment
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo; str := "rv" |})
                                          (LInstance ["apply"; "rv"]))
                                         (TypBit 32%N) Out)
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "value" |})
                                          (LInstance ["apply"; "value"]))
                                         (TypBit 32%N) InOut)) StmUnit)
                          (BlockEmpty NoInfo))))]);
     (DeclAction NoInfo {| stags := NoInfo; str := "act_count" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpName
                                         (BareName
                                          {| stags := NoInfo;
                                             str := "ig_md" |})
                                         (LInstance ["ig_md"]))
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "metadata_t" |}) InOut)
                                   {| stags := NoInfo; str := "num_pkts" |})
                              (TypBit 32%N) Directionless)
                         (MkExpression NoInfo
                              (ExpFunctionCall
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "regact_count" |})
                                                   (LInstance
                                                        ["regact_count"]))
                                                  (TypSpecializedType
                                                       (TypExtern
                                                        {| stags := NoInfo;
                                                           str := "RegisterAction" |})
                                                       [(TypBit 32%N);
                                                        (TypBit 1%N);
                                                        (TypBit 32%N)])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "execute" |})
                                        (TypFunction
                                         (MkFunctionType nil
                                              [(MkParameter false In
                                                    (TypBit 1%N) None
                                                    {| stags := NoInfo;
                                                       str := "index" |})]
                                              FunExtern (TypBit 32%N)))
                                        Directionless) nil
                                   [(Some
                                     (MkExpression NoInfo
                                          (ExpCast (TypBit 1%N)
                                               (MkExpression NoInfo
                                                    (ExpInt
                                                     {| itags := NoInfo;
                                                        value := 0;
                                                        width_signed :=
                                                        None |}) TypInteger
                                                    Directionless))
                                          (TypBit 1%N) Directionless))])
                              (TypBit 32%N) Directionless)) StmUnit)
               (BlockEmpty NoInfo)));
     (DeclAction NoInfo {| stags := NoInfo; str := "act_sample" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatAssignment
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   (LInstance ["hdr"]))
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "header_sample_t" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "bridge" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "contains_sample" |},
                                            (TypBit 8%N) )]) Directionless)
                                   {| stags := NoInfo;
                                      str := "contains_sample" |})
                              (TypBit 8%N) Directionless)
                         (MkExpression NoInfo
                              (ExpCast (TypBit 8%N)
                                   (MkExpression NoInfo
                                        (ExpInt
                                         {| itags := NoInfo; value := 1;
                                            width_signed := None |})
                                        TypInteger Directionless))
                              (TypBit 8%N) Directionless)) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "hdr" |})
                                                        (LInstance ["hdr"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "header_sample_t" |})
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "sample" |})
                                             (TypHeader
                                              [( {| stags := NoInfo;
                                                    str := "dmac" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "smac" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "etype" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "srcip" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "dstip" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "num_pkts" |},
                                                 (TypBit 32%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "setValid" |})
                                   (TypFunction
                                    (MkFunctionType nil nil FunBuiltin
                                         TypVoid)) Directionless) nil nil)
                         StmUnit)
                    (BlockCons
                         (MkStatement NoInfo
                              (StatAssignment
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpExpressionMember
                                                       (MkExpression NoInfo
                                                            (ExpName
                                                             (BareName
                                                              {| stags := NoInfo;
                                                                 str := "hdr" |})
                                                             (LInstance
                                                                  ["hdr"]))
                                                            (TypTypeName
                                                             {| stags := NoInfo;
                                                                str := "header_sample_t" |})
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "sample" |})
                                                  (TypHeader
                                                   [( {| stags := NoInfo;
                                                         str := "dmac" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "smac" |},
                                                      (TypBit 48%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "etype" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "srcip" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "dstip" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "num_pkts" |},
                                                      (TypBit 32%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "dmac" |})
                                        (TypBit 48%N) Directionless)
                                   (MkExpression NoInfo
                                        (ExpCast (TypBit 48%N)
                                             (MkExpression NoInfo
                                                  (ExpInt
                                                   {| itags := NoInfo;
                                                      value := 2;
                                                      width_signed :=
                                                      None |}) TypInteger
                                                  Directionless))
                                        (TypBit 48%N) Directionless))
                              StmUnit)
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatAssignment
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpExpressionMember
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpName
                                                                  (BareName
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "hdr" |})
                                                                  (LInstance
                                                                    ["hdr"]))
                                                                 (TypTypeName
                                                                  {|
                                                                  stags := NoInfo;
                                                                  str := "header_sample_t" |})
                                                                 InOut)
                                                            {| stags := NoInfo;
                                                               str := "sample" |})
                                                       (TypHeader
                                                        [( {| stags := NoInfo;
                                                              str := "dmac" |},
                                                           (TypBit 48%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "smac" |},
                                                           (TypBit 48%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "etype" |},
                                                           (TypBit 16%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "srcip" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "dstip" |},
                                                           (TypBit 32%N) );
                                                         ( {| stags := NoInfo;
                                                              str := "num_pkts" |},
                                                           (TypBit 32%N) )])
                                                       Directionless)
                                                  {| stags := NoInfo;
                                                     str := "smac" |})
                                             (TypBit 48%N) Directionless)
                                        (MkExpression NoInfo
                                             (ExpCast (TypBit 48%N)
                                                  (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 1;
                                                           width_signed :=
                                                           None |})
                                                       TypInteger
                                                       Directionless))
                                             (TypBit 48%N) Directionless))
                                   StmUnit)
                              (BlockCons
                                   (MkStatement NoInfo
                                        (StatAssignment
                                             (MkExpression NoInfo
                                                  (ExpExpressionMember
                                                       (MkExpression NoInfo
                                                            (ExpExpressionMember
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                 {| stags := NoInfo;
                                                                    str := "sample" |})
                                                            (TypHeader
                                                             [( {| stags := NoInfo;
                                                                   str := "dmac" |},
                                                                (TypBit 48%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "smac" |},
                                                                (TypBit 48%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "etype" |},
                                                                (TypBit 16%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "srcip" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "dstip" |},
                                                                (TypBit 32%N) );
                                                              ( {| stags := NoInfo;
                                                                   str := "num_pkts" |},
                                                                (TypBit 32%N) )])
                                                            Directionless)
                                                       {| stags := NoInfo;
                                                          str := "etype" |})
                                                  (TypBit 16%N)
                                                  Directionless)
                                             (MkExpression NoInfo
                                                  (ExpCast (TypBit 16%N)
                                                       (MkExpression NoInfo
                                                            (ExpInt
                                                             {| itags := NoInfo;
                                                                value := 4660;
                                                                width_signed :=
                                                                None |})
                                                            TypInteger
                                                            Directionless))
                                                  (TypBit 16%N)
                                                  Directionless)) StmUnit)
                                   (BlockCons
                                        (MkStatement NoInfo
                                             (StatAssignment
                                                  (MkExpression NoInfo
                                                       (ExpExpressionMember
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "sample" |})
                                                                 (TypHeader
                                                                  [(
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "dmac" |},
                                                                   (TypBit
                                                                    48%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "smac" |},
                                                                   (TypBit
                                                                    48%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "etype" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "srcip" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "dstip" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "num_pkts" |},
                                                                   (TypBit
                                                                    32%N) )])
                                                                 Directionless)
                                                            {| stags := NoInfo;
                                                               str := "srcip" |})
                                                       (TypBit 32%N)
                                                       Directionless)
                                                  (MkExpression NoInfo
                                                       (ExpExpressionMember
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ipv4" |})
                                                                 (TypHeader
                                                                  [(
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "version" |},
                                                                   (TypBit
                                                                    4%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "ihl" |},
                                                                   (TypBit
                                                                    4%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "diffserv" |},
                                                                   (TypBit
                                                                    8%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "total_len" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "identification" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "flags" |},
                                                                   (TypBit
                                                                    3%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "frag_offset" |},
                                                                   (TypBit
                                                                    13%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "ttl" |},
                                                                   (TypBit
                                                                    8%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "protocol" |},
                                                                   (TypBit
                                                                    8%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "hdr_checksum" |},
                                                                   (TypBit
                                                                    16%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "src_addr" |},
                                                                   (TypBit
                                                                    32%N) );
                                                                   (
                                                                   {|
                                                                   stags := NoInfo;
                                                                   str := "dst_addr" |},
                                                                   (TypBit
                                                                    32%N) )])
                                                                 Directionless)
                                                            {| stags := NoInfo;
                                                               str := "src_addr" |})
                                                       (TypBit 32%N)
                                                       Directionless))
                                             StmUnit)
                                        (BlockCons
                                             (MkStatement NoInfo
                                                  (StatAssignment
                                                       (MkExpression NoInfo
                                                            (ExpExpressionMember
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "sample" |})
                                                                    (TypHeader
                                                                    [(
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "dmac" |},
                                                                    (
                                                                    TypBit
                                                                    48%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "smac" |},
                                                                    (
                                                                    TypBit
                                                                    48%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "etype" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "srcip" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "dstip" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "num_pkts" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                 {| stags := NoInfo;
                                                                    str := "dstip" |})
                                                            (TypBit 32%N)
                                                            Directionless)
                                                       (MkExpression NoInfo
                                                            (ExpExpressionMember
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "ipv4" |})
                                                                    (TypHeader
                                                                    [(
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "version" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ihl" |},
                                                                    (
                                                                    TypBit
                                                                    4%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "diffserv" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "total_len" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "identification" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "flags" |},
                                                                    (
                                                                    TypBit
                                                                    3%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "frag_offset" |},
                                                                    (
                                                                    TypBit
                                                                    13%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ttl" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "protocol" |},
                                                                    (
                                                                    TypBit
                                                                    8%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr_checksum" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "src_addr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "dst_addr" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                 {| stags := NoInfo;
                                                                    str := "dst_addr" |})
                                                            (TypBit 32%N)
                                                            Directionless))
                                                  StmUnit)
                                             (BlockCons
                                                  (MkStatement NoInfo
                                                       (StatAssignment
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "hdr" |})
                                                                    (LInstance
                                                                    ["hdr"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "header_sample_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "sample" |})
                                                                    (TypHeader
                                                                    [(
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "dmac" |},
                                                                    (
                                                                    TypBit
                                                                    48%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "smac" |},
                                                                    (
                                                                    TypBit
                                                                    48%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "etype" |},
                                                                    (
                                                                    TypBit
                                                                    16%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "srcip" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "dstip" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) );
                                                                    (
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "num_pkts" |},
                                                                    (
                                                                    TypBit
                                                                    32%N) )])
                                                                    Directionless)
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "num_pkts" |})
                                                                 (TypBit
                                                                  32%N)
                                                                 Directionless)
                                                            (MkExpression
                                                                 NoInfo
                                                                 (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ig_md" |})
                                                                    (LInstance
                                                                    ["ig_md"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "metadata_t" |})
                                                                    InOut)
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "num_pkts" |})
                                                                 (TypBit
                                                                  32%N)
                                                                 Directionless))
                                                       StmUnit)
                                                  (BlockCons
                                                       (MkStatement NoInfo
                                                            (StatAssignment
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpExpressionMember
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpName
                                                                    (BareName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ig_intr_tm_md" |})
                                                                    (LInstance
                                                                    ["ig_intr_tm_md"]))
                                                                    (TypTypeName
                                                                    {|
                                                                    stags := NoInfo;
                                                                    str := "ingress_intrinsic_metadata_for_tm_t" |})
                                                                    InOut)
                                                                    {| stags := NoInfo;
                                                                    str := "mcast_grp_a" |})
                                                                    (TypBit
                                                                    16%N)
                                                                    Directionless)
                                                                 (MkExpression
                                                                    NoInfo
                                                                    (ExpCast
                                                                    (TypBit
                                                                    16%N)
                                                                    (MkExpression
                                                                    NoInfo
                                                                    (ExpInt
                                                                    {|
                                                                    itags := NoInfo;
                                                                    value := 1;
                                                                    width_signed :=
                                                                    None |})
                                                                    TypInteger
                                                                    Directionless))
                                                                    (TypBit
                                                                    16%N)
                                                                    Directionless))
                                                            StmUnit)
                                                       (BlockEmpty NoInfo)))))))))));
     (DeclTable NoInfo {| stags := NoInfo; str := "tbl_sample" |}
          [(MkTableKey NoInfo
                (MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpName
                                (BareName
                                 {| stags := NoInfo; str := "ig_md" |})
                                (LInstance ["ig_md"]))
                               (TypTypeName
                                {| stags := NoInfo; str := "metadata_t" |})
                               InOut)
                          {| stags := NoInfo; str := "num_pkts" |})
                     (TypBit 32%N) Directionless)
                {| stags := NoInfo; str := "ternary" |})]
          [(MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (BareName {| stags := NoInfo; str := "act_sample" |})
                     nil) (TypAction nil nil));
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (QualifiedName nil
                          {| stags := NoInfo; str := "NoAction" |}) nil)
                (TypAction nil nil))]
          (Some
           [(MkTableEntry NoInfo
                 [(MkMatch NoInfo
                       (MatchMask
                        (MkExpression NoInfo
                             (ExpInt
                              {| itags := NoInfo; value := 1;
                                 width_signed := (Some ( 32%N, false )) |})
                             (TypBit 32%N) Directionless) (MkExpression
                                                               NoInfo
                                                               (ExpInt
                                                                {| itags := NoInfo;
                                                                   value := 1023;
                                                                   width_signed := (
                                                                   Some
                                                                   (
                                                                   32%N,
                                                                   false )) |})
                                                               (TypBit 32%N)
                                                               Directionless))
                       (TypBit 32%N))]
                 (MkTableActionRef NoInfo
                      (MkTablePreActionRef
                           (BareName
                            {| stags := NoInfo; str := "act_sample" |}) nil)
                      (TypAction nil nil)));
            (MkTableEntry NoInfo
                 [(MkMatch NoInfo MatchDontCare (TypBit 32%N))]
                 (MkTableActionRef NoInfo
                      (MkTablePreActionRef
                           (QualifiedName nil
                                {| stags := NoInfo; str := "NoAction" |})
                           nil) (TypAction nil nil)))])
          (Some
           (MkTableActionRef NoInfo
                (MkTablePreActionRef
                     (QualifiedName nil
                          {| stags := NoInfo; str := "NoAction" |}) nil)
                (TypAction nil nil))) (Some 2%N) nil)]
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpName
                         (BareName
                          {| stags := NoInfo; str := "act_set_egress_port" |})
                         (LInstance ["act_set_egress_port"]))
                        (TypAction nil nil) Directionless) nil nil) StmUnit)
         (BlockCons
              (MkStatement NoInfo
                   (StatMethodCall
                        (MkExpression NoInfo
                             (ExpName
                              (BareName
                               {| stags := NoInfo; str := "act_count" |})
                              (LInstance ["act_count"])) (TypAction nil nil)
                             Directionless) nil nil) StmUnit)
              (BlockCons
                   (MkStatement NoInfo
                        (StatMethodCall
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpName
                                             (BareName
                                              {| stags := NoInfo;
                                                 str := "tbl_sample" |})
                                             (LInstance ["tbl_sample"]))
                                            (TypTable
                                             {| stags := NoInfo;
                                                str := "apply_result_tbl_sample" |})
                                            Directionless)
                                       {| stags := NoInfo; str := "apply" |})
                                  (TypFunction
                                   (MkFunctionType nil nil FunTable
                                        (TypTypeName
                                         {| stags := NoInfo;
                                            str := "apply_result_tbl_sample" |})))
                                  Directionless) nil nil) StmUnit)
                   (BlockEmpty NoInfo)))).

Definition SwitchIngressDeparser := DeclControl NoInfo
    {| stags := NoInfo; str := "SwitchIngressDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "ig_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "ingress_intrinsic_metadata_for_deparser_t" |})
          None {| stags := NoInfo; str := "ig_intr_dprsr_md" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "pkt" |})
                                   (LInstance ["pkt"]))
                                  (TypTypeName
                                   {| stags := NoInfo; str := "packet_out" |})
                                  Directionless)
                             {| stags := NoInfo; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := NoInfo; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     {| stags := NoInfo; str := "T2" |})
                                    None {| stags := NoInfo; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypStruct
                     [( {| stags := NoInfo; str := "bridge" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "contains_sample" |},
                            (TypBit 8%N) )]) );
                      ( {| stags := NoInfo; str := "sample" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "dmac" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "smac" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "etype" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "srcip" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "dstip" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "num_pkts" |},
                            (TypBit 32%N) )]) );
                      ( {| stags := NoInfo; str := "ethernet" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "dst_addr" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "src_addr" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "ether_type" |},
                            (TypBit 16%N) )]) );
                      ( {| stags := NoInfo; str := "ipv4" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "version" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "ihl" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "diffserv" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "total_len" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "identification" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "flags" |},
                            (TypBit 3%N) );
                          ( {| stags := NoInfo; str := "frag_offset" |},
                            (TypBit 13%N) );
                          ( {| stags := NoInfo; str := "ttl" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "protocol" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "hdr_checksum" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "src_addr" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "dst_addr" |},
                            (TypBit 32%N) )]) );
                      ( {| stags := NoInfo; str := "tcp" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "src_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "dst_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "seq_no" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "ack_no" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "data_offset" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "res" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "flags" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "window" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "checksum" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "urgent_ptr" |},
                            (TypBit 16%N) )]) );
                      ( {| stags := NoInfo; str := "udp" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "src_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "dst_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "hdr_length" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "checksum" |},
                            (TypBit 16%N) )]) )])]
                   [(Some
                     (MkExpression NoInfo
                          (ExpName
                           (BareName {| stags := NoInfo; str := "hdr" |})
                           (LInstance ["hdr"]))
                          (TypTypeName
                           {| stags := NoInfo; str := "header_sample_t" |})
                          InOut))]) StmUnit) (BlockEmpty NoInfo)).

Definition SwitchEgressParser := DeclParser NoInfo
    {| stags := NoInfo; str := "SwitchEgressParser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_in" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false Out
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false Out
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |})] nil
    [(DeclInstantiation NoInfo
          (TypSpecializedType
               (TypTypeName
                {| stags := NoInfo; str := "TofinoEgressParser" |}) nil) nil
          {| stags := NoInfo; str := "tofino_parser" |} nil)]
    [(MkParserState NoInfo {| stags := NoInfo; str := "start" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo;
                                         str := "tofino_parser" |})
                                     (LInstance ["tofino_parser"]))
                                    (TypParser
                                     (MkControlType nil
                                          [(MkParameter false Directionless
                                                (TypExtern
                                                 {| stags := NoInfo;
                                                    str := "packet_in" |})
                                                None
                                                {| stags := NoInfo;
                                                   str := "pkt" |});
                                           (MkParameter false Out
                                                (TypHeader
                                                 [( {| stags := NoInfo;
                                                       str := "_pad0" |},
                                                    (TypBit 7%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "egress_port" |},
                                                    (TypBit 9%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad1" |},
                                                    (TypBit 5%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "enq_qdepth" |},
                                                    (TypBit 19%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad2" |},
                                                    (TypBit 6%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "enq_congest_stat" |},
                                                    (TypBit 2%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad3" |},
                                                    (TypBit 14%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "enq_tstamp" |},
                                                    (TypBit 18%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad4" |},
                                                    (TypBit 5%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "deq_qdepth" |},
                                                    (TypBit 19%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad5" |},
                                                    (TypBit 6%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "deq_congest_stat" |},
                                                    (TypBit 2%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "app_pool_congest_stat" |},
                                                    (TypBit 8%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad6" |},
                                                    (TypBit 14%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "deq_timedelta" |},
                                                    (TypBit 18%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "egress_rid" |},
                                                    (TypBit 16%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad7" |},
                                                    (TypBit 7%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "egress_rid_first" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad8" |},
                                                    (TypBit 3%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "egress_qid" |},
                                                    (TypBit 5%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad9" |},
                                                    (TypBit 5%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "egress_cos" |},
                                                    (TypBit 3%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "_pad10" |},
                                                    (TypBit 7%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "deflection_flag" |},
                                                    (TypBit 1%N) );
                                                  ( {| stags := NoInfo;
                                                       str := "pkt_length" |},
                                                    (TypBit 16%N) )])
                                                None
                                                {| stags := NoInfo;
                                                   str := "eg_intr_md" |})]))
                                    Directionless)
                               {| stags := NoInfo; str := "apply" |})
                          (TypFunction
                           (MkFunctionType nil
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_in" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false Out
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "_pad0" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad3" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_tstamp" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad4" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad5" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "app_pool_congest_stat" |},
                                          (TypBit 8%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad6" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_timedelta" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad7" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid_first" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad8" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad9" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad10" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflection_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "pkt_length" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md" |})] FunParser
                                TypVoid)) Directionless) nil
                     [(Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName {| stags := NoInfo; str := "pkt" |})
                             (LInstance ["pkt"]))
                            (TypTypeName
                             {| stags := NoInfo; str := "packet_in" |})
                            Directionless));
                      (Some
                       (MkExpression NoInfo
                            (ExpName
                             (BareName
                              {| stags := NoInfo; str := "eg_intr_md" |})
                             (LInstance ["eg_intr_md"]))
                            (TypTypeName
                             {| stags := NoInfo;
                                str := "egress_intrinsic_metadata_t" |}) Out))])
                StmUnit);
           (MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "contains_sample" |},
                          (TypBit 8%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "bridge" |})
                            (TypHeader
                             [( {| stags := NoInfo;
                                   str := "contains_sample" |},
                                (TypBit 8%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |})
                                          (LInstance ["hdr"]))
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "header_sample_t" |})
                                         Out)
                                    {| stags := NoInfo; str := "bridge" |})
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) Directionless)
                          {| stags := NoInfo; str := "contains_sample" |})
                     (TypBit 8%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpInt
                                                        {| itags := NoInfo;
                                                           value := 1;
                                                           width_signed :=
                                                           None |})
                                                       TypInteger
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_sample" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_ethernet" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_sample" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "dmac" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "smac" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "etype" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "srcip" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "dstip" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "sample" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "dmac" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "smac" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "etype" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "srcip" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "dstip" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "num_pkts" |},
                                (TypBit 32%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo
               {| stags := NoInfo; str := "parse_ethernet" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ethernet" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "dst_addr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "src_addr" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "ether_type" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "ethernet" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "dst_addr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "src_addr" |},
                                (TypBit 48%N) );
                              ( {| stags := NoInfo; str := "ether_type" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |})
                                          (LInstance ["hdr"]))
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "header_sample_t" |})
                                         Out)
                                    {| stags := NoInfo; str := "ethernet" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) Directionless)
                          {| stags := NoInfo; str := "ether_type" |})
                     (TypBit 16%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 16%N)) (MkExpression NoInfo
                                                        (ExpName
                                                         (BareName
                                                          {| stags := NoInfo;
                                                             str := "ETHERTYPE_IPV4" |})
                                                         (LGlobal
                                                              ["ETHERTYPE_IPV4"]))
                                                        (TypTypeName
                                                         {| stags := NoInfo;
                                                            str := "ether_type_t" |})
                                                        Directionless))
                           (TypBit 16%N))]
                     {| stags := NoInfo; str := "parse_ipv4" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 16%N))]
                     {| stags := NoInfo; str := "reject" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_ipv4" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "version" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "diffserv" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "total_len" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "identification" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "frag_offset" |},
                          (TypBit 13%N) );
                        ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "protocol" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "hdr_checksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "src_addr" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "dst_addr" |},
                          (TypBit 32%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "ipv4" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "version" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "ihl" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "diffserv" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "total_len" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo;
                                   str := "identification" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 3%N) );
                              ( {| stags := NoInfo; str := "frag_offset" |},
                                (TypBit 13%N) );
                              ( {| stags := NoInfo; str := "ttl" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "protocol" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "hdr_checksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "src_addr" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "dst_addr" |},
                                (TypBit 32%N) )]) Directionless))]) StmUnit)]
          (ParserSelect NoInfo
               [(MkExpression NoInfo
                     (ExpExpressionMember
                          (MkExpression NoInfo
                               (ExpExpressionMember
                                    (MkExpression NoInfo
                                         (ExpName
                                          (BareName
                                           {| stags := NoInfo;
                                              str := "hdr" |})
                                          (LInstance ["hdr"]))
                                         (TypTypeName
                                          {| stags := NoInfo;
                                             str := "header_sample_t" |})
                                         Out)
                                    {| stags := NoInfo; str := "ipv4" |})
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) Directionless)
                          {| stags := NoInfo; str := "protocol" |})
                     (TypBit 8%N) Directionless)]
               [(MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "IP_PROTOCOLS_TCP" |})
                                                        (LGlobal
                                                             ["IP_PROTOCOLS_TCP"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "ip_protocol_t" |})
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_tcp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo
                           (MatchCast
                            (TypSet (TypBit 8%N)) (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "IP_PROTOCOLS_UDP" |})
                                                        (LGlobal
                                                             ["IP_PROTOCOLS_UDP"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "ip_protocol_t" |})
                                                       Directionless))
                           (TypBit 8%N))]
                     {| stags := NoInfo; str := "parse_udp" |});
                (MkParserCase NoInfo
                     [(MkMatch NoInfo MatchDontCare (TypBit 8%N))]
                     {| stags := NoInfo; str := "accept" |})]));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_tcp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "src_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dst_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "seq_no" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "ack_no" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "data_offset" |},
                          (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                        ( {| stags := NoInfo; str := "flags" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "window" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "urgent_ptr" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "tcp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "src_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dst_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "seq_no" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "ack_no" |},
                                (TypBit 32%N) );
                              ( {| stags := NoInfo; str := "data_offset" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "res" |},
                                (TypBit 4%N) );
                              ( {| stags := NoInfo; str := "flags" |},
                                (TypBit 8%N) );
                              ( {| stags := NoInfo; str := "window" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "urgent_ptr" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}));
     (MkParserState NoInfo {| stags := NoInfo; str := "parse_udp" |}
          [(MkStatement NoInfo
                (StatMethodCall
                     (MkExpression NoInfo
                          (ExpExpressionMember
                               (MkExpression NoInfo
                                    (ExpName
                                     (BareName
                                      {| stags := NoInfo; str := "pkt" |})
                                     (LInstance ["pkt"]))
                                    (TypTypeName
                                     {| stags := NoInfo;
                                        str := "packet_in" |}) Directionless)
                               {| stags := NoInfo; str := "extract" |})
                          (TypFunction
                           (MkFunctionType
                                [{| stags := NoInfo; str := "T" |}]
                                [(MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "T" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |})]
                                FunExtern TypVoid)) Directionless)
                     [(TypHeader
                       [( {| stags := NoInfo; str := "src_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "dst_port" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "hdr_length" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "checksum" |},
                          (TypBit 16%N) )])]
                     [(Some
                       (MkExpression NoInfo
                            (ExpExpressionMember
                                 (MkExpression NoInfo
                                      (ExpName
                                       (BareName
                                        {| stags := NoInfo; str := "hdr" |})
                                       (LInstance ["hdr"]))
                                      (TypTypeName
                                       {| stags := NoInfo;
                                          str := "header_sample_t" |}) Out)
                                 {| stags := NoInfo; str := "udp" |})
                            (TypHeader
                             [( {| stags := NoInfo; str := "src_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "dst_port" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "hdr_length" |},
                                (TypBit 16%N) );
                              ( {| stags := NoInfo; str := "checksum" |},
                                (TypBit 16%N) )]) Directionless))]) StmUnit)]
          (ParserDirect NoInfo {| stags := NoInfo; str := "accept" |}))].

Definition SwitchEgress := DeclControl NoInfo
    {| stags := NoInfo; str := "SwitchEgress" |} nil
    [(MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo; str := "egress_intrinsic_metadata_t" |})
          None {| stags := NoInfo; str := "eg_intr_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_from_parser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_from_prsr" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_md_for_dprsr" |});
     (MkParameter false InOut
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_output_port_t" |})
          None {| stags := NoInfo; str := "eg_intr_md_for_oport" |})] nil
    [(DeclAction NoInfo
          {| stags := NoInfo; str := "act_delete_sample_hdrs" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   (LInstance ["hdr"]))
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "header_sample_t" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "bridge" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "contains_sample" |},
                                            (TypBit 8%N) )]) Directionless)
                                   {| stags := NoInfo; str := "setInvalid" |})
                              (TypFunction
                               (MkFunctionType nil nil FunBuiltin TypVoid))
                              Directionless) nil nil) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "hdr" |})
                                                        (LInstance ["hdr"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "header_sample_t" |})
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "sample" |})
                                             (TypHeader
                                              [( {| stags := NoInfo;
                                                    str := "dmac" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "smac" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "etype" |},
                                                 (TypBit 16%N) );
                                               ( {| stags := NoInfo;
                                                    str := "srcip" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "dstip" |},
                                                 (TypBit 32%N) );
                                               ( {| stags := NoInfo;
                                                    str := "num_pkts" |},
                                                 (TypBit 32%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "setInvalid" |})
                                   (TypFunction
                                    (MkFunctionType nil nil FunBuiltin
                                         TypVoid)) Directionless) nil nil)
                         StmUnit) (BlockEmpty NoInfo))));
     (DeclAction NoInfo
          {| stags := NoInfo; str := "act_delete_packet_hdrs" |} nil nil
          (BlockCons
               (MkStatement NoInfo
                    (StatMethodCall
                         (MkExpression NoInfo
                              (ExpExpressionMember
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpName
                                                   (BareName
                                                    {| stags := NoInfo;
                                                       str := "hdr" |})
                                                   (LInstance ["hdr"]))
                                                  (TypTypeName
                                                   {| stags := NoInfo;
                                                      str := "header_sample_t" |})
                                                  InOut)
                                             {| stags := NoInfo;
                                                str := "bridge" |})
                                        (TypHeader
                                         [( {| stags := NoInfo;
                                               str := "contains_sample" |},
                                            (TypBit 8%N) )]) Directionless)
                                   {| stags := NoInfo; str := "setInvalid" |})
                              (TypFunction
                               (MkFunctionType nil nil FunBuiltin TypVoid))
                              Directionless) nil nil) StmUnit)
               (BlockCons
                    (MkStatement NoInfo
                         (StatMethodCall
                              (MkExpression NoInfo
                                   (ExpExpressionMember
                                        (MkExpression NoInfo
                                             (ExpExpressionMember
                                                  (MkExpression NoInfo
                                                       (ExpName
                                                        (BareName
                                                         {| stags := NoInfo;
                                                            str := "hdr" |})
                                                        (LInstance ["hdr"]))
                                                       (TypTypeName
                                                        {| stags := NoInfo;
                                                           str := "header_sample_t" |})
                                                       InOut)
                                                  {| stags := NoInfo;
                                                     str := "ethernet" |})
                                             (TypHeader
                                              [( {| stags := NoInfo;
                                                    str := "dst_addr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "src_addr" |},
                                                 (TypBit 48%N) );
                                               ( {| stags := NoInfo;
                                                    str := "ether_type" |},
                                                 (TypBit 16%N) )])
                                             Directionless)
                                        {| stags := NoInfo;
                                           str := "setInvalid" |})
                                   (TypFunction
                                    (MkFunctionType nil nil FunBuiltin
                                         TypVoid)) Directionless) nil nil)
                         StmUnit)
                    (BlockCons
                         (MkStatement NoInfo
                              (StatMethodCall
                                   (MkExpression NoInfo
                                        (ExpExpressionMember
                                             (MkExpression NoInfo
                                                  (ExpExpressionMember
                                                       (MkExpression NoInfo
                                                            (ExpName
                                                             (BareName
                                                              {| stags := NoInfo;
                                                                 str := "hdr" |})
                                                             (LInstance
                                                                  ["hdr"]))
                                                            (TypTypeName
                                                             {| stags := NoInfo;
                                                                str := "header_sample_t" |})
                                                            InOut)
                                                       {| stags := NoInfo;
                                                          str := "ipv4" |})
                                                  (TypHeader
                                                   [( {| stags := NoInfo;
                                                         str := "version" |},
                                                      (TypBit 4%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ihl" |},
                                                      (TypBit 4%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "diffserv" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "total_len" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "identification" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "flags" |},
                                                      (TypBit 3%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "frag_offset" |},
                                                      (TypBit 13%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "ttl" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "protocol" |},
                                                      (TypBit 8%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "hdr_checksum" |},
                                                      (TypBit 16%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "src_addr" |},
                                                      (TypBit 32%N) );
                                                    ( {| stags := NoInfo;
                                                         str := "dst_addr" |},
                                                      (TypBit 32%N) )])
                                                  Directionless)
                                             {| stags := NoInfo;
                                                str := "setInvalid" |})
                                        (TypFunction
                                         (MkFunctionType nil nil FunBuiltin
                                              TypVoid)) Directionless) nil
                                   nil) StmUnit) (BlockEmpty NoInfo)))))]
    (BlockCons
         (MkStatement NoInfo
              (StatConditional
                   (MkExpression NoInfo
                        (ExpBinaryOp Eq
                             (MkExpression NoInfo
                                  (ExpExpressionMember
                                       (MkExpression NoInfo
                                            (ExpName
                                             (BareName
                                              {| stags := NoInfo;
                                                 str := "eg_intr_md" |})
                                             (LInstance ["eg_intr_md"]))
                                            (TypTypeName
                                             {| stags := NoInfo;
                                                str := "egress_intrinsic_metadata_t" |})
                                            In)
                                       {| stags := NoInfo;
                                          str := "egress_rid" |})
                                  (TypBit 16%N) Directionless)
                             (MkExpression NoInfo
                                  (ExpCast (TypBit 16%N)
                                       (MkExpression NoInfo
                                            (ExpInt
                                             {| itags := NoInfo; value := 0;
                                                width_signed := None |})
                                            TypInteger Directionless))
                                  (TypBit 16%N) Directionless)) TypBool
                        Directionless)
                   (MkStatement NoInfo
                        (StatBlock
                         (BlockCons
                              (MkStatement NoInfo
                                   (StatMethodCall
                                        (MkExpression NoInfo
                                             (ExpName
                                              (BareName
                                               {| stags := NoInfo;
                                                  str := "act_delete_sample_hdrs" |})
                                              (LInstance
                                                   ["act_delete_sample_hdrs"]))
                                             (TypAction nil nil)
                                             Directionless) nil nil) StmUnit)
                              (BlockEmpty NoInfo))) StmUnit)
                   (Some
                    (MkStatement NoInfo
                         (StatBlock
                          (BlockCons
                               (MkStatement NoInfo
                                    (StatMethodCall
                                         (MkExpression NoInfo
                                              (ExpName
                                               (BareName
                                                {| stags := NoInfo;
                                                   str := "act_delete_packet_hdrs" |})
                                               (LInstance
                                                    ["act_delete_packet_hdrs"]))
                                              (TypAction nil nil)
                                              Directionless) nil nil)
                                    StmUnit) (BlockEmpty NoInfo))) StmUnit)))
              StmUnit) (BlockEmpty NoInfo)).

Definition SwitchEgressDeparser := DeclControl NoInfo
    {| stags := NoInfo; str := "SwitchEgressDeparser" |} nil
    [(MkParameter false Directionless
          (TypTypeName {| stags := NoInfo; str := "packet_out" |}) None
          {| stags := NoInfo; str := "pkt" |});
     (MkParameter false InOut
          (TypTypeName {| stags := NoInfo; str := "header_sample_t" |})
          None {| stags := NoInfo; str := "hdr" |});
     (MkParameter false In
          (TypTypeName {| stags := NoInfo; str := "metadata_t" |}) None
          {| stags := NoInfo; str := "eg_md" |});
     (MkParameter false In
          (TypTypeName
           {| stags := NoInfo;
              str := "egress_intrinsic_metadata_for_deparser_t" |}) None
          {| stags := NoInfo; str := "eg_intr_dprsr_md" |})] nil nil
    (BlockCons
         (MkStatement NoInfo
              (StatMethodCall
                   (MkExpression NoInfo
                        (ExpExpressionMember
                             (MkExpression NoInfo
                                  (ExpName
                                   (BareName
                                    {| stags := NoInfo; str := "pkt" |})
                                   (LInstance ["pkt"]))
                                  (TypTypeName
                                   {| stags := NoInfo; str := "packet_out" |})
                                  Directionless)
                             {| stags := NoInfo; str := "emit" |})
                        (TypFunction
                         (MkFunctionType [{| stags := NoInfo; str := "T2" |}]
                              [(MkParameter false In
                                    (TypTypeName
                                     {| stags := NoInfo; str := "T2" |})
                                    None {| stags := NoInfo; str := "hdr" |})]
                              FunExtern TypVoid)) Directionless)
                   [(TypStruct
                     [( {| stags := NoInfo; str := "bridge" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "contains_sample" |},
                            (TypBit 8%N) )]) );
                      ( {| stags := NoInfo; str := "sample" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "dmac" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "smac" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "etype" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "srcip" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "dstip" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "num_pkts" |},
                            (TypBit 32%N) )]) );
                      ( {| stags := NoInfo; str := "ethernet" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "dst_addr" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "src_addr" |},
                            (TypBit 48%N) );
                          ( {| stags := NoInfo; str := "ether_type" |},
                            (TypBit 16%N) )]) );
                      ( {| stags := NoInfo; str := "ipv4" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "version" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "ihl" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "diffserv" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "total_len" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "identification" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "flags" |},
                            (TypBit 3%N) );
                          ( {| stags := NoInfo; str := "frag_offset" |},
                            (TypBit 13%N) );
                          ( {| stags := NoInfo; str := "ttl" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "protocol" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "hdr_checksum" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "src_addr" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "dst_addr" |},
                            (TypBit 32%N) )]) );
                      ( {| stags := NoInfo; str := "tcp" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "src_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "dst_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "seq_no" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "ack_no" |},
                            (TypBit 32%N) );
                          ( {| stags := NoInfo; str := "data_offset" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "res" |},
                            (TypBit 4%N) );
                          ( {| stags := NoInfo; str := "flags" |},
                            (TypBit 8%N) );
                          ( {| stags := NoInfo; str := "window" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "checksum" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "urgent_ptr" |},
                            (TypBit 16%N) )]) );
                      ( {| stags := NoInfo; str := "udp" |},
                        (TypHeader
                         [( {| stags := NoInfo; str := "src_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "dst_port" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "hdr_length" |},
                            (TypBit 16%N) );
                          ( {| stags := NoInfo; str := "checksum" |},
                            (TypBit 16%N) )]) )])]
                   [(Some
                     (MkExpression NoInfo
                          (ExpName
                           (BareName {| stags := NoInfo; str := "hdr" |})
                           (LInstance ["hdr"]))
                          (TypTypeName
                           {| stags := NoInfo; str := "header_sample_t" |})
                          InOut))]) StmUnit) (BlockEmpty NoInfo)).

Definition pipe := DeclInstantiation NoInfo
    (TypSpecializedType
         (TypTypeName {| stags := NoInfo; str := "Pipeline" |})
         [(TypStruct
           [( {| stags := NoInfo; str := "bridge" |},
              (TypHeader
               [( {| stags := NoInfo; str := "contains_sample" |},
                  (TypBit 8%N) )]) );
            ( {| stags := NoInfo; str := "sample" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dmac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "smac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etype" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "srcip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dstip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "ether_type" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "ipv4" |},
              (TypHeader
               [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "total_len" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "identification" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
                ( {| stags := NoInfo; str := "frag_offset" |},
                  (TypBit 13%N) );
                ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "hdr_checksum" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "tcp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "seq_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ack_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "data_offset" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "urgent_ptr" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "udp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "hdr_length" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "bridge" |},
              (TypHeader
               [( {| stags := NoInfo; str := "contains_sample" |},
                  (TypBit 8%N) )]) );
            ( {| stags := NoInfo; str := "sample" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dmac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "smac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etype" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "srcip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dstip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "ether_type" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "ipv4" |},
              (TypHeader
               [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "total_len" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "identification" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
                ( {| stags := NoInfo; str := "frag_offset" |},
                  (TypBit 13%N) );
                ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "hdr_checksum" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "tcp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "seq_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ack_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "data_offset" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "urgent_ptr" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "udp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "hdr_length" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )])])
    [(MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchIngressParser" |})
                    nil) nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_in" |})
                      None {| stags := NoInfo; str := "pkt" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "ig_md" |});
                 (MkParameter false Out
                      (TypHeader
                       [( {| stags := NoInfo; str := "resubmit_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "packet_version" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "ingress_mac_tstamp" |},
                          (TypBit 48%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_md" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchIngress" |}) nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "ig_md" |});
                 (MkParameter false In
                      (TypHeader
                       [( {| stags := NoInfo; str := "resubmit_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "packet_version" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "ingress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "ingress_mac_tstamp" |},
                          (TypBit 48%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_md" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "global_tstamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "global_ver" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "parser_err" |},
                          (TypBit 16%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_prsr_md" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "drop_ctl" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "digest_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "resubmit_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "mirror_type" |},
                          (TypBit 3%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_dprsr_md" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "ucast_egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "bypass_egress" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "deflect_on_drop" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "ingress_cos" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "qid" |}, (TypBit 5%N) );
                        ( {| stags := NoInfo;
                             str := "icos_for_copy_to_cpu" |}, (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "copy_to_cpu" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "packet_color" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo;
                             str := "disable_ucast_cutthru" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo;
                             str := "enable_mcast_cutthru" |}, (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "mcast_grp_a" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "mcast_grp_b" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "level1_mcast_hash" |},
                          (TypBit 13%N) );
                        ( {| stags := NoInfo; str := "level2_mcast_hash" |},
                          (TypBit 13%N) );
                        ( {| stags := NoInfo; str := "level1_exclusion_id" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "level2_exclusion_id" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "rid" |},
                          (TypBit 16%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_tm_md" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchIngressDeparser" |})
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_out" |})
                      None {| stags := NoInfo; str := "pkt" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "ig_md" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "drop_ctl" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "digest_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "resubmit_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "mirror_type" |},
                          (TypBit 3%N) )]) None
                      {| stags := NoInfo; str := "ig_intr_dprsr_md" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchEgressParser" |}) nil)
               nil)
          (TypParser
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_in" |})
                      None {| stags := NoInfo; str := "pkt" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false Out
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "eg_md" |});
                 (MkParameter false Out
                      (TypHeader
                       [( {| stags := NoInfo; str := "_pad0" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "enq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad3" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "enq_tstamp" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "_pad4" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad5" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "deq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo;
                             str := "app_pool_congest_stat" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "_pad6" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "_pad7" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_rid_first" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad8" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "egress_qid" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "_pad9" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "egress_cos" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "_pad10" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "deflection_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "pkt_length" |},
                          (TypBit 16%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_md" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchEgress" |}) nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "eg_md" |});
                 (MkParameter false In
                      (TypHeader
                       [( {| stags := NoInfo; str := "_pad0" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_port" |},
                          (TypBit 9%N) );
                        ( {| stags := NoInfo; str := "_pad1" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "enq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad2" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "enq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo; str := "_pad3" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "enq_tstamp" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "_pad4" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "deq_qdepth" |},
                          (TypBit 19%N) );
                        ( {| stags := NoInfo; str := "_pad5" |},
                          (TypBit 6%N) );
                        ( {| stags := NoInfo; str := "deq_congest_stat" |},
                          (TypBit 2%N) );
                        ( {| stags := NoInfo;
                             str := "app_pool_congest_stat" |},
                          (TypBit 8%N) );
                        ( {| stags := NoInfo; str := "_pad6" |},
                          (TypBit 14%N) );
                        ( {| stags := NoInfo; str := "deq_timedelta" |},
                          (TypBit 18%N) );
                        ( {| stags := NoInfo; str := "egress_rid" |},
                          (TypBit 16%N) );
                        ( {| stags := NoInfo; str := "_pad7" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "egress_rid_first" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "_pad8" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "egress_qid" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "_pad9" |},
                          (TypBit 5%N) );
                        ( {| stags := NoInfo; str := "egress_cos" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "_pad10" |},
                          (TypBit 7%N) );
                        ( {| stags := NoInfo; str := "deflection_flag" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "pkt_length" |},
                          (TypBit 16%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_md" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "global_tstamp" |},
                          (TypBit 48%N) );
                        ( {| stags := NoInfo; str := "global_ver" |},
                          (TypBit 32%N) );
                        ( {| stags := NoInfo; str := "parser_err" |},
                          (TypBit 16%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_from_prsr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "drop_ctl" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "mirror_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "coalesce_flush" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "coalesce_length" |},
                          (TypBit 7%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_md_for_dprsr" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo;
                             str := "capture_tstamp_on_tx" |}, (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "update_delay_on_tx" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "force_tx_error" |},
                          (TypBit 1%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_md_for_oport" |})]))
          Directionless);
     (MkExpression NoInfo
          (ExpNamelessInstantiation
               (TypSpecializedType
                    (TypTypeName
                     {| stags := NoInfo; str := "SwitchEgressDeparser" |})
                    nil) nil)
          (TypControl
           (MkControlType nil
                [(MkParameter false Directionless
                      (TypExtern {| stags := NoInfo; str := "packet_out" |})
                      None {| stags := NoInfo; str := "pkt" |});
                 (MkParameter false InOut
                      (TypStruct
                       [( {| stags := NoInfo; str := "bridge" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "contains_sample" |},
                              (TypBit 8%N) )]) );
                        ( {| stags := NoInfo; str := "sample" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dmac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "smac" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "etype" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "srcip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dstip" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "num_pkts" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "ethernet" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 48%N) );
                            ( {| stags := NoInfo; str := "ether_type" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "ipv4" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "version" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "ihl" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "diffserv" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "total_len" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "identification" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 3%N) );
                            ( {| stags := NoInfo; str := "frag_offset" |},
                              (TypBit 13%N) );
                            ( {| stags := NoInfo; str := "ttl" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "protocol" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "hdr_checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "src_addr" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "dst_addr" |},
                              (TypBit 32%N) )]) );
                        ( {| stags := NoInfo; str := "tcp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "seq_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "ack_no" |},
                              (TypBit 32%N) );
                            ( {| stags := NoInfo; str := "data_offset" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "res" |},
                              (TypBit 4%N) );
                            ( {| stags := NoInfo; str := "flags" |},
                              (TypBit 8%N) );
                            ( {| stags := NoInfo; str := "window" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "urgent_ptr" |},
                              (TypBit 16%N) )]) );
                        ( {| stags := NoInfo; str := "udp" |},
                          (TypHeader
                           [( {| stags := NoInfo; str := "src_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "dst_port" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "hdr_length" |},
                              (TypBit 16%N) );
                            ( {| stags := NoInfo; str := "checksum" |},
                              (TypBit 16%N) )]) )]) None
                      {| stags := NoInfo; str := "hdr" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "num_pkts" |},
                          (TypBit 32%N) )]) None
                      {| stags := NoInfo; str := "eg_md" |});
                 (MkParameter false In
                      (TypStruct
                       [( {| stags := NoInfo; str := "drop_ctl" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "mirror_type" |},
                          (TypBit 3%N) );
                        ( {| stags := NoInfo; str := "coalesce_flush" |},
                          (TypBit 1%N) );
                        ( {| stags := NoInfo; str := "coalesce_length" |},
                          (TypBit 7%N) )]) None
                      {| stags := NoInfo; str := "eg_intr_dprsr_md" |})]))
          Directionless)] {| stags := NoInfo; str := "pipe" |} nil.

Definition main := DeclInstantiation NoInfo
    (TypSpecializedType (TypTypeName {| stags := NoInfo; str := "Switch" |})
         [(TypStruct
           [( {| stags := NoInfo; str := "bridge" |},
              (TypHeader
               [( {| stags := NoInfo; str := "contains_sample" |},
                  (TypBit 8%N) )]) );
            ( {| stags := NoInfo; str := "sample" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dmac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "smac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etype" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "srcip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dstip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "ether_type" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "ipv4" |},
              (TypHeader
               [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "total_len" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "identification" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
                ( {| stags := NoInfo; str := "frag_offset" |},
                  (TypBit 13%N) );
                ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "hdr_checksum" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "tcp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "seq_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ack_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "data_offset" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "urgent_ptr" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "udp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "hdr_length" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "bridge" |},
              (TypHeader
               [( {| stags := NoInfo; str := "contains_sample" |},
                  (TypBit 8%N) )]) );
            ( {| stags := NoInfo; str := "sample" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dmac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "smac" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "etype" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "srcip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dstip" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "ethernet" |},
              (TypHeader
               [( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 48%N) );
                ( {| stags := NoInfo; str := "ether_type" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "ipv4" |},
              (TypHeader
               [( {| stags := NoInfo; str := "version" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "ihl" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "diffserv" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "total_len" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "identification" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 3%N) );
                ( {| stags := NoInfo; str := "frag_offset" |},
                  (TypBit 13%N) );
                ( {| stags := NoInfo; str := "ttl" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "protocol" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "hdr_checksum" |},
                  (TypBit 16%N) );
                ( {| stags := NoInfo; str := "src_addr" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "dst_addr" |}, (TypBit 32%N) )]) );
            ( {| stags := NoInfo; str := "tcp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "seq_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "ack_no" |}, (TypBit 32%N) );
                ( {| stags := NoInfo; str := "data_offset" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "res" |}, (TypBit 4%N) );
                ( {| stags := NoInfo; str := "flags" |}, (TypBit 8%N) );
                ( {| stags := NoInfo; str := "window" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "urgent_ptr" |}, (TypBit 16%N) )]) );
            ( {| stags := NoInfo; str := "udp" |},
              (TypHeader
               [( {| stags := NoInfo; str := "src_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "dst_port" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "hdr_length" |}, (TypBit 16%N) );
                ( {| stags := NoInfo; str := "checksum" |}, (TypBit 16%N) )]) )]);
          (TypStruct
           [( {| stags := NoInfo; str := "num_pkts" |}, (TypBit 32%N) )]);
          TypVoid; TypVoid; TypVoid; TypVoid; TypVoid; TypVoid; TypVoid;
          TypVoid; TypVoid; TypVoid; TypVoid; TypVoid])
    [(MkExpression NoInfo
          (ExpName (BareName {| stags := NoInfo; str := "pipe" |})
           (LGlobal ["missing_locator"]))
          (TypPackage nil nil
               [(MkParameter false Directionless
                     (TypSpecializedType
                          (TypParser
                           (MkControlType
                                [{| stags := NoInfo; str := "H38" |};
                                 {| stags := NoInfo; str := "M" |}]
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_in" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H38" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M" |})
                                      None
                                      {| stags := NoInfo; str := "ig_md" |});
                                 (MkParameter true Out
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "resubmit_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_version" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_mac_tstamp" |},
                                          (TypBit 48%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md" |});
                                 (MkParameter true Out
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "ucast_egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "bypass_egress" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflect_on_drop" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo; str := "qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "icos_for_copy_to_cpu" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "copy_to_cpu" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_color" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "disable_ucast_cutthru" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "enable_mcast_cutthru" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "mcast_grp_a" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "mcast_grp_b" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "level1_mcast_hash" |},
                                          (TypBit 13%N) );
                                        ( {| stags := NoInfo;
                                             str := "level2_mcast_hash" |},
                                          (TypBit 13%N) );
                                        ( {| stags := NoInfo;
                                             str := "level1_exclusion_id" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "level2_exclusion_id" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo; str := "rid" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_for_tm" |});
                                 (MkParameter true Out
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "global_tstamp" |},
                                          (TypBit 48%N) );
                                        ( {| stags := NoInfo;
                                             str := "global_ver" |},
                                          (TypBit 32%N) );
                                        ( {| stags := NoInfo;
                                             str := "parser_err" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_from_prsr" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "ingress_parser" |});
                (MkParameter false Directionless
                     (TypSpecializedType
                          (TypControl
                           (MkControlType
                                [{| stags := NoInfo; str := "H41" |};
                                 {| stags := NoInfo; str := "M42" |}]
                                [(MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H41" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M42" |})
                                      None
                                      {| stags := NoInfo; str := "ig_md" |});
                                 (MkParameter true In
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "resubmit_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_version" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_mac_tstamp" |},
                                          (TypBit 48%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md" |});
                                 (MkParameter true In
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "global_tstamp" |},
                                          (TypBit 48%N) );
                                        ( {| stags := NoInfo;
                                             str := "global_ver" |},
                                          (TypBit 32%N) );
                                        ( {| stags := NoInfo;
                                             str := "parser_err" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_from_prsr" |});
                                 (MkParameter true InOut
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "drop_ctl" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "digest_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "resubmit_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "mirror_type" |},
                                          (TypBit 3%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_for_dprsr" |});
                                 (MkParameter true InOut
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "ucast_egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "bypass_egress" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflect_on_drop" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo; str := "qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "icos_for_copy_to_cpu" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "copy_to_cpu" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_color" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "disable_ucast_cutthru" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "enable_mcast_cutthru" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "mcast_grp_a" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "mcast_grp_b" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "level1_mcast_hash" |},
                                          (TypBit 13%N) );
                                        ( {| stags := NoInfo;
                                             str := "level2_mcast_hash" |},
                                          (TypBit 13%N) );
                                        ( {| stags := NoInfo;
                                             str := "level1_exclusion_id" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "level2_exclusion_id" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo; str := "rid" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_for_tm" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "ingress" |});
                (MkParameter false Directionless
                     (TypSpecializedType
                          (TypControl
                           (MkControlType
                                [{| stags := NoInfo; str := "H45" |};
                                 {| stags := NoInfo; str := "M46" |}]
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_out" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H45" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false In
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M46" |})
                                      None
                                      {| stags := NoInfo;
                                         str := "metadata" |});
                                 (MkParameter true In
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "drop_ctl" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "digest_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "resubmit_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "mirror_type" |},
                                          (TypBit 3%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md_for_dprsr" |});
                                 (MkParameter true In
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "resubmit_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "packet_version" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "ingress_mac_tstamp" |},
                                          (TypBit 48%N) )]) None
                                      {| stags := NoInfo;
                                         str := "ig_intr_md" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "ingress_deparser" |});
                (MkParameter false Directionless
                     (TypSpecializedType
                          (TypParser
                           (MkControlType
                                [{| stags := NoInfo; str := "H39" |};
                                 {| stags := NoInfo; str := "M40" |}]
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_in" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H39" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false Out
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M40" |})
                                      None
                                      {| stags := NoInfo; str := "eg_md" |});
                                 (MkParameter true Out
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "_pad0" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad3" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_tstamp" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad4" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad5" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "app_pool_congest_stat" |},
                                          (TypBit 8%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad6" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_timedelta" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad7" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid_first" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad8" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad9" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad10" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflection_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "pkt_length" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md" |});
                                 (MkParameter true Out
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "global_tstamp" |},
                                          (TypBit 48%N) );
                                        ( {| stags := NoInfo;
                                             str := "global_ver" |},
                                          (TypBit 32%N) );
                                        ( {| stags := NoInfo;
                                             str := "parser_err" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_from_prsr" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "egress_parser" |});
                (MkParameter false Directionless
                     (TypSpecializedType
                          (TypControl
                           (MkControlType
                                [{| stags := NoInfo; str := "H43" |};
                                 {| stags := NoInfo; str := "M44" |}]
                                [(MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H43" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M44" |})
                                      None
                                      {| stags := NoInfo; str := "eg_md" |});
                                 (MkParameter true In
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "_pad0" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad3" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_tstamp" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad4" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad5" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "app_pool_congest_stat" |},
                                          (TypBit 8%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad6" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_timedelta" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad7" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid_first" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad8" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad9" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad10" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflection_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "pkt_length" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md" |});
                                 (MkParameter true In
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "global_tstamp" |},
                                          (TypBit 48%N) );
                                        ( {| stags := NoInfo;
                                             str := "global_ver" |},
                                          (TypBit 32%N) );
                                        ( {| stags := NoInfo;
                                             str := "parser_err" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_from_prsr" |});
                                 (MkParameter true InOut
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "drop_ctl" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "mirror_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "coalesce_flush" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "coalesce_length" |},
                                          (TypBit 7%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_for_dprsr" |});
                                 (MkParameter true InOut
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "capture_tstamp_on_tx" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "update_delay_on_tx" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "force_tx_error" |},
                                          (TypBit 1%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_for_oport" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "egress" |});
                (MkParameter false Directionless
                     (TypSpecializedType
                          (TypControl
                           (MkControlType
                                [{| stags := NoInfo; str := "H47" |};
                                 {| stags := NoInfo; str := "M48" |}]
                                [(MkParameter false Directionless
                                      (TypExtern
                                       {| stags := NoInfo;
                                          str := "packet_out" |}) None
                                      {| stags := NoInfo; str := "pkt" |});
                                 (MkParameter false InOut
                                      (TypTypeName
                                       {| stags := NoInfo; str := "H47" |})
                                      None
                                      {| stags := NoInfo; str := "hdr" |});
                                 (MkParameter false In
                                      (TypTypeName
                                       {| stags := NoInfo; str := "M48" |})
                                      None
                                      {| stags := NoInfo;
                                         str := "metadata" |});
                                 (MkParameter true In
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "drop_ctl" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "mirror_type" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "coalesce_flush" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "coalesce_length" |},
                                          (TypBit 7%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_for_dprsr" |});
                                 (MkParameter true In
                                      (TypHeader
                                       [( {| stags := NoInfo;
                                             str := "_pad0" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_port" |},
                                          (TypBit 9%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad1" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad2" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad3" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "enq_tstamp" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad4" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_qdepth" |},
                                          (TypBit 19%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad5" |},
                                          (TypBit 6%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_congest_stat" |},
                                          (TypBit 2%N) );
                                        ( {| stags := NoInfo;
                                             str := "app_pool_congest_stat" |},
                                          (TypBit 8%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad6" |},
                                          (TypBit 14%N) );
                                        ( {| stags := NoInfo;
                                             str := "deq_timedelta" |},
                                          (TypBit 18%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid" |},
                                          (TypBit 16%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad7" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_rid_first" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad8" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_qid" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad9" |},
                                          (TypBit 5%N) );
                                        ( {| stags := NoInfo;
                                             str := "egress_cos" |},
                                          (TypBit 3%N) );
                                        ( {| stags := NoInfo;
                                             str := "_pad10" |},
                                          (TypBit 7%N) );
                                        ( {| stags := NoInfo;
                                             str := "deflection_flag" |},
                                          (TypBit 1%N) );
                                        ( {| stags := NoInfo;
                                             str := "pkt_length" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md" |});
                                 (MkParameter true In
                                      (TypStruct
                                       [( {| stags := NoInfo;
                                             str := "global_tstamp" |},
                                          (TypBit 48%N) );
                                        ( {| stags := NoInfo;
                                             str := "global_ver" |},
                                          (TypBit 32%N) );
                                        ( {| stags := NoInfo;
                                             str := "parser_err" |},
                                          (TypBit 16%N) )]) None
                                      {| stags := NoInfo;
                                         str := "eg_intr_md_from_prsr" |})]))
                          [(TypStruct
                            [( {| stags := NoInfo; str := "bridge" |},
                               (TypHeader
                                [( {| stags := NoInfo;
                                      str := "contains_sample" |},
                                   (TypBit 8%N) )]) );
                             ( {| stags := NoInfo; str := "sample" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dmac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "smac" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "etype" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "srcip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dstip" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "num_pkts" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "ethernet" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 48%N) );
                                 ( {| stags := NoInfo; str := "ether_type" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "ipv4" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "version" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "ihl" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "diffserv" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "total_len" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo;
                                      str := "identification" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 3%N) );
                                 ( {| stags := NoInfo;
                                      str := "frag_offset" |},
                                   (TypBit 13%N) );
                                 ( {| stags := NoInfo; str := "ttl" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "protocol" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo;
                                      str := "hdr_checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "src_addr" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "dst_addr" |},
                                   (TypBit 32%N) )]) );
                             ( {| stags := NoInfo; str := "tcp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "seq_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo; str := "ack_no" |},
                                   (TypBit 32%N) );
                                 ( {| stags := NoInfo;
                                      str := "data_offset" |}, (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "res" |},
                                   (TypBit 4%N) );
                                 ( {| stags := NoInfo; str := "flags" |},
                                   (TypBit 8%N) );
                                 ( {| stags := NoInfo; str := "window" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "urgent_ptr" |},
                                   (TypBit 16%N) )]) );
                             ( {| stags := NoInfo; str := "udp" |},
                               (TypHeader
                                [( {| stags := NoInfo; str := "src_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "dst_port" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "hdr_length" |},
                                   (TypBit 16%N) );
                                 ( {| stags := NoInfo; str := "checksum" |},
                                   (TypBit 16%N) )]) )]);
                           (TypStruct
                            [( {| stags := NoInfo; str := "num_pkts" |},
                               (TypBit 32%N) )])]) None
                     {| stags := NoInfo; str := "egress_deparser" |})])
          Directionless)] {| stags := NoInfo; str := "main" |} nil.

Definition prog := Program
    [decl'1; packet_in; packet_out; verify'check'toSignal; NoAction; decl'2;
     PortId_t; MulticastGroupId_t; QueueId_t; MirrorType_t; MirrorId_t;
     ResubmitType_t; DigestType_t; ReplicationId_t; ParserError_t;
     PORT_METADATA_SIZE; PARSER_ERROR_OK; PARSER_ERROR_NO_MATCH;
     PARSER_ERROR_PARTIAL_HDR; PARSER_ERROR_CTR_RANGE;
     PARSER_ERROR_TIMEOUT_USER; PARSER_ERROR_TIMEOUT_HW;
     PARSER_ERROR_SRC_EXT; PARSER_ERROR_DST_CONT; PARSER_ERROR_PHV_OWNER;
     PARSER_ERROR_MULTIWRITE; PARSER_ERROR_ARAM_MBE; PARSER_ERROR_FCS;
     MeterType_t; MeterColor_t; CounterType_t; SelectorMode_t;
     HashAlgorithm_t; decl'3; decl'4; ingress_intrinsic_metadata_t;
     ingress_intrinsic_metadata_for_tm_t;
     ingress_intrinsic_metadata_from_parser_t;
     ingress_intrinsic_metadata_for_deparser_t; egress_intrinsic_metadata_t;
     egress_intrinsic_metadata_from_parser_t;
     egress_intrinsic_metadata_for_deparser_t;
     egress_intrinsic_metadata_for_output_port_t; pktgen_timer_header_t;
     pktgen_port_down_header_t; pktgen_recirc_header_t; ptp_metadata_t;
     Checksum; ParserCounter; ParserPriority; CRCPolynomial; Hash; Random;
     max't1't2; min't1't2; funnel_shift_right'dst'src1'src2'shift_amount;
     invalidate'field; port_metadata_unpack'pkt; sizeInBits'h; sizeInBytes'h;
     Counter; DirectCounter; Meter; DirectMeter; Lpf; DirectLpf; Wred;
     DirectWred; Register; DirectRegister; RegisterParam; MathOp_t; MathUnit;
     RegisterAction; DirectRegisterAction; ActionProfile; ActionSelector;
     SelectorAction; Mirror; Resubmit; Digest; Atcam; Alpm; IngressParserT;
     EgressParserT; IngressT; EgressT; IngressDeparserT; EgressDeparserT;
     Pipeline; Switch; IngressParsers; EgressParsers; MultiParserPipeline;
     MultiParserSwitch; mac_addr_t; ipv4_addr_t; ipv6_addr_t; vlan_id_t;
     ether_type_t; ETHERTYPE_IPV4; ETHERTYPE_ARP; ETHERTYPE_IPV6;
     ETHERTYPE_VLAN; ip_protocol_t; IP_PROTOCOLS_ICMP; IP_PROTOCOLS_TCP;
     IP_PROTOCOLS_UDP; ethernet_h; vlan_tag_h; mpls_h; ipv4_h; ipv6_h; tcp_h;
     udp_h; icmp_h; arp_h; ipv6_srh_h; vxlan_h; gre_h; header_t;
     empty_header_t; empty_metadata_t; TofinoIngressParser;
     TofinoEgressParser; BypassEgress; EmptyEgressParser;
     EmptyEgressDeparser; EmptyEgress; bridge_t; sample_t; header_sample_t;
     metadata_t; SwitchIngressParser; SwitchIngress; SwitchIngressDeparser;
     SwitchEgressParser; SwitchEgress; SwitchEgressDeparser; pipe; main].
