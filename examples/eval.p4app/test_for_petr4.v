open Petr4
open P4light
let decl'1 = DeclError (Info.dummy,
    [{  tags = Info.dummy; str = "NoError" };
     {  tags = Info.dummy; str = "PacketTooShort" };
     {  tags = Info.dummy; str = "NoMatch" };
     {  tags = Info.dummy; str = "StackOutOfBounds" };
     {  tags = Info.dummy; str = "HeaderTooShort" };
     {  tags = Info.dummy; str = "ParserTimeout" };
     {  tags = Info.dummy; str = "ParserInvalidArgument" }]);;

let decl'packet_in = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "packet_in" }, [],
    [(ProtoMethod (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "length" }, [], []));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "advance" }, [],
          [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "sizeInBits" }))]));
     (ProtoMethod (Info.dummy,
          (TypTypeName {  tags = Info.dummy; str = "T1" }),
          {  tags = Info.dummy; str = "lookahead" },
          [{  tags = Info.dummy; str = "T1" }], []));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "extract" },
          [{  tags = Info.dummy; str = "T0" }],
          [(MkParameter (false, Out,
                (TypTypeName {  tags = Info.dummy; str = "T0" }), None,
                {  tags = Info.dummy; str = "variableSizeHeader" }));
           (MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "variableFieldSizeInBits" }))]));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "extract" },
          [{  tags = Info.dummy; str = "T" }],
          [(MkParameter (false, Out,
                (TypTypeName {  tags = Info.dummy; str = "T" }), None,
                {  tags = Info.dummy; str = "hdr" }))]))]);;

let decl'packet_out = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "packet_out" }, [],
    [(ProtoMethod (Info.dummy, TypVoid, {  tags = Info.dummy; str = "emit" },
          [{  tags = Info.dummy; str = "T2" }],
          [(MkParameter (false, In,
                (TypTypeName {  tags = Info.dummy; str = "T2" }), None,
                {  tags = Info.dummy; str = "hdr" }))]))]);;

let verify'check'toSignal = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "verify" }, [],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "check" }));
     (MkParameter (false, In, TypError, None,
          {  tags = Info.dummy; str = "toSignal" }))]);;

let decl'NoAction = DeclAction (Info.dummy,
    {  tags = Info.dummy; str = "NoAction" }, [], [],
    (BlockEmpty Info.dummy));;

let decl'2 = DeclMatchKind (Info.dummy,
    [{  tags = Info.dummy; str = "exact" };
     {  tags = Info.dummy; str = "ternary" };
     {  tags = Info.dummy; str = "lpm" }]);;

let decl'3 = DeclMatchKind (Info.dummy,
    [{  tags = Info.dummy; str = "range" };
     {  tags = Info.dummy; str = "selector" }]);;

let decl'standard_metadata_t = DeclStruct (Info.dummy,
    {  tags = Info.dummy; str = "standard_metadata_t" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 9)),
          {  tags = Info.dummy; str = "ingress_port" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 9)),
          {  tags = Info.dummy; str = "egress_spec" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 9)),
          {  tags = Info.dummy; str = "egress_port" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "instance_type" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "packet_length" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "enq_timestamp" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 19)),
          {  tags = Info.dummy; str = "enq_qdepth" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "deq_timedelta" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 19)),
          {  tags = Info.dummy; str = "deq_qdepth" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 48)),
          {  tags = Info.dummy; str = "ingress_global_timestamp" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 48)),
          {  tags = Info.dummy; str = "egress_global_timestamp" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "mcast_grp" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "egress_rid" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 1)),
          {  tags = Info.dummy; str = "checksum_error" }));
     (MkDeclarationField (Info.dummy, TypError,
          {  tags = Info.dummy; str = "parser_error" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 3)),
          {  tags = Info.dummy; str = "priority" }))]);;

let decl'CounterType = DeclEnum (Info.dummy,
    {  tags = Info.dummy; str = "CounterType" },
    [{  tags = Info.dummy; str = "packets" };
     {  tags = Info.dummy; str = "bytes" };
     {  tags = Info.dummy; str = "packets_and_bytes" }]);;

let decl'MeterType = DeclEnum (Info.dummy,
    {  tags = Info.dummy; str = "MeterType" },
    [{  tags = Info.dummy; str = "packets" };
     {  tags = Info.dummy; str = "bytes" }]);;

let decl'counter = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "counter" }, [],
    [(ProtoConstructor (Info.dummy, {  tags = Info.dummy; str = "counter" },
          [(MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "size" }));
           (MkParameter (false, Directionless,
                (TypTypeName {  tags = Info.dummy; str = "CounterType" }),
                None, {  tags = Info.dummy; str = "type" }))]));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "count" }, [],
          [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "index" }))]))]);;

let decl'direct_counter = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "direct_counter" }, [],
    [(ProtoConstructor (Info.dummy,
          {  tags = Info.dummy; str = "direct_counter" },
          [(MkParameter (false, Directionless,
                (TypTypeName {  tags = Info.dummy; str = "CounterType" }),
                None, {  tags = Info.dummy; str = "type" }))]));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "count" }, [], []))]);;

let decl'meter = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "meter" }, [],
    [(ProtoConstructor (Info.dummy, {  tags = Info.dummy; str = "meter" },
          [(MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "size" }));
           (MkParameter (false, Directionless,
                (TypTypeName {  tags = Info.dummy; str = "MeterType" }),
                None, {  tags = Info.dummy; str = "type" }))]));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "execute_meter" },
          [{  tags = Info.dummy; str = "T3" }],
          [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "index" }));
           (MkParameter (false, Out,
                (TypTypeName {  tags = Info.dummy; str = "T3" }), None,
                {  tags = Info.dummy; str = "result" }))]))]);;

let decl'direct_meter = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "direct_meter" },
    [{  tags = Info.dummy; str = "T4" }],
    [(ProtoConstructor (Info.dummy,
          {  tags = Info.dummy; str = "direct_meter" },
          [(MkParameter (false, Directionless,
                (TypTypeName {  tags = Info.dummy; str = "MeterType" }),
                None, {  tags = Info.dummy; str = "type" }))]));
     (ProtoMethod (Info.dummy, TypVoid, {  tags = Info.dummy; str = "read" },
          [],
          [(MkParameter (false, Out,
                (TypTypeName {  tags = Info.dummy; str = "T4" }), None,
                {  tags = Info.dummy; str = "result" }))]))]);;

let decl'register = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "register" },
    [{  tags = Info.dummy; str = "T5" }],
    [(ProtoConstructor (Info.dummy, {  tags = Info.dummy; str = "register" },
          [(MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "size" }))]));
     (ProtoMethod (Info.dummy, TypVoid,
          {  tags = Info.dummy; str = "write" }, [],
          [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "index" }));
           (MkParameter (false, In,
                (TypTypeName {  tags = Info.dummy; str = "T5" }), None,
                {  tags = Info.dummy; str = "value" }))]));
     (ProtoMethod (Info.dummy, TypVoid, {  tags = Info.dummy; str = "read" },
          [],
          [(MkParameter (false, Out,
                (TypTypeName {  tags = Info.dummy; str = "T5" }), None,
                {  tags = Info.dummy; str = "result" }));
           (MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
                {  tags = Info.dummy; str = "index" }))]))]);;

let decl'action_profile = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "action_profile" }, [],
    [(ProtoConstructor (Info.dummy,
          {  tags = Info.dummy; str = "action_profile" },
          [(MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "size" }))]))]);;

let random'result'lo'hi = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "random" },
    [{  tags = Info.dummy; str = "T6" }],
    [(MkParameter (false, Out,
          (TypTypeName {  tags = Info.dummy; str = "T6" }), None,
          {  tags = Info.dummy; str = "result" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T6" }), None,
          {  tags = Info.dummy; str = "lo" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T6" }), None,
          {  tags = Info.dummy; str = "hi" }))]);;

let digest'receiver'data = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "digest" },
    [{  tags = Info.dummy; str = "T7" }],
    [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
          {  tags = Info.dummy; str = "receiver" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T7" }), None,
          {  tags = Info.dummy; str = "data" }))]);;

let decl'HashAlgorithm = DeclEnum (Info.dummy,
    {  tags = Info.dummy; str = "HashAlgorithm" },
    [{  tags = Info.dummy; str = "crc32" };
     {  tags = Info.dummy; str = "crc32_custom" };
     {  tags = Info.dummy; str = "crc16" };
     {  tags = Info.dummy; str = "crc16_custom" };
     {  tags = Info.dummy; str = "random" };
     {  tags = Info.dummy; str = "identity" };
     {  tags = Info.dummy; str = "csum16" };
     {  tags = Info.dummy; str = "xor16" }]);;

let mark_to_drop = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "mark_to_drop" }, [], []);;

let mark_to_drop'standard_metadata = DeclExternFunction (Info.dummy, 
    TypVoid, {  tags = Info.dummy; str = "mark_to_drop" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "standard_metadata" }))]);;

let hash'result'algo'base'data'max = DeclExternFunction (Info.dummy, 
    TypVoid, {  tags = Info.dummy; str = "hash" },
    [{  tags = Info.dummy; str = "O" }; {  tags = Info.dummy; str = "T8" };
     {  tags = Info.dummy; str = "D" }; {  tags = Info.dummy; str = "M" }],
    [(MkParameter (false, Out,
          (TypTypeName {  tags = Info.dummy; str = "O" }), None,
          {  tags = Info.dummy; str = "result" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }), 
          None, {  tags = Info.dummy; str = "algo" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T8" }), None,
          {  tags = Info.dummy; str = "base" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "D" }), None,
          {  tags = Info.dummy; str = "data" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "M" }), None,
          {  tags = Info.dummy; str = "max" }))]);;

let decl'action_selector = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "action_selector" }, [],
    [(ProtoConstructor (Info.dummy,
          {  tags = Info.dummy; str = "action_selector" },
          [(MkParameter (false, Directionless,
                (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }),
                None, {  tags = Info.dummy; str = "algorithm" }));
           (MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "size" }));
           (MkParameter (false, Directionless, (TypBit (Bigint.of_int 32)),
                None, {  tags = Info.dummy; str = "outputWidth" }))]))]);;

let decl'CloneType = DeclEnum (Info.dummy,
    {  tags = Info.dummy; str = "CloneType" },
    [{  tags = Info.dummy; str = "I2E" };
     {  tags = Info.dummy; str = "E2E" }]);;

let decl'Checksum16 = DeclExternObject (Info.dummy,
    {  tags = Info.dummy; str = "Checksum16" }, [],
    [(ProtoConstructor (Info.dummy,
          {  tags = Info.dummy; str = "Checksum16" }, []));
     (ProtoMethod (Info.dummy, (TypBit (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "get" },
          [{  tags = Info.dummy; str = "D9" }],
          [(MkParameter (false, In,
                (TypTypeName {  tags = Info.dummy; str = "D9" }), None,
                {  tags = Info.dummy; str = "data" }))]))]);;

let verify_checksum'condition'data'checksum'algo = DeclExternFunction
    (Info.dummy, TypVoid, {  tags = Info.dummy; str = "verify_checksum" },
    [{  tags = Info.dummy; str = "T10" };
     {  tags = Info.dummy; str = "O11" }],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "condition" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T10" }), None,
          {  tags = Info.dummy; str = "data" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "O11" }), None,
          {  tags = Info.dummy; str = "checksum" }));
     (MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }), 
          None, {  tags = Info.dummy; str = "algo" }))]);;

let update_checksum'condition'data'checksum'algo = DeclExternFunction
    (Info.dummy, TypVoid, {  tags = Info.dummy; str = "update_checksum" },
    [{  tags = Info.dummy; str = "T12" };
     {  tags = Info.dummy; str = "O13" }],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "condition" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T12" }), None,
          {  tags = Info.dummy; str = "data" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "O13" }), None,
          {  tags = Info.dummy; str = "checksum" }));
     (MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }), 
          None, {  tags = Info.dummy; str = "algo" }))]);;

let verify_checksum_with_payload'condition'data'checksum'algo = DeclExternFunction
    (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "verify_checksum_with_payload" },
    [{  tags = Info.dummy; str = "T14" };
     {  tags = Info.dummy; str = "O15" }],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "condition" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T14" }), None,
          {  tags = Info.dummy; str = "data" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "O15" }), None,
          {  tags = Info.dummy; str = "checksum" }));
     (MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }), 
          None, {  tags = Info.dummy; str = "algo" }))]);;

let update_checksum_with_payload'condition'data'checksum'algo = DeclExternFunction
    (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "update_checksum_with_payload" },
    [{  tags = Info.dummy; str = "T16" };
     {  tags = Info.dummy; str = "O17" }],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "condition" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T16" }), None,
          {  tags = Info.dummy; str = "data" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "O17" }), None,
          {  tags = Info.dummy; str = "checksum" }));
     (MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "HashAlgorithm" }), 
          None, {  tags = Info.dummy; str = "algo" }))]);;

let resubmit'data = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "resubmit" },
    [{  tags = Info.dummy; str = "T18" }],
    [(MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T18" }), None,
          {  tags = Info.dummy; str = "data" }))]);;

let recirculate'data = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "recirculate" },
    [{  tags = Info.dummy; str = "T19" }],
    [(MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T19" }), None,
          {  tags = Info.dummy; str = "data" }))]);;

let clone'type'session = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "clone" }, [],
    [(MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "CloneType" }), None,
          {  tags = Info.dummy; str = "type" }));
     (MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
          {  tags = Info.dummy; str = "session" }))]);;

let clone3'type'session'data = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "clone3" },
    [{  tags = Info.dummy; str = "T20" }],
    [(MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "CloneType" }), None,
          {  tags = Info.dummy; str = "type" }));
     (MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
          {  tags = Info.dummy; str = "session" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "T20" }), None,
          {  tags = Info.dummy; str = "data" }))]);;

let truncate'length = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "truncate" }, [],
    [(MkParameter (false, In, (TypBit (Bigint.of_int 32)), None,
          {  tags = Info.dummy; str = "length" }))]);;

let assert'check = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "assert" }, [],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "check" }))]);;

let assume'check = DeclExternFunction (Info.dummy, TypVoid,
    {  tags = Info.dummy; str = "assume" }, [],
    [(MkParameter (false, In, TypBool, None,
          {  tags = Info.dummy; str = "check" }))]);;

let decl'Parser = DeclParserType (Info.dummy,
    {  tags = Info.dummy; str = "Parser" },
    [{  tags = Info.dummy; str = "H" }; {  tags = Info.dummy; str = "M21" }],
    [(MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "packet_in" }), None,
          {  tags = Info.dummy; str = "b" }));
     (MkParameter (false, Out,
          (TypTypeName {  tags = Info.dummy; str = "H" }), None,
          {  tags = Info.dummy; str = "parsedHdr" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "M21" }), None,
          {  tags = Info.dummy; str = "meta" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "standard_metadata" }))]);;

let decl'VerifyChecksum = DeclControlType (Info.dummy,
    {  tags = Info.dummy; str = "VerifyChecksum" },
    [{  tags = Info.dummy; str = "H22" };
     {  tags = Info.dummy; str = "M23" }],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "H22" }), None,
          {  tags = Info.dummy; str = "hdr" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "M23" }), None,
          {  tags = Info.dummy; str = "meta" }))]);;

let decl'Ingress = DeclControlType (Info.dummy,
    {  tags = Info.dummy; str = "Ingress" },
    [{  tags = Info.dummy; str = "H24" };
     {  tags = Info.dummy; str = "M25" }],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "H24" }), None,
          {  tags = Info.dummy; str = "hdr" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "M25" }), None,
          {  tags = Info.dummy; str = "meta" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "standard_metadata" }))]);;

let decl'Egress = DeclControlType (Info.dummy,
    {  tags = Info.dummy; str = "Egress" },
    [{  tags = Info.dummy; str = "H26" };
     {  tags = Info.dummy; str = "M27" }],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "H26" }), None,
          {  tags = Info.dummy; str = "hdr" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "M27" }), None,
          {  tags = Info.dummy; str = "meta" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "standard_metadata" }))]);;

let decl'ComputeChecksum = DeclControlType (Info.dummy,
    {  tags = Info.dummy; str = "ComputeChecksum" },
    [{  tags = Info.dummy; str = "H28" };
     {  tags = Info.dummy; str = "M29" }],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "H28" }), None,
          {  tags = Info.dummy; str = "hdr" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "M29" }), None,
          {  tags = Info.dummy; str = "meta" }))]);;

let decl'Deparser = DeclControlType (Info.dummy,
    {  tags = Info.dummy; str = "Deparser" },
    [{  tags = Info.dummy; str = "H30" }],
    [(MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "packet_out" }), None,
          {  tags = Info.dummy; str = "b" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "H30" }), None,
          {  tags = Info.dummy; str = "hdr" }))]);;

let decl'V1Switch = DeclPackageType (Info.dummy,
    {  tags = Info.dummy; str = "V1Switch" },
    [{  tags = Info.dummy; str = "H31" };
     {  tags = Info.dummy; str = "M32" }],
    [(MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "Parser" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" });
                (TypTypeName {  tags = Info.dummy; str = "M32" })])), 
          None, {  tags = Info.dummy; str = "p" }));
     (MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "VerifyChecksum" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" });
                (TypTypeName {  tags = Info.dummy; str = "M32" })])), 
          None, {  tags = Info.dummy; str = "vr" }));
     (MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "Ingress" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" });
                (TypTypeName {  tags = Info.dummy; str = "M32" })])), 
          None, {  tags = Info.dummy; str = "ig" }));
     (MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "Egress" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" });
                (TypTypeName {  tags = Info.dummy; str = "M32" })])), 
          None, {  tags = Info.dummy; str = "eg" }));
     (MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "ComputeChecksum" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" });
                (TypTypeName {  tags = Info.dummy; str = "M32" })])), 
          None, {  tags = Info.dummy; str = "ck" }));
     (MkParameter (false, Directionless,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "Deparser" }),
               [(TypTypeName {  tags = Info.dummy; str = "H31" })])), 
          None, {  tags = Info.dummy; str = "dep" }))]);;

let decl'hdr = DeclHeader (Info.dummy, {  tags = Info.dummy; str = "hdr" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "input" }));
     (MkDeclarationField (Info.dummy, (TypInt (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "output" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "output2" }))]);;

let decl'meta = DeclStruct (Info.dummy, {  tags = Info.dummy; str = "meta" },
    [(MkDeclarationField (Info.dummy,
          (TypTuple [TypBool; (TypBit (Bigint.of_int 1))]),
          {  tags = Info.dummy; str = "x" }))]);;

let decl'E = DeclSerializableEnum (Info.dummy,
    (TypEnum ({  tags = Info.dummy; str = "E" },
         (Some (TypBit (Bigint.of_int 8))),
         [{  tags = Info.dummy; str = "e1" };
          {  tags = Info.dummy; str = "e2" }])),
    {  tags = Info.dummy; str = "E" },
    [( {  tags = Info.dummy; str = "e1" },
       (MkExpression (Info.dummy,
            (ExpCast ((TypBit (Bigint.of_int 8)),
                 (MkExpression (Info.dummy,
                      (ExpInt
                       {  tags = Info.dummy; value = (Bigint.of_int 1);
                         width_signed = None }), TypInteger, Directionless)))),
            (TypBit (Bigint.of_int 8)), Directionless)) );
     ( {  tags = Info.dummy; str = "e2" },
       (MkExpression (Info.dummy,
            (ExpCast ((TypBit (Bigint.of_int 8)),
                 (MkExpression (Info.dummy,
                      (ExpInt
                       {  tags = Info.dummy; value = (Bigint.of_int 2);
                         width_signed = None }), TypInteger, Directionless)))),
            (TypBit (Bigint.of_int 8)), Directionless)) )]);;

let decl'S = DeclStruct (Info.dummy, {  tags = Info.dummy; str = "S" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "a" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "b" }))]);;

let decl'S1 = DeclStruct (Info.dummy, {  tags = Info.dummy; str = "S1" },
    [(MkDeclarationField (Info.dummy,
          (TypTypeName {  tags = Info.dummy; str = "E" }),
          {  tags = Info.dummy; str = "a" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "b" }))]);;

let decl'S2 = DeclStruct (Info.dummy, {  tags = Info.dummy; str = "S2" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 8)),
          {  tags = Info.dummy; str = "a" }));
     (MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 32)),
          {  tags = Info.dummy; str = "b" }))]);;

let decl'E2 = DeclSerializableEnum (Info.dummy,
    (TypEnum ({  tags = Info.dummy; str = "E2" },
         (Some (TypBit (Bigint.of_int 16))),
         [{  tags = Info.dummy; str = "e3" };
          {  tags = Info.dummy; str = "e4" }])),
    {  tags = Info.dummy; str = "E2" },
    [( {  tags = Info.dummy; str = "e3" },
       (MkExpression (Info.dummy,
            (ExpCast ((TypBit (Bigint.of_int 16)),
                 (MkExpression (Info.dummy,
                      (ExpInt
                       {  tags = Info.dummy; value = (Bigint.of_int 1);
                         width_signed = None }), TypInteger, Directionless)))),
            (TypBit (Bigint.of_int 16)), Directionless)) );
     ( {  tags = Info.dummy; str = "e4" },
       (MkExpression (Info.dummy,
            (ExpCast ((TypBit (Bigint.of_int 16)),
                 (MkExpression (Info.dummy,
                      (ExpInt
                       {  tags = Info.dummy; value = (Bigint.of_int 2);
                         width_signed = None }), TypInteger, Directionless)))),
            (TypBit (Bigint.of_int 16)), Directionless)) )]);;

let decl'k1 = DeclConstant (Info.dummy, (TypBit (Bigint.of_int 16)),
    {  tags = Info.dummy; str = "k1" },
    (MkExpression (Info.dummy,
         (ExpInt
          {  tags = Info.dummy; value = (Bigint.of_int 1);
            width_signed = (Some ( (Bigint.of_int 16), false )) }),
         (TypBit (Bigint.of_int 16)), In)));;

let decl'k2 = DeclConstant (Info.dummy, (TypInt (Bigint.of_int 16)),
    {  tags = Info.dummy; str = "k2" },
    (MkExpression (Info.dummy,
         (ExpInt
          {  tags = Info.dummy; value = (Bigint.of_int 1);
            width_signed = (Some ( (Bigint.of_int 16), true )) }),
         (TypInt (Bigint.of_int 16)), In)));;

let decl'k3 = DeclConstant (Info.dummy, TypInteger,
    {  tags = Info.dummy; str = "k3" },
    (MkExpression (Info.dummy,
         (ExpInt
          {  tags = Info.dummy; value = (Bigint.of_int 1);
            width_signed = None }), TypInteger, In)));;

let decl'k4 = DeclConstant (Info.dummy,
    (TypTypeName {  tags = Info.dummy; str = "E2" }),
    {  tags = Info.dummy; str = "k4" },
    (MkExpression (Info.dummy,
         (ExpTypeMember ({  tags = Info.dummy; str = "E2" },
              {  tags = Info.dummy; str = "e3" })),
         (TypTypeName {  tags = Info.dummy; str = "E2" }), In)));;

let decl'H1 = DeclHeader (Info.dummy, {  tags = Info.dummy; str = "H1" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 8)),
          {  tags = Info.dummy; str = "f" }))]);;

let decl'H2 = DeclHeader (Info.dummy, {  tags = Info.dummy; str = "H2" },
    [(MkDeclarationField (Info.dummy, (TypBit (Bigint.of_int 16)),
          {  tags = Info.dummy; str = "g" }))]);;

let decl'U = DeclHeaderUnion (Info.dummy, {  tags = Info.dummy; str = "U" },
    [(MkDeclarationField (Info.dummy,
          (TypTypeName {  tags = Info.dummy; str = "H1" }),
          {  tags = Info.dummy; str = "h1" }));
     (MkDeclarationField (Info.dummy,
          (TypTypeName {  tags = Info.dummy; str = "H2" }),
          {  tags = Info.dummy; str = "h2" }))]);;

let decl'NewT = DeclNewType (Info.dummy,
    {  tags = Info.dummy; str = "NewT" },
    (Coq_inl (TypBit (Bigint.of_int 8))));;

let decl'compute = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "compute" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "hdr" }), None,
          {  tags = Info.dummy; str = "h" }))], [], [],
    (BlockCons
         ((MkStatement (Info.dummy,
               (StatVariable
                    ((TypTypeName {  tags = Info.dummy; str = "NewT" }),
                    {  tags = Info.dummy; str = "test3" }, None,
                    (LInstance ["test3"]))), StmUnit)),
         (BlockCons
              ((MkStatement (Info.dummy,
                    (StatVariable
                         ((TypTypeName {  tags = Info.dummy; str = "hdr" }),
                         {  tags = Info.dummy; str = "test4" }, None,
                         (LInstance ["test4"]))), StmUnit)),
              (BlockCons
                   ((MkStatement (Info.dummy,
                         (StatVariable
                              ((TypTypeName
                                {  tags = Info.dummy; str = "E" }),
                              {  tags = Info.dummy; str = "e" },
                              (Some
                               (MkExpression (Info.dummy,
                                    (ExpTypeMember
                                         ({  tags = Info.dummy; str = "E" },
                                         {  tags = Info.dummy; str = "e1" })),
                                    (TypEnum
                                         ({  tags = Info.dummy; str = "E" },
                                         (Some (TypBit (Bigint.of_int 8))),
                                         [{  tags = Info.dummy; str = "e1" };
                                          {  tags = Info.dummy; str = "e2" }])),
                                    Directionless))), (LInstance ["e"]))),
                         StmUnit)), (BlockEmpty Info.dummy))))))));;

let decl'Headers = DeclStruct (Info.dummy,
    {  tags = Info.dummy; str = "Headers" },
    [(MkDeclarationField (Info.dummy,
          (TypTypeName {  tags = Info.dummy; str = "hdr" }),
          {  tags = Info.dummy; str = "h" }))]);;

let decl'Meta = DeclStruct (Info.dummy, {  tags = Info.dummy; str = "Meta" },
    []);;

let decl'p = DeclParser (Info.dummy, {  tags = Info.dummy; str = "p" }, [],
    [(MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "packet_in" }), None,
          {  tags = Info.dummy; str = "b" }));
     (MkParameter (false, Out,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Meta" }), None,
          {  tags = Info.dummy; str = "m" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "sm" }))], [], [],
    [(MkParserState (Info.dummy, {  tags = Info.dummy; str = "start" },
          [(MkStatement (Info.dummy,
                (StatMethodCall
                     ((MkExpression (Info.dummy,
                           (ExpExpressionMember
                                ((MkExpression (Info.dummy,
                                      (ExpName
                                       ((BareName
                                         {  tags = Info.dummy; str = "b" }),
                                       LGlobal [])),
                                      (TypTypeName
                                       {  tags = Info.dummy;
                                         str = "packet_in" }),
                                      Directionless)),
                                {  tags = Info.dummy; str = "extract" })),
                           (TypFunction
                            (MkFunctionType
                                 ([{  tags = Info.dummy; str = "T" }],
                                 [(MkParameter (false, Out,
                                       (TypTypeName
                                        {  tags = Info.dummy; str = "T" }),
                                       None,
                                       {  tags = Info.dummy; str = "hdr" }))],
                                 FunExtern, TypVoid))), Directionless)),
                     [(TypHeader
                       [( {  tags = Info.dummy; str = "input" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "output" },
                          (TypInt (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "output2" },
                          (TypBit (Bigint.of_int 32)) )])],
                     [(Some
                       (MkExpression (Info.dummy,
                            (ExpExpressionMember
                                 ((MkExpression (Info.dummy,
                                       (ExpName
                                        ((BareName
                                          {  tags = Info.dummy; str = "h" }),
                                        LGlobal [])),
                                       (TypTypeName
                                        {  tags = Info.dummy;
                                          str = "Headers" }), Out)),
                                 {  tags = Info.dummy; str = "h" })),
                            (TypHeader
                             [( {  tags = Info.dummy; str = "input" },
                                (TypBit (Bigint.of_int 16)) );
                              ( {  tags = Info.dummy; str = "output" },
                                (TypInt (Bigint.of_int 16)) );
                              ( {  tags = Info.dummy; str = "output2" },
                                (TypBit (Bigint.of_int 32)) )]),
                            Directionless)))])), StmUnit))],
          (ParserDirect (Info.dummy, {  tags = Info.dummy; str = "accept" }))))]);;

let decl'vrfy = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "vrfy" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Meta" }), None,
          {  tags = Info.dummy; str = "m" }))], [], [],
    (BlockEmpty Info.dummy));;

let decl'update = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "update" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Meta" }), None,
          {  tags = Info.dummy; str = "m" }))], [], [],
    (BlockEmpty Info.dummy));;

let decl'egress = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "egress" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Meta" }), None,
          {  tags = Info.dummy; str = "m" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "sm" }))], [], [],
    (BlockEmpty Info.dummy));;

let decl'deparser = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "deparser" }, [],
    [(MkParameter (false, Directionless,
          (TypTypeName {  tags = Info.dummy; str = "packet_out" }), None,
          {  tags = Info.dummy; str = "b" }));
     (MkParameter (false, In,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }))], [], [],
    (BlockCons
         ((MkStatement (Info.dummy,
               (StatMethodCall
                    ((MkExpression (Info.dummy,
                          (ExpExpressionMember
                               ((MkExpression (Info.dummy,
                                     (ExpName
                                      ((BareName
                                        {  tags = Info.dummy; str = "b" }),
                                      (LInstance ["b"]))),
                                     (TypTypeName
                                      {  tags = Info.dummy;
                                        str = "packet_out" }),
                                     Directionless)),
                               {  tags = Info.dummy; str = "emit" })),
                          (TypFunction
                           (MkFunctionType
                                ([{  tags = Info.dummy; str = "T2" }],
                                [(MkParameter (false, In,
                                      (TypTypeName
                                       {  tags = Info.dummy; str = "T2" }),
                                      None,
                                      {  tags = Info.dummy; str = "hdr" }))],
                                FunExtern, TypVoid))), Directionless)),
                    [(TypHeader
                      [( {  tags = Info.dummy; str = "input" },
                         (TypBit (Bigint.of_int 16)) );
                       ( {  tags = Info.dummy; str = "output" },
                         (TypInt (Bigint.of_int 16)) );
                       ( {  tags = Info.dummy; str = "output2" },
                         (TypBit (Bigint.of_int 32)) )])],
                    [(Some
                      (MkExpression (Info.dummy,
                           (ExpExpressionMember
                                ((MkExpression (Info.dummy,
                                      (ExpName
                                       ((BareName
                                         {  tags = Info.dummy; str = "h" }),
                                       (LInstance ["h"]))),
                                      (TypTypeName
                                       {  tags = Info.dummy;
                                         str = "Headers" }), In)),
                                {  tags = Info.dummy; str = "h" })),
                           (TypHeader
                            [( {  tags = Info.dummy; str = "input" },
                               (TypBit (Bigint.of_int 16)) );
                             ( {  tags = Info.dummy; str = "output" },
                               (TypInt (Bigint.of_int 16)) );
                             ( {  tags = Info.dummy; str = "output2" },
                               (TypBit (Bigint.of_int 32)) )]),
                           Directionless)))])), StmUnit)),
         (BlockEmpty Info.dummy))));;

let decl'ingress = DeclControl (Info.dummy,
    {  tags = Info.dummy; str = "ingress" }, [],
    [(MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Headers" }), None,
          {  tags = Info.dummy; str = "h" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "Meta" }), None,
          {  tags = Info.dummy; str = "m" }));
     (MkParameter (false, InOut,
          (TypTypeName {  tags = Info.dummy; str = "standard_metadata_t" }),
          None, {  tags = Info.dummy; str = "sm" }))], [],
    [(DeclInstantiation (Info.dummy,
          (TypSpecializedType
               ((TypTypeName {  tags = Info.dummy; str = "compute" }), [])),
          [], {  tags = Info.dummy; str = "c" }, []))],
    (BlockCons
         ((MkStatement (Info.dummy,
               (StatMethodCall
                    ((MkExpression (Info.dummy,
                          (ExpExpressionMember
                               ((MkExpression (Info.dummy,
                                     (ExpName
                                      ((BareName
                                        {  tags = Info.dummy; str = "c" }),
                                      (LInstance ["c"]))),
                                     (TypControl
                                      (MkControlType ([],
                                           [(MkParameter (false, InOut,
                                                 (TypHeader
                                                  [( {  tags = Info.dummy;
                                                       str = "input" },
                                                     (TypBit
                                                      (Bigint.of_int 16)) );
                                                   ( {  tags = Info.dummy;
                                                       str = "output" },
                                                     (TypInt
                                                      (Bigint.of_int 16)) );
                                                   ( {  tags = Info.dummy;
                                                       str = "output2" },
                                                     (TypBit
                                                      (Bigint.of_int 32)) )]),
                                                 None,
                                                 {  tags = Info.dummy;
                                                   str = "h" }))]))),
                                     Directionless)),
                               {  tags = Info.dummy; str = "apply" })),
                          (TypFunction
                           (MkFunctionType ([],
                                [(MkParameter (false, InOut,
                                      (TypHeader
                                       [( {  tags = Info.dummy;
                                            str = "input" },
                                          (TypBit (Bigint.of_int 16)) );
                                        ( {  tags = Info.dummy;
                                            str = "output" },
                                          (TypInt (Bigint.of_int 16)) );
                                        ( {  tags = Info.dummy;
                                            str = "output2" },
                                          (TypBit (Bigint.of_int 32)) )]),
                                      None,
                                      {  tags = Info.dummy; str = "h" }))],
                                FunControl, TypVoid))), Directionless)), [],
                    [(Some
                      (MkExpression (Info.dummy,
                           (ExpExpressionMember
                                ((MkExpression (Info.dummy,
                                      (ExpName
                                       ((BareName
                                         {  tags = Info.dummy; str = "h" }),
                                       (LInstance ["h"]))),
                                      (TypTypeName
                                       {  tags = Info.dummy;
                                         str = "Headers" }), InOut)),
                                {  tags = Info.dummy; str = "h" })),
                           (TypHeader
                            [( {  tags = Info.dummy; str = "input" },
                               (TypBit (Bigint.of_int 16)) );
                             ( {  tags = Info.dummy; str = "output" },
                               (TypInt (Bigint.of_int 16)) );
                             ( {  tags = Info.dummy; str = "output2" },
                               (TypBit (Bigint.of_int 32)) )]),
                           Directionless)))])), StmUnit)),
         (BlockCons
              ((MkStatement (Info.dummy,
                    (StatAssignment
                         ((MkExpression (Info.dummy,
                               (ExpExpressionMember
                                    ((MkExpression (Info.dummy,
                                          (ExpName
                                           ((BareName
                                             {  tags = Info.dummy;
                                               str = "sm" }),
                                           (LInstance ["sm"]))),
                                          (TypTypeName
                                           {  tags = Info.dummy;
                                             str = "standard_metadata_t" }),
                                          InOut)),
                                    {  tags = Info.dummy;
                                      str = "egress_spec" })),
                               (TypBit (Bigint.of_int 9)), Directionless)),
                         (MkExpression (Info.dummy,
                              (ExpCast ((TypBit (Bigint.of_int 9)),
                                   (MkExpression (Info.dummy,
                                        (ExpInt
                                         {  tags = Info.dummy;
                                           value = (Bigint.of_int 1);
                                           width_signed = None }),
                                        TypInteger, Directionless)))),
                              (TypBit (Bigint.of_int 9)), Directionless)))),
                    StmUnit)), (BlockEmpty Info.dummy))))));;

let decl'main = DeclInstantiation (Info.dummy,
    (TypSpecializedType
         ((TypTypeName {  tags = Info.dummy; str = "V1Switch" }),
         [(TypStruct
           [( {  tags = Info.dummy; str = "h" },
              (TypHeader
               [( {  tags = Info.dummy; str = "input" },
                  (TypBit (Bigint.of_int 16)) );
                ( {  tags = Info.dummy; str = "output" },
                  (TypInt (Bigint.of_int 16)) );
                ( {  tags = Info.dummy; str = "output2" },
                  (TypBit (Bigint.of_int 32)) )]) )]); (TypStruct [])])),
    [(MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "p" }), [])),
               [])),
          (TypParser
           (MkControlType ([],
                [(MkParameter (false, Directionless,
                      (TypExtern {  tags = Info.dummy; str = "packet_in" }),
                      None, {  tags = Info.dummy; str = "b" }));
                 (MkParameter (false, Out,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }));
                 (MkParameter (false, InOut, (TypStruct []), None,
                      {  tags = Info.dummy; str = "m" }));
                 (MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "ingress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_spec" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "instance_type" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "packet_length" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_timestamp" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy; str = "deq_timedelta" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "deq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy;
                            str = "ingress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy;
                            str = "egress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy; str = "mcast_grp" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "egress_rid" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "checksum_error" },
                          (TypBit (Bigint.of_int 1)) );
                        ( {  tags = Info.dummy; str = "parser_error" },
                          TypError );
                        ( {  tags = Info.dummy; str = "priority" },
                          (TypBit (Bigint.of_int 3)) )]), None,
                      {  tags = Info.dummy; str = "sm" }))]))),
          Directionless));
     (MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "vrfy" }),
                     [])), [])),
          (TypControl
           (MkControlType ([],
                [(MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }));
                 (MkParameter (false, InOut, (TypStruct []), None,
                      {  tags = Info.dummy; str = "m" }))]))),
          Directionless));
     (MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "ingress" }),
                     [])), [])),
          (TypControl
           (MkControlType ([],
                [(MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }));
                 (MkParameter (false, InOut, (TypStruct []), None,
                      {  tags = Info.dummy; str = "m" }));
                 (MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "ingress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_spec" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "instance_type" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "packet_length" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_timestamp" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy; str = "deq_timedelta" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "deq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy;
                            str = "ingress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy;
                            str = "egress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy; str = "mcast_grp" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "egress_rid" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "checksum_error" },
                          (TypBit (Bigint.of_int 1)) );
                        ( {  tags = Info.dummy; str = "parser_error" },
                          TypError );
                        ( {  tags = Info.dummy; str = "priority" },
                          (TypBit (Bigint.of_int 3)) )]), None,
                      {  tags = Info.dummy; str = "sm" }))]))),
          Directionless));
     (MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "egress" }),
                     [])), [])),
          (TypControl
           (MkControlType ([],
                [(MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }));
                 (MkParameter (false, InOut, (TypStruct []), None,
                      {  tags = Info.dummy; str = "m" }));
                 (MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "ingress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_spec" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "egress_port" },
                          (TypBit (Bigint.of_int 9)) );
                        ( {  tags = Info.dummy; str = "instance_type" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "packet_length" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_timestamp" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "enq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy; str = "deq_timedelta" },
                          (TypBit (Bigint.of_int 32)) );
                        ( {  tags = Info.dummy; str = "deq_qdepth" },
                          (TypBit (Bigint.of_int 19)) );
                        ( {  tags = Info.dummy;
                            str = "ingress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy;
                            str = "egress_global_timestamp" },
                          (TypBit (Bigint.of_int 48)) );
                        ( {  tags = Info.dummy; str = "mcast_grp" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "egress_rid" },
                          (TypBit (Bigint.of_int 16)) );
                        ( {  tags = Info.dummy; str = "checksum_error" },
                          (TypBit (Bigint.of_int 1)) );
                        ( {  tags = Info.dummy; str = "parser_error" },
                          TypError );
                        ( {  tags = Info.dummy; str = "priority" },
                          (TypBit (Bigint.of_int 3)) )]), None,
                      {  tags = Info.dummy; str = "sm" }))]))),
          Directionless));
     (MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "update" }),
                     [])), [])),
          (TypControl
           (MkControlType ([],
                [(MkParameter (false, InOut,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }));
                 (MkParameter (false, InOut, (TypStruct []), None,
                      {  tags = Info.dummy; str = "m" }))]))),
          Directionless));
     (MkExpression (Info.dummy,
          (ExpNamelessInstantiation
               ((TypSpecializedType
                     ((TypTypeName {  tags = Info.dummy; str = "deparser" }),
                     [])), [])),
          (TypControl
           (MkControlType ([],
                [(MkParameter (false, Directionless,
                      (TypExtern {  tags = Info.dummy; str = "packet_out" }),
                      None, {  tags = Info.dummy; str = "b" }));
                 (MkParameter (false, In,
                      (TypStruct
                       [( {  tags = Info.dummy; str = "h" },
                          (TypHeader
                           [( {  tags = Info.dummy; str = "input" },
                              (TypBit (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output" },
                              (TypInt (Bigint.of_int 16)) );
                            ( {  tags = Info.dummy; str = "output2" },
                              (TypBit (Bigint.of_int 32)) )]) )]), None,
                      {  tags = Info.dummy; str = "h" }))]))),
          Directionless))], {  tags = Info.dummy; str = "main" }, []);;

let prog : program = 
    [decl'1; decl'packet_in; decl'packet_out; verify'check'toSignal;
     decl'NoAction; decl'2; decl'3; decl'standard_metadata_t;
     decl'CounterType; decl'MeterType; decl'counter; decl'direct_counter;
     decl'meter; decl'direct_meter; decl'register; decl'action_profile;
     random'result'lo'hi; digest'receiver'data; decl'HashAlgorithm;
     mark_to_drop; mark_to_drop'standard_metadata;
     hash'result'algo'base'data'max; decl'action_selector; decl'CloneType;
     decl'Checksum16; verify_checksum'condition'data'checksum'algo;
     update_checksum'condition'data'checksum'algo;
     verify_checksum_with_payload'condition'data'checksum'algo;
     update_checksum_with_payload'condition'data'checksum'algo;
     resubmit'data; recirculate'data; clone'type'session;
     clone3'type'session'data; truncate'length; assert'check; assume'check;
     decl'Parser; decl'VerifyChecksum; decl'Ingress; decl'Egress;
     decl'ComputeChecksum; decl'Deparser; decl'V1Switch; decl'hdr; decl'meta;
     decl'E; decl'S; decl'S1; decl'S2; decl'E2; decl'k1; decl'k2; decl'k3;
     decl'k4; decl'H1; decl'H2; decl'U; decl'NewT; decl'compute;
     decl'Headers; decl'Meta; decl'p; decl'vrfy; decl'update; decl'egress;
     decl'deparser; decl'ingress; decl'main];;


