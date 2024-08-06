#define NOOP 0
#define CLEAR 1
#define INSERT 2
#define QUERY 3
#define INSQUERY 4
#define UPDATE 5
#define UPDQUERY 6
#define DONTCARE 0
#define QDEFAULT 0

#define GENERATOR_PORT 196

#include <core.p4>
#include <tna.p4>
#include "common/headers.p4"
#include "common/util.p4"


typedef bit<8> api_t;

typedef bit<16> window_t;

typedef bit<4> pred_t;

typedef bit<18> bf2_index_t;

typedef bit<8> bf2_value_t;

typedef bit<64> bf2_key_t;

struct bf2_win_md_t {
    api_t api;
    bf2_index_t index_1;
    bf2_index_t index_2;
    bf2_index_t index_3;
    bf2_value_t rw_1;
    bf2_value_t rw_2;
    bf2_value_t rw_3;
}

struct bf2_ds_md_t {
    window_t clear_window;
    bf2_index_t clear_index_1;
    bf2_index_t hash_index_1;
    bf2_index_t hash_index_2;
    bf2_index_t hash_index_3;
    bf2_win_md_t win_1;
    bf2_win_md_t win_2;
    bf2_win_md_t win_3;
    bf2_win_md_t win_4;
}

struct metadata_t {
    bf2_key_t bf2_key;
    api_t bf2_api;
    bit<8> solicited;
}

struct window_pair_t {
    window_t lo;
    window_t hi;
}

parser EtherIPTCPUDPParser(packet_in pkt, out header_t hdr)  {
    state start {
        transition parse_ethernet;
    }
    state parse_ethernet {
        pkt.extract(hdr.ethernet);
        transition select(hdr.ethernet.ether_type) {
            ETHERTYPE_IPV4 : parse_ipv4;
            _ : reject;
        }
    }
    state parse_ipv4 {
        pkt.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) {
            IP_PROTOCOLS_TCP : parse_tcp;
            IP_PROTOCOLS_UDP : parse_udp;
            _ : accept;
        }
    }
    state parse_tcp {
        pkt.extract(hdr.tcp);
        transition accept;
    }
    state parse_udp {
        pkt.extract(hdr.udp);
        transition accept;
    }
}

parser SwitchIngressParser(packet_in pkt,
                           out header_t hdr,
                           out metadata_t ig_md,
                           out ingress_intrinsic_metadata_t ig_intr_md)  {
    TofinoIngressParser() tofino_parser;
    EtherIPTCPUDPParser() layer4_parser;
    state start {
        tofino_parser.apply(pkt, ig_intr_md);
        transition select(ig_intr_md.ingress_port) {
            GENERATOR_PORT : accept; // dummy packets by pktgenerator
            _ : parse_layer4_pkt;
        }
    }

    state parse_layer4_pkt {
        layer4_parser.apply(pkt, hdr);
        transition accept;
    }
}

control Bf2BloomFilterRow(in api_t api,
                          in bf2_index_t index,
                          out bf2_value_t rw)  {
    Register<bf2_value_t, bf2_index_t>(32w262144, 8w0) reg_row;
    RegisterAction<bf2_value_t, bf2_index_t, bf2_value_t>(reg_row) regact_insert = {
        void apply(inout bf2_value_t value, out bf2_value_t rv) {
            value = 8w1;
            rv = 8w1;
        }
    };
    action act_insert() {
        rw = regact_insert.execute(index);
    }
    RegisterAction<bf2_value_t, bf2_index_t, bf2_value_t>(reg_row) regact_query = {
        void apply(inout bf2_value_t value, out bf2_value_t rv) {
            rv = value;
        }
    };
    action act_query() {
        rw = regact_query.execute(index);
    }
    RegisterAction<bf2_value_t, bf2_index_t, bf2_value_t>(reg_row) regact_clear = {
        void apply(inout bf2_value_t value, out bf2_value_t rv) {
            value = 8w0;
            rv = 8w0;
        }
    };
    action act_clear() {
        rw = regact_clear.execute(index);
    }
    table tbl_bloom {
        key = {
            api : ternary;
        }
        actions = {
            act_insert();
            act_query();
            act_clear();
            .NoAction();
        }
        const entries = {
            INSERT : act_insert();
            QUERY : act_query();
            CLEAR : act_clear();
            _ : .NoAction();
        }
        default_action = .NoAction();
        size = 4;
    }
    apply {
        tbl_bloom.apply();
    }
}

control Bf2BloomFilterWin(inout bf2_win_md_t win_md)  {
    Bf2BloomFilterRow() row_1;
    Bf2BloomFilterRow() row_2;
    Bf2BloomFilterRow() row_3;
    apply {
        row_1.apply(win_md.api, win_md.index_1, win_md.rw_1);
        row_2.apply(win_md.api, win_md.index_2, win_md.rw_2);
        row_3.apply(win_md.api, win_md.index_3, win_md.rw_3);
    }
}

control Bf2BloomFilter(in bf2_key_t ds_key,
                       in api_t api,
                       in bit<48> ingress_mac_tstamp,
                       inout bf2_value_t query_res)  {
    bf2_ds_md_t ds_md;
    CRCPolynomial<bit<32>>(32w79764919, true, false, false, 32w0, 32w4294967295) poly_idx_1;
    Hash<bit<32>>(HashAlgorithm_t.CUSTOM, poly_idx_1) hash_idx_1;
    action act_hash_index_1() {
        ds_md.hash_index_1 = hash_idx_1.get(ds_key)[17:0];
    }
    table tbl_hash_index_1 {
        actions = {
            act_hash_index_1();
        }
        default_action = act_hash_index_1();
        size = 1;
    }
    CRCPolynomial<bit<32>>(32w517762881, true, false, false, 32w0, 32w4294967295) poly_idx_2;
    Hash<bit<32>>(HashAlgorithm_t.CUSTOM, poly_idx_2) hash_idx_2;
    action act_hash_index_2() {
        ds_md.hash_index_2 = hash_idx_2.get(ds_key)[17:0];
    }
    table tbl_hash_index_2 {
        actions = {
            act_hash_index_2();
        }
        default_action = act_hash_index_2();
        size = 1;
    }
    CRCPolynomial<bit<32>>(32w2821953579, true, false, false, 32w0, 32w4294967295) poly_idx_3;
    Hash<bit<32>>(HashAlgorithm_t.CUSTOM, poly_idx_3) hash_idx_3;
    action act_hash_index_3() {
        ds_md.hash_index_3 = hash_idx_3.get(ds_key)[17:0];
    }
    table tbl_hash_index_3 {
        actions = {
            act_hash_index_3();
        }
        default_action = act_hash_index_3();
        size = 1;
    }
    Register<bit<32>, bit<1>>(32w1, 32w0) reg_clear_index;
    RegisterAction<bit<32>, bit<1>, bit<32>>(reg_clear_index) regact_clear_index = {
        void apply(inout bit<32> val, out bit<32> rv) {
            rv = val;
            val = (val + 32w1);
        }
    };
    action act_clear_index() {
        ds_md.clear_index_1 = regact_clear_index.execute(1w0)[17:0];
    }
    table tbl_clear_index {
        actions = {
            act_clear_index();
        }
        default_action = act_clear_index();
        size = 1;
    }
    Register<window_pair_t, bit<1>>(32w1, {16w0, 16w0}) reg_clear_window;
    RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_0 = {
        void apply(inout window_pair_t val, out window_t rv) {
            bool flip = (val.lo != 16w0);
            bool wrap = (val.hi == 16w28135);
            if (flip)
            {
                if (wrap)
                {
                    val.lo = 16w0;
                    val.hi = 16w0;
                }
                else
                {
                    val.lo = 16w0;
                    val.hi = (val.hi + 16w1);
                }
            }
            else
            {
                val.lo = val.lo;
                val.hi = val.hi;
            }
            rv = val.hi;
        }
    };
    RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_1 = {
        void apply(inout window_pair_t val, out window_t rv) {
            if ((val.lo != 16w1))
            {
                val.lo = 16w1;
            }
            rv = val.hi;
        }
    };
    action act_clear_window_signal_0() {
        ds_md.clear_window = regact_clear_window_signal_0.execute(1w0);
    }
    action act_clear_window_signal_1() {
        ds_md.clear_window = regact_clear_window_signal_1.execute(1w0);
    }
    table tbl_clear_window {
        key = {
            ingress_mac_tstamp : ternary;
        }
        actions = {
            act_clear_window_signal_0();
            act_clear_window_signal_1();
        }
        const entries = {
            48w0 &&& 48w2097152 : act_clear_window_signal_0();
            _ : act_clear_window_signal_1();
        }
        default_action = act_clear_window_signal_1();
        size = 2;
    }
    action act_set_clear_win_1(bit<8> api_1,
                               bit<8> api_2,
                               bit<8> api_3,
                               bit<8> api_4) {
        ds_md.win_1.index_1 = ds_md.clear_index_1;
        ds_md.win_1.index_2 = ds_md.clear_index_1;
        ds_md.win_1.index_3 = ds_md.clear_index_1;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
        ds_md.win_4.api = api_4;
    }
    action act_set_clear_win_2(bit<8> api_1,
                               bit<8> api_2,
                               bit<8> api_3,
                               bit<8> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_1 = ds_md.clear_index_1;
        ds_md.win_2.index_2 = ds_md.clear_index_1;
        ds_md.win_2.index_3 = ds_md.clear_index_1;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
        ds_md.win_4.api = api_4;
    }
    action act_set_clear_win_3(bit<8> api_1,
                               bit<8> api_2,
                               bit<8> api_3,
                               bit<8> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_1 = ds_md.clear_index_1;
        ds_md.win_3.index_2 = ds_md.clear_index_1;
        ds_md.win_3.index_3 = ds_md.clear_index_1;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
        ds_md.win_4.api = api_4;
    }
    action act_set_clear_win_4(bit<8> api_1,
                               bit<8> api_2,
                               bit<8> api_3,
                               bit<8> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_1 = ds_md.clear_index_1;
        ds_md.win_4.index_2 = ds_md.clear_index_1;
        ds_md.win_4.index_3 = ds_md.clear_index_1;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
        ds_md.win_4.api = api_4;
    }
    table tbl_set_win {
        key = {
            api : ternary;
            ds_md.clear_window : range;
        }
        actions = {
            act_set_clear_win_1();
            act_set_clear_win_2();
            act_set_clear_win_3();
            act_set_clear_win_4();
            .NoAction();
        }
        const entries = {
            (INSERT, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR,
                                                            NOOP,
                                                            NOOP,
                                                            INSERT);
            (INSERT, 16w7034 .. 16w14067) : act_set_clear_win_2(INSERT,
                                                                CLEAR,
                                                                NOOP,
                                                                NOOP);
            (INSERT, 16w14068 .. 16w21101) : act_set_clear_win_3(NOOP,
                                                                 INSERT,
                                                                 CLEAR,
                                                                 NOOP);
            (INSERT, 16w21102 .. 16w28135) : act_set_clear_win_4(NOOP,
                                                                 NOOP,
                                                                 INSERT,
                                                                 CLEAR);
            (QUERY, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR,
                                                           QUERY,
                                                           QUERY,
                                                           QUERY);
            (QUERY, 16w7034 .. 16w14067) : act_set_clear_win_2(QUERY,
                                                               CLEAR,
                                                               QUERY,
                                                               QUERY);
            (QUERY, 16w14068 .. 16w21101) : act_set_clear_win_3(QUERY,
                                                                QUERY,
                                                                CLEAR,
                                                                QUERY);
            (QUERY, 16w21102 .. 16w28135) : act_set_clear_win_4(QUERY,
                                                                QUERY,
                                                                QUERY,
                                                                CLEAR);
            (CLEAR, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR,
                                                           NOOP,
                                                           NOOP,
                                                           NOOP);
            (CLEAR, 16w7034 .. 16w14067) : act_set_clear_win_2(NOOP,
                                                               CLEAR,
                                                               NOOP,
                                                               NOOP);
            (CLEAR, 16w14068 .. 16w21101) : act_set_clear_win_3(NOOP,
                                                                NOOP,
                                                                CLEAR,
                                                                NOOP);
            (CLEAR, 16w21102 .. 16w28135) : act_set_clear_win_4(NOOP,
                                                                NOOP,
                                                                NOOP,
                                                                CLEAR);
            (_, _) : .NoAction();
        }
        default_action = .NoAction();
        size = 13;
    }
    Bf2BloomFilterWin() win_1;
    Bf2BloomFilterWin() win_2;
    Bf2BloomFilterWin() win_3;
    Bf2BloomFilterWin() win_4;
    action act_merge_wins() {
        query_res = 8w1;
    }
    action act_merge_default() {
        query_res = 8w0;
    }
    table tbl_merge_wins {
        key = {
            api : ternary;
            ds_md.win_1.rw_1 : ternary;
            ds_md.win_1.rw_2 : ternary;
            ds_md.win_1.rw_3 : ternary;
            ds_md.win_2.rw_1 : ternary;
            ds_md.win_2.rw_2 : ternary;
            ds_md.win_2.rw_3 : ternary;
            ds_md.win_3.rw_1 : ternary;
            ds_md.win_3.rw_2 : ternary;
            ds_md.win_3.rw_3 : ternary;
            ds_md.win_4.rw_1 : ternary;
            ds_md.win_4.rw_2 : ternary;
            ds_md.win_4.rw_3 : ternary;
        }
        actions = {
            act_merge_wins();
            act_merge_default();
            .NoAction();
        }
        const entries = {
            (QUERY, 8w1, 8w1, 8w1, _, _, _, _, _, _, _, _, _) : act_merge_wins();
            (QUERY, _, _, _, 8w1, 8w1, 8w1, _, _, _, _, _, _) : act_merge_wins();
            (QUERY, _, _, _, _, _, _, 8w1, 8w1, 8w1, _, _, _) : act_merge_wins();
            (QUERY, _, _, _, _, _, _, _, _, _, 8w1, 8w1, 8w1) : act_merge_wins();
            (QUERY, _, _, _, _, _, _, _, _, _, _, _, _) : act_merge_default();
            (_, _, _, _, _, _, _, _, _, _, _, _, _) : .NoAction();
        }
        default_action = .NoAction();
        size = 6;
    }
    apply {
        tbl_hash_index_1.apply();
        tbl_hash_index_2.apply();
        tbl_hash_index_3.apply();
        tbl_clear_index.apply();
        tbl_clear_window.apply();
        tbl_set_win.apply();
        win_1.apply(ds_md.win_1);
        win_2.apply(ds_md.win_2);
        win_3.apply(ds_md.win_3);
        win_4.apply(ds_md.win_4);
        tbl_merge_wins.apply();
    }
}

control SwitchIngress(inout header_t hdr,
                      inout metadata_t ig_md,
                      in ingress_intrinsic_metadata_t ig_intr_md,
                      in ingress_intrinsic_metadata_from_parser_t ig_intr_prsr_md,
                      inout ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md,
                      inout ingress_intrinsic_metadata_for_tm_t ig_intr_tm_md)
                      {
    action act_for_tbl_1_action_0() {
        ig_md.solicited = 1;
    }
    table tbl_for_stmt_1 {
        actions = {
            act_for_tbl_1_action_0();
        }
        default_action = act_for_tbl_1_action_0();
        size = 1;
    }
    action bf2_act_set_insert_key(bit<8> api) {
        ig_md.bf2_api = api;
        ig_md.bf2_key = (hdr.ipv4.dst_addr ++ hdr.ipv4.src_addr);
    }
    action bf2_act_set_query_key(bit<8> api) {
        ig_md.bf2_api = api;
        ig_md.bf2_key = (hdr.ipv4.src_addr ++ hdr.ipv4.dst_addr);
    }
    action bf2_act_set_clear_key() {
        ig_md.bf2_api = CLEAR;
        ig_md.bf2_key = 0;
    }
    table bf2_tbl_set_key {
        key = {
            ig_intr_md.ingress_port : exact;
            hdr.ipv4.src_addr : ternary;
        }
        actions = {
            bf2_act_set_insert_key();
            bf2_act_set_query_key();
            bf2_act_set_clear_key();
        }
        const entries = {
            (GENERATOR_PORT, _) : bf2_act_set_clear_key();
            (_, 2154823680 &&& 4294901760) : bf2_act_set_insert_key(INSERT);
            (_, _) : bf2_act_set_query_key(QUERY);
        }
        default_action = bf2_act_set_clear_key();
        size = 2;
    }
    Bf2BloomFilter() bf2_ds;
    action act_for_tbl_3_action_0() {
        ig_intr_dprsr_md.drop_ctl = 1;
    }
    action act_for_tbl_3_action_1() {
        ig_intr_dprsr_md.drop_ctl = 0;
    }
    table tbl_for_stmt_3 {
        key = {
            ig_intr_md.ingress_port : exact;
            ig_md.solicited : ternary;
        }
        actions = {
            act_for_tbl_3_action_0();
            act_for_tbl_3_action_1();
        }
        const entries = {
            (GENERATOR_PORT, _) : act_for_tbl_3_action_0();
            (_, 0) : act_for_tbl_3_action_0();
            (_, _) : act_for_tbl_3_action_1();
        }
        default_action = act_for_tbl_3_action_1();
        size = 2;
    }
    apply {
        tbl_for_stmt_1.apply();
        bf2_tbl_set_key.apply();
        bf2_ds.apply(ig_md.bf2_key,
                     ig_md.bf2_api,
                     ig_intr_md.ingress_mac_tstamp,
                     ig_md.solicited);
        tbl_for_stmt_3.apply();
    }
}

control SwitchIngressDeparser(packet_out pkt,
                              inout header_t hdr,
                              in metadata_t ig_md,
                              in ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md)
                              {
    apply {
        pkt.emit(hdr);
    }
}

parser SwitchEgressParser(packet_in pkt,
                          out header_t hdr,
                          out metadata_t eg_md,
                          out egress_intrinsic_metadata_t eg_intr_md)  {
    TofinoEgressParser() tofino_parser;
    EtherIPTCPUDPParser() layer4_parser;
    state start {
        tofino_parser.apply(pkt, eg_intr_md);
        layer4_parser.apply(pkt, hdr);
        transition accept;
    }
}

control SwitchEgress(inout header_t hdr,
                     inout metadata_t eg_md,
                     in egress_intrinsic_metadata_t eg_intr_md,
                     in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr,
                     inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
                     inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport)
                     {
    apply { }
}

control SwitchEgressDeparser(packet_out pkt,
                             inout header_t hdr,
                             in metadata_t eg_md,
                             in egress_intrinsic_metadata_for_deparser_t eg_intr_dprsr_md)
                             {
    apply {
        pkt.emit(hdr);
    }
}

Pipeline(SwitchIngressParser(), SwitchIngress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch(pipe) main;

