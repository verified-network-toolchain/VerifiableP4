#define NOOP 0
#define CLEAR 1
#define INSERT 2
#define QUERY 3
#define INSQUERY 4
#define UPDATE 5
#define UPDQUERY 6
#define DONTCARE 0
#define QDEFAULT 0

#include <core.p4>
#include <tna.p4>
#include "common/headers.p4"
#include "common/util.p4"


typedef bit<8> api_t;

typedef bit<16> window_t;

typedef bit<4> pred_t;

typedef bit<15> cm2_index_t;

typedef bit<32> cm2_value_t;

typedef bit<32> cm2_key_t;

struct cm2_win_md_t {
    api_t api;
    cm2_index_t index_1;
    cm2_index_t index_2;
    cm2_index_t index_3;
    cm2_index_t index_4;
    cm2_index_t index_5;
    cm2_value_t rw_1;
    cm2_value_t rw_2;
    cm2_value_t rw_3;
    cm2_value_t rw_4;
    cm2_value_t rw_5;
}

struct cm2_ds_md_t {
    window_t clear_window;
    cm2_index_t clear_index_1;
    cm2_index_t hash_index_1;
    cm2_index_t hash_index_2;
    cm2_index_t hash_index_3;
    cm2_index_t hash_index_4;
    cm2_index_t hash_index_5;
    cm2_win_md_t win_1;
    cm2_win_md_t win_2;
    cm2_win_md_t win_3;
}

struct metadata_t {
    cm2_key_t cm2_key;
    api_t cm2_api;
    bit<32> num_pkt;
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
        layer4_parser.apply(pkt, hdr);
        transition accept;
    }
}

control Cm2CountMinSketchRow(in api_t api,
                             in cm2_index_t index,
                             out cm2_value_t rw)  {
    Register<cm2_value_t, cm2_index_t>(32w32768, 32w0) reg_row;
    RegisterAction<cm2_value_t, cm2_index_t, cm2_value_t>(reg_row) regact_insert = {
        void apply(inout cm2_value_t value, out cm2_value_t rv) {
            value = (value |+| 32w1);
            rv = value;
        }
    };
    action act_insert() {
        rw = regact_insert.execute(index);
    }
    RegisterAction<cm2_value_t, cm2_index_t, cm2_value_t>(reg_row) regact_query = {
        void apply(inout cm2_value_t value, out cm2_value_t rv) {
            rv = value;
        }
    };
    action act_query() {
        rw = regact_query.execute(index);
    }
    RegisterAction<cm2_value_t, cm2_index_t, cm2_value_t>(reg_row) regact_clear = {
        void apply(inout cm2_value_t value, out cm2_value_t rv) {
            value = 32w0;
            rv = 32w0;
        }
    };
    action act_clear() {
        rw = regact_clear.execute(index);
    }
    table tbl_cms {
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
        tbl_cms.apply();
    }
}

control Cm2CountMinSketchWin(inout cm2_win_md_t win_md)  {
    Cm2CountMinSketchRow() row_1;
    Cm2CountMinSketchRow() row_2;
    Cm2CountMinSketchRow() row_3;
    Cm2CountMinSketchRow() row_4;
    Cm2CountMinSketchRow() row_5;
    action act_merge_rows_1() {
        win_md.rw_1 = (win_md.rw_1 |+| win_md.rw_4);
        win_md.rw_2 = (win_md.rw_2 |+| win_md.rw_5);
    }
    action act_merge_rows_2() {
        win_md.rw_1 = (win_md.rw_1 |+| win_md.rw_3);
    }
    action act_merge_rows_3() {
        win_md.rw_1 = (win_md.rw_1 |+| win_md.rw_2);
    }
    table tbl_merge_rows_1 {
        actions = {
            act_merge_rows_1();
        }
        default_action = act_merge_rows_1();
        size = 1;
    }
    table tbl_merge_rows_2 {
        actions = {
            act_merge_rows_2();
        }
        default_action = act_merge_rows_2();
        size = 1;
    }
    table tbl_merge_rows_3 {
        actions = {
            act_merge_rows_3();
        }
        default_action = act_merge_rows_3();
        size = 1;
    }
    apply {
        row_1.apply(win_md.api, win_md.index_1, win_md.rw_1);
        row_2.apply(win_md.api, win_md.index_2, win_md.rw_2);
        row_3.apply(win_md.api, win_md.index_3, win_md.rw_3);
        row_4.apply(win_md.api, win_md.index_4, win_md.rw_4);
        row_5.apply(win_md.api, win_md.index_5, win_md.rw_5);
        tbl_merge_rows_1.apply();
        tbl_merge_rows_2.apply();
        tbl_merge_rows_3.apply();
    }
}

control Cm2CountMinSketch(in cm2_key_t ds_key,
                          in api_t api,
                          in bit<48> ingress_mac_tstamp,
                          inout cm2_value_t query_res)  {
    cm2_ds_md_t ds_md;
    CRCPolynomial<bit<16>>(16w32773, true, false, false, 16w0, 16w0) poly_idx_1;
    Hash<bit<16>>(HashAlgorithm_t.CUSTOM, poly_idx_1) hash_idx_1;
    action act_hash_index_1() {
        ds_md.hash_index_1 = hash_idx_1.get(ds_key)[14:0];
    }
    table tbl_hash_index_1 {
        actions = {
            act_hash_index_1();
        }
        default_action = act_hash_index_1();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w4129, false, false, false, 16w65535, 16w0) poly_idx_2;
    Hash<bit<16>>(HashAlgorithm_t.CUSTOM, poly_idx_2) hash_idx_2;
    action act_hash_index_2() {
        ds_md.hash_index_2 = hash_idx_2.get(ds_key)[14:0];
    }
    table tbl_hash_index_2 {
        actions = {
            act_hash_index_2();
        }
        default_action = act_hash_index_2();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w1417, false, false, false, 16w1, 16w1) poly_idx_3;
    Hash<bit<16>>(HashAlgorithm_t.CUSTOM, poly_idx_3) hash_idx_3;
    action act_hash_index_3() {
        ds_md.hash_index_3 = hash_idx_3.get(ds_key)[14:0];
    }
    table tbl_hash_index_3 {
        actions = {
            act_hash_index_3();
        }
        default_action = act_hash_index_3();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w15717, true, false, false, 16w0, 16w65535) poly_idx_4;
    Hash<bit<16>>(HashAlgorithm_t.CUSTOM, poly_idx_4) hash_idx_4;
    action act_hash_index_4() {
        ds_md.hash_index_4 = hash_idx_4.get(ds_key)[14:0];
    }
    table tbl_hash_index_4 {
        actions = {
            act_hash_index_4();
        }
        default_action = act_hash_index_4();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w35767, false, false, false, 16w0, 16w0) poly_idx_5;
    Hash<bit<16>>(HashAlgorithm_t.CUSTOM, poly_idx_5) hash_idx_5;
    action act_hash_index_5() {
        ds_md.hash_index_5 = hash_idx_5.get(ds_key)[14:0];
    }
    table tbl_hash_index_5 {
        actions = {
            act_hash_index_5();
        }
        default_action = act_hash_index_5();
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
        ds_md.clear_index_1 = regact_clear_index.execute(1w0)[14:0];
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
            bool wrap = (val.hi == 16w21101);
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
            48w0 &&& 48w4194304 : act_clear_window_signal_0();
            _ : act_clear_window_signal_1();
        }
        default_action = act_clear_window_signal_1();
        size = 2;
    }
    action act_set_clear_win_1(bit<8> api_1, bit<8> api_2, bit<8> api_3) {
        ds_md.win_1.index_1 = ds_md.clear_index_1;
        ds_md.win_1.index_2 = ds_md.clear_index_1;
        ds_md.win_1.index_3 = ds_md.clear_index_1;
        ds_md.win_1.index_4 = ds_md.clear_index_1;
        ds_md.win_1.index_5 = ds_md.clear_index_1;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_4 = ds_md.hash_index_4;
        ds_md.win_2.index_5 = ds_md.hash_index_5;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_4 = ds_md.hash_index_4;
        ds_md.win_3.index_5 = ds_md.hash_index_5;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
    }
    action act_set_clear_win_2(bit<8> api_1, bit<8> api_2, bit<8> api_3) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_1.index_4 = ds_md.hash_index_4;
        ds_md.win_1.index_5 = ds_md.hash_index_5;
        ds_md.win_2.index_1 = ds_md.clear_index_1;
        ds_md.win_2.index_2 = ds_md.clear_index_1;
        ds_md.win_2.index_3 = ds_md.clear_index_1;
        ds_md.win_2.index_4 = ds_md.clear_index_1;
        ds_md.win_2.index_5 = ds_md.clear_index_1;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_4 = ds_md.hash_index_4;
        ds_md.win_3.index_5 = ds_md.hash_index_5;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
    }
    action act_set_clear_win_3(bit<8> api_1, bit<8> api_2, bit<8> api_3) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_1.index_4 = ds_md.hash_index_4;
        ds_md.win_1.index_5 = ds_md.hash_index_5;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_4 = ds_md.hash_index_4;
        ds_md.win_2.index_5 = ds_md.hash_index_5;
        ds_md.win_3.index_1 = ds_md.clear_index_1;
        ds_md.win_3.index_2 = ds_md.clear_index_1;
        ds_md.win_3.index_3 = ds_md.clear_index_1;
        ds_md.win_3.index_4 = ds_md.clear_index_1;
        ds_md.win_3.index_5 = ds_md.clear_index_1;
        ds_md.win_1.api = api_1;
        ds_md.win_2.api = api_2;
        ds_md.win_3.api = api_3;
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
            .NoAction();
        }
        const entries = {
            (INSERT, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR,
                                                            NOOP,
                                                            INSERT);
            (INSERT, 16w7034 .. 16w14067) : act_set_clear_win_2(INSERT,
                                                                CLEAR,
                                                                NOOP);
            (INSERT, 16w14068 .. 16w21101) : act_set_clear_win_3(NOOP,
                                                                 INSERT,
                                                                 CLEAR);
            (QUERY, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR,
                                                           QUERY,
                                                           QUERY);
            (QUERY, 16w7034 .. 16w14067) : act_set_clear_win_2(QUERY,
                                                               CLEAR,
                                                               QUERY);
            (QUERY, 16w14068 .. 16w21101) : act_set_clear_win_3(QUERY,
                                                                QUERY,
                                                                CLEAR);
            (CLEAR, 16w0 .. 16w7033) : act_set_clear_win_1(CLEAR, NOOP, NOOP);
            (CLEAR, 16w7034 .. 16w14067) : act_set_clear_win_2(NOOP,
                                                               CLEAR,
                                                               NOOP);
            (CLEAR, 16w14068 .. 16w21101) : act_set_clear_win_3(NOOP,
                                                                NOOP,
                                                                CLEAR);
            (_, _) : .NoAction();
        }
        default_action = .NoAction();
        size = 10;
    }
    Cm2CountMinSketchWin() win_1;
    Cm2CountMinSketchWin() win_2;
    Cm2CountMinSketchWin() win_3;
    action act_merge_wins_1() {
        ds_md.win_1.rw_1 = (ds_md.win_1.rw_1 |+| ds_md.win_3.rw_1);
    }
    table tbl_merge_wins_1 {
        actions = {
            act_merge_wins_1();
        }
        default_action = act_merge_wins_1();
        size = 1;
    }
    action act_merge_wins_final() {
        query_res = (ds_md.win_1.rw_1 |+| ds_md.win_2.rw_1);
    }
    table tbl_merge_wins_final {
        key = {
            api : ternary;
        }
        actions = {
            act_merge_wins_final();
            .NoAction();
        }
        const entries = {
            QUERY : act_merge_wins_final();
            _ : .NoAction();
        }
        default_action = .NoAction();
        size = 2;
    }
    apply {
        tbl_hash_index_1.apply();
        tbl_hash_index_2.apply();
        tbl_hash_index_3.apply();
        tbl_hash_index_4.apply();
        tbl_hash_index_5.apply();
        tbl_clear_index.apply();
        tbl_clear_window.apply();
        tbl_set_win.apply();
        win_1.apply(ds_md.win_1);
        win_2.apply(ds_md.win_2);
        win_3.apply(ds_md.win_3);
        tbl_merge_wins_1.apply();
        tbl_merge_wins_final.apply();
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
        ig_md.num_pkt = 0;
    }
    table tbl_for_stmt_1 {
        actions = {
            act_for_tbl_1_action_0();
        }
        default_action = act_for_tbl_1_action_0();
        size = 1;
    }
    action cm2_act_set_insert_key(bit<8> api) {
        ig_md.cm2_api = api;
    }
    action cm2_act_set_clear_key() {
        ig_md.cm2_api = CLEAR;
    }
    table cm2_tbl_set_key {
        key = {
            ig_intr_md.ingress_port : ternary;
        }
        actions = {
            cm2_act_set_insert_key();
            cm2_act_set_clear_key();
        }
        const entries = {
            0 : cm2_act_set_insert_key(INSERT);
            _ : cm2_act_set_insert_key(QUERY);
        }
        default_action = cm2_act_set_insert_key(QUERY);
        size = 2;
    }
    Cm2CountMinSketch() cm2_ds;
    action act_for_tbl_3_action_0() {
        ig_intr_dprsr_md.drop_ctl = 0;
    }
    action act_for_tbl_3_action_1() {
        ig_intr_dprsr_md.drop_ctl = 1;
    }
    table tbl_for_stmt_3 {
        key = {
            ig_md.num_pkt : range;
        }
        actions = {
            act_for_tbl_3_action_0();
            act_for_tbl_3_action_1();
        }
        const entries = {
            0 .. 1000 : act_for_tbl_3_action_0();
            _ : act_for_tbl_3_action_1();
        }
        default_action = act_for_tbl_3_action_1();
        size = 2;
    }
    apply {
        tbl_for_stmt_1.apply();
        cm2_tbl_set_key.apply();
        cm2_ds.apply(hdr.ipv4.dst_addr,
                     ig_md.cm2_api,
                     ig_intr_md.ingress_mac_tstamp,
                     ig_md.num_pkt);
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

