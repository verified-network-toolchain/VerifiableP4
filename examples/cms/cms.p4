#define NOOP 0
#define CLEAR 1
#define INSERT 2
#define QUERY 3
#define INSQUERY 4

#include "core.p4"
#include "tna.p4"
#include "common/headers.p4"
#include "common/util.p4"

@pragma pa_auto_init_metadata

typedef bit<32> api_t;

typedef bit<8> window_t;

typedef bit<15> cm2_index_t;

typedef bit<32> cm2_value_t;

typedef bit<64> cm2_key_t;

struct cm2_win_md_t {
    api_t api_call;
    cm2_index_t index_1;
    cm2_index_t index_2;
    cm2_index_t index_3;
    cm2_index_t index_4;
    cm2_value_t rw_1;
    cm2_value_t rw_2;
    cm2_value_t rw_3;
    cm2_value_t rw_4;
}

struct cm2_ds_md_t {
    window_t clear_window;
    cm2_index_t clear_index_1;
    cm2_index_t clear_index_2;
    cm2_index_t hash_index_1;
    cm2_index_t hash_index_2;
    cm2_index_t hash_index_3;
    cm2_index_t hash_index_4;
    cm2_win_md_t win_1;
    cm2_win_md_t win_2;
    cm2_win_md_t win_3;
    cm2_win_md_t win_4;
}

struct metadata_t {
    cm2_key_t cm2_key;
    api_t cm2_api_call;
    bit<32> solicitated;
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
            value = (value |+| 1);
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
    action act_merge_rows_1() {
        win_md.rw_1 = min(win_md.rw_1, win_md.rw_3);
        win_md.rw_2 = min(win_md.rw_2, win_md.rw_4);
    }
    action act_merge_rows_2() {
        win_md.rw_1 = min(win_md.rw_1, win_md.rw_2);
    }
    table tbl_merge_rows_1 {
        key = { }
        actions = {
            act_merge_rows_1();
        }
        default_action = act_merge_rows_1();
        size = 1;
    }
    table tbl_merge_rows_2 {
        key = { }
        actions = {
            act_merge_rows_2();
        }
        default_action = act_merge_rows_2();
        size = 1;
    }
    apply {
        row_1.apply(win_md.api_call, win_md.index_1, win_md.rw_1);
        row_2.apply(win_md.api_call, win_md.index_2, win_md.rw_2);
        row_3.apply(win_md.api_call, win_md.index_3, win_md.rw_3);
        row_4.apply(win_md.api_call, win_md.index_4, win_md.rw_4);
        tbl_merge_rows_1.apply();
        tbl_merge_rows_2.apply();
    }
}

control Cm2CountMinSketch(in cm2_key_t ds_key,
                          in api_t api_call,
                          in bit<48> ingress_mac_tstamp,
                          out cm2_value_t query_res)  {
    cm2_ds_md_t ds_md;
    CRCPolynomial<bit<16>>(16w15717, false, false, false, 16w0, 16w0) crc_poly_1;
    Hash<bit<16>>(HashAlgorithm_t.CRC16, crc_poly_1) crc_hash_1;
    action act_hash_index_1() {
        ds_md.hash_index_1 = crc_hash_1.get(ds_key)[14:0];
    }
    table tbl_hash_index_1 {
        key = { }
        actions = {
            act_hash_index_1();
        }
        default_action = act_hash_index_1();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w15717, false, false, false, 16w0, 16w0) crc_poly_2;
    Hash<bit<16>>(HashAlgorithm_t.CRC16, crc_poly_2) crc_hash_2;
    action act_hash_index_2() {
        ds_md.hash_index_2 = crc_hash_2.get(ds_key)[14:0];
    }
    table tbl_hash_index_2 {
        key = { }
        actions = {
            act_hash_index_2();
        }
        default_action = act_hash_index_2();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w15717, false, false, false, 16w0, 16w0) crc_poly_3;
    Hash<bit<16>>(HashAlgorithm_t.CRC16, crc_poly_3) crc_hash_3;
    action act_hash_index_3() {
        ds_md.hash_index_3 = crc_hash_3.get(ds_key)[14:0];
    }
    table tbl_hash_index_3 {
        key = { }
        actions = {
            act_hash_index_3();
        }
        default_action = act_hash_index_3();
        size = 1;
    }
    CRCPolynomial<bit<16>>(16w15717, false, false, false, 16w0, 16w0) crc_poly_4;
    Hash<bit<16>>(HashAlgorithm_t.CRC16, crc_poly_4) crc_hash_4;
    action act_hash_index_4() {
        ds_md.hash_index_4 = crc_hash_4.get(ds_key)[14:0];
    }
    table tbl_hash_index_4 {
        key = { }
        actions = {
            act_hash_index_4();
        }
        default_action = act_hash_index_4();
        size = 1;
    }
    Register<bit<16>, bit<1>>(32w1, 16w0) reg_clear_index;
    RegisterAction<bit<16>, bit<1>, bit<16>>(reg_clear_index) regact_clear_index = {
        void apply(inout bit<16> val, out bit<16> rv) {
            rv = val;
            val = (val + 16w1);
        }
    };
    action act_clear_index() {
        ds_md.clear_index_1 = regact_clear_index.execute(1w0)[14:0];
    }
    table tbl_clear_index {
        key = { }
        actions = {
            act_clear_index();
        }
        default_action = act_clear_index();
        size = 1;
    }
    Register<window_pair_t, bit<1>>(32w1, {8w0, 8w0}) reg_clear_window;
    RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_0 = {
        void apply(inout window_pair_t val, out window_t rv) {
            if ((val.lo != 8w0))
            {
                val.hi = (val.hi + 8w1);
                val.lo = 8w0;
            }
            rv = val.hi;
        }
    };
    RegisterAction<window_pair_t, bit<1>, window_t>(reg_clear_window) regact_clear_window_signal_1 = {
        void apply(inout window_pair_t val, out window_t rv) {
            if ((val.hi == 8w224))
            {
                val.hi = 8w0;
            }
            if ((val.lo != 8w1))
            {
                val.lo = 8w1;
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
            ingress_mac_tstamp[28:28] : ternary;
        }
        actions = {
            act_clear_window_signal_0();
            act_clear_window_signal_1();
        }
        const entries = {
            1w0 : act_clear_window_signal_0();
            _ : act_clear_window_signal_1();
        }
        default_action = act_clear_window_signal_1();
        size = 2;
    }
    Hash<bit<16>>(HashAlgorithm_t.IDENTITY) copy_clear_2;
    action act_copy_clear_2() {
        ds_md.clear_index_2 = copy_clear_2.get(ds_md.clear_index_1)[14:0];
    }
    table tbl_copy_clear_2 {
        key = { }
        actions = {
            act_copy_clear_2();
        }
        default_action = act_copy_clear_2();
        size = 1;
    }
    action act_set_clear_win_1(bit<32> api_1,
                               bit<32> api_2,
                               bit<32> api_3,
                               bit<32> api_4) {
        ds_md.win_1.index_1 = ds_md.clear_index_1;
        ds_md.win_1.index_2 = ds_md.clear_index_1;
        ds_md.win_1.index_3 = ds_md.clear_index_1;
        ds_md.win_1.index_4 = ds_md.clear_index_2;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_4 = ds_md.hash_index_4;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_4 = ds_md.hash_index_4;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_4 = ds_md.hash_index_4;
        ds_md.win_1.api_call = api_1;
        ds_md.win_2.api_call = api_2;
        ds_md.win_3.api_call = api_3;
        ds_md.win_4.api_call = api_4;
    }
    action act_set_clear_win_2(bit<32> api_1,
                               bit<32> api_2,
                               bit<32> api_3,
                               bit<32> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_1.index_4 = ds_md.hash_index_4;
        ds_md.win_2.index_1 = ds_md.clear_index_1;
        ds_md.win_2.index_2 = ds_md.clear_index_1;
        ds_md.win_2.index_3 = ds_md.clear_index_1;
        ds_md.win_2.index_4 = ds_md.clear_index_2;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_4 = ds_md.hash_index_4;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_4 = ds_md.hash_index_4;
        ds_md.win_1.api_call = api_1;
        ds_md.win_2.api_call = api_2;
        ds_md.win_3.api_call = api_3;
        ds_md.win_4.api_call = api_4;
    }
    action act_set_clear_win_3(bit<32> api_1,
                               bit<32> api_2,
                               bit<32> api_3,
                               bit<32> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_1.index_4 = ds_md.hash_index_4;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_4 = ds_md.hash_index_4;
        ds_md.win_3.index_1 = ds_md.clear_index_1;
        ds_md.win_3.index_2 = ds_md.clear_index_1;
        ds_md.win_3.index_3 = ds_md.clear_index_1;
        ds_md.win_3.index_4 = ds_md.clear_index_2;
        ds_md.win_4.index_1 = ds_md.hash_index_1;
        ds_md.win_4.index_2 = ds_md.hash_index_2;
        ds_md.win_4.index_3 = ds_md.hash_index_3;
        ds_md.win_4.index_4 = ds_md.hash_index_4;
        ds_md.win_1.api_call = api_1;
        ds_md.win_2.api_call = api_2;
        ds_md.win_3.api_call = api_3;
        ds_md.win_4.api_call = api_4;
    }
    action act_set_clear_win_4(bit<32> api_1,
                               bit<32> api_2,
                               bit<32> api_3,
                               bit<32> api_4) {
        ds_md.win_1.index_1 = ds_md.hash_index_1;
        ds_md.win_1.index_2 = ds_md.hash_index_2;
        ds_md.win_1.index_3 = ds_md.hash_index_3;
        ds_md.win_1.index_4 = ds_md.hash_index_4;
        ds_md.win_2.index_1 = ds_md.hash_index_1;
        ds_md.win_2.index_2 = ds_md.hash_index_2;
        ds_md.win_2.index_3 = ds_md.hash_index_3;
        ds_md.win_2.index_4 = ds_md.hash_index_4;
        ds_md.win_3.index_1 = ds_md.hash_index_1;
        ds_md.win_3.index_2 = ds_md.hash_index_2;
        ds_md.win_3.index_3 = ds_md.hash_index_3;
        ds_md.win_3.index_4 = ds_md.hash_index_4;
        ds_md.win_4.index_1 = ds_md.clear_index_1;
        ds_md.win_4.index_2 = ds_md.clear_index_1;
        ds_md.win_4.index_3 = ds_md.clear_index_1;
        ds_md.win_4.index_4 = ds_md.clear_index_2;
        ds_md.win_1.api_call = api_1;
        ds_md.win_2.api_call = api_2;
        ds_md.win_3.api_call = api_3;
        ds_md.win_4.api_call = api_4;
    }
    table tbl_set_win {
        key = {
            api_call : ternary;
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
            (INSERT, 8w0 .. 8w55) : act_set_clear_win_1(CLEAR,
                                                        NOOP,
                                                        NOOP,
                                                        INSERT);
            (INSERT, 8w56 .. 8w111) : act_set_clear_win_2(INSERT,
                                                          CLEAR,
                                                          NOOP,
                                                          NOOP);
            (INSERT, 8w112 .. 8w167) : act_set_clear_win_3(NOOP,
                                                           INSERT,
                                                           CLEAR,
                                                           NOOP);
            (INSERT, 8w168 .. 8w223) : act_set_clear_win_4(NOOP,
                                                           NOOP,
                                                           INSERT,
                                                           CLEAR);
            (INSERT, 8w224) : act_set_clear_win_1(CLEAR, NOOP, NOOP, INSERT);
            (QUERY, 8w0 .. 8w55) : act_set_clear_win_1(CLEAR,
                                                       QUERY,
                                                       QUERY,
                                                       QUERY);
            (QUERY, 8w56 .. 8w111) : act_set_clear_win_2(QUERY,
                                                         CLEAR,
                                                         QUERY,
                                                         QUERY);
            (QUERY, 8w112 .. 8w167) : act_set_clear_win_3(QUERY,
                                                          QUERY,
                                                          CLEAR,
                                                          QUERY);
            (QUERY, 8w168 .. 8w223) : act_set_clear_win_4(QUERY,
                                                          QUERY,
                                                          QUERY,
                                                          CLEAR);
            (QUERY, 8w224) : act_set_clear_win_1(CLEAR, QUERY, QUERY, QUERY);
            (_, _) : .NoAction();
        }
        default_action = .NoAction();
        size = 11;
    }
    Cm2CountMinSketchWin() win_1;
    Cm2CountMinSketchWin() win_2;
    Cm2CountMinSketchWin() win_3;
    Cm2CountMinSketchWin() win_4;
    action act_merge_wins_1() {
        ds_md.win_1.rw_1 = (ds_md.win_1.rw_1 |+| ds_md.win_3.rw_1);
        ds_md.win_2.rw_1 = (ds_md.win_2.rw_1 |+| ds_md.win_4.rw_1);
    }
    table tbl_merge_wins_1 {
        key = { }
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
            api_call : ternary;
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
        tbl_clear_index.apply();
        tbl_clear_window.apply();
        tbl_copy_clear_2.apply();
        tbl_set_win.apply();
        win_1.apply(ds_md.win_1);
        win_2.apply(ds_md.win_2);
        win_3.apply(ds_md.win_3);
        win_4.apply(ds_md.win_4);
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
        ig_md.solicitated = 0;
    }
    table tbl_for_stmt_1 {
        key = { }
        actions = {
            act_for_tbl_1_action_0();
        }
        default_action = act_for_tbl_1_action_0();
        size = 1;
    }
    action cm2_act_set_insert_key(bit<32> api) {
        ig_md.cm2_api_call = api;
        ig_md.cm2_key = (hdr.ipv4.dst_addr ++ hdr.ipv4.src_addr);
    }
    action cm2_act_set_query_key(bit<32> api) {
        ig_md.cm2_api_call = api;
        ig_md.cm2_key = (hdr.ipv4.src_addr ++ hdr.ipv4.dst_addr);
    }
    table cm2_tbl_set_key {
        key = {
            ig_intr_md.ingress_port : ternary;
        }
        actions = {
            cm2_act_set_insert_key();
            cm2_act_set_query_key();
        }
        const entries = {
            0 : cm2_act_set_insert_key(INSERT);
            _ : cm2_act_set_query_key(QUERY);
        }
        default_action = cm2_act_set_query_key(QUERY);
        size = 2;
    }
    Cm2CountMinSketch() cm2_ds;
    action act_for_tbl_3_action_0() {
        ig_intr_dprsr_md.drop_ctl = 1;
    }
    table tbl_for_stmt_3 {
        key = {
            ig_md.solicitated : ternary;
        }
        actions = {
            act_for_tbl_3_action_0();
            .NoAction();
        }
        const entries = {
            0 : act_for_tbl_3_action_0();
            _ : .NoAction();
        }
        default_action = .NoAction();
        size = 2;
    }
    apply {
        tbl_for_stmt_1.apply();
        cm2_tbl_set_key.apply();
        cm2_ds.apply(ig_md.cm2_key,
                     ig_md.cm2_api_call,
                     ig_intr_md.ingress_mac_tstamp,
                     ig_md.solicitated);
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

