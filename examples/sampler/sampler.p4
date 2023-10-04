// P4 program of the multicast sampler

#include <core.p4>
#include <tna.p4>
#include "common/headers.p4"
#include "common/util.p4"

#define COLLECTOR_MULTICAST_GROUP 1
#define COLLECTOR_MAC 2
#define MY_MAC 1
#define SAMPLE_ETYPE 0x1234
#define OUT_PORT 128

header bridge_t {
    bit<8> contains_sample;
}
// Information to collect in the digest
header sample_t {
  bit<48> dmac;
  bit<48> smac;
  bit<16> etype;
  bit<32> srcip;
  bit<32> dstip;
  bit<32> num_pkts;
}
struct header_sample_t {
    bridge_t bridge;
    sample_t sample;
    ethernet_h ethernet;
    ipv4_h ipv4;
    tcp_h tcp;
    udp_h udp;
}
struct metadata_t {
    bit<32> num_pkts;
}

parser SwitchIngressParser(packet_in pkt,
                           out header_sample_t hdr,
                           out metadata_t ig_md,
                           out ingress_intrinsic_metadata_t ig_intr_md)  {
    TofinoIngressParser() tofino_parser;
    state start {
        tofino_parser.apply(pkt, ig_intr_md);
        hdr.bridge.setValid();
        hdr.bridge.contains_sample = 0;
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

control SwitchIngress(inout header_sample_t hdr,
                      inout metadata_t ig_md,
                      in ingress_intrinsic_metadata_t ig_intr_md,
                      in ingress_intrinsic_metadata_from_parser_t ig_intr_prsr_md,
                      inout ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md,
                      inout ingress_intrinsic_metadata_for_tm_t ig_intr_tm_md)
                      {
    action act_set_egress_port() {
        ig_intr_tm_md.ucast_egress_port = OUT_PORT;
    }
    Register<bit<32>, bit<1>>(32w1, 32w0) reg_count;
    RegisterAction<bit<32>, bit<1>, bit<32>>(reg_count) regact_count = {
        void apply(inout bit<32> value, out bit<32> rv) {
            value = (value + 32w1);
            rv = value;
        }
    };
    action act_count() {
        ig_md.num_pkts = regact_count.execute(0);
    }

    action act_sample() {
        hdr.bridge.contains_sample = 1;

        hdr.sample.setValid();
        hdr.sample.dmac = COLLECTOR_MAC;
        hdr.sample.smac = MY_MAC;
        hdr.sample.etype = SAMPLE_ETYPE;
        hdr.sample.srcip = hdr.ipv4.src_addr;
        hdr.sample.dstip = hdr.ipv4.dst_addr;
        hdr.sample.num_pkts = ig_md.num_pkts;

        ig_intr_tm_md.mcast_grp_a = COLLECTOR_MULTICAST_GROUP;
    }
    table tbl_sample {
        key = { ig_md.num_pkts: ternary; }
        actions = {
            act_sample;
            NoAction;
        }
        const entries = {
            32w0x00000001 &&& 32w0x000003FF : act_sample();
            _ : NoAction();
        }

        const default_action = NoAction;
        size = 2;
    }

    apply {
        act_set_egress_port();
        act_count();
        tbl_sample.apply();
    }
}

control SwitchIngressDeparser(packet_out pkt,
                              inout header_sample_t hdr,
                              in metadata_t ig_md,
                              in ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md)
                              {
    apply {
        pkt.emit(hdr);
    }
}

parser SwitchEgressParser(packet_in pkt,
                          out header_sample_t hdr,
                          out metadata_t eg_md,
                          out egress_intrinsic_metadata_t eg_intr_md)  {
    TofinoEgressParser() tofino_parser;
    state start {
        tofino_parser.apply(pkt, eg_intr_md);
        pkt.extract(hdr.bridge);
        transition select(hdr.bridge.contains_sample) {
            1 : parse_sample;
            _ : parse_ethernet;
        }
    }
    state parse_sample {
        pkt.extract(hdr.sample);
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

control SwitchEgress(inout header_sample_t hdr,
                     inout metadata_t eg_md,
                     in egress_intrinsic_metadata_t eg_intr_md,
                     in egress_intrinsic_metadata_from_parser_t eg_intr_from_prsr,
                     inout egress_intrinsic_metadata_for_deparser_t eg_intr_md_for_dprsr,
                     inout egress_intrinsic_metadata_for_output_port_t eg_intr_md_for_oport)
                     {
    action act_delete_sample_hdrs() {
        hdr.bridge.setInvalid();
        hdr.sample.setInvalid();
    }
    action act_delete_packet_hdrs() {
        hdr.bridge.setInvalid();
        hdr.ethernet.setInvalid();
        hdr.ipv4.setInvalid();
    }
    apply {
        // keep different headers for the original and digest packets
        if (eg_intr_md.egress_rid == 0) {
            act_delete_sample_hdrs();
        } else {
            act_delete_packet_hdrs();
        }
    }
}

control SwitchEgressDeparser(packet_out pkt,
                             inout header_sample_t hdr,
                             in metadata_t eg_md,
                             in egress_intrinsic_metadata_for_deparser_t eg_intr_dprsr_md)
                             {
    apply {
        pkt.emit(hdr);
    }
}

Pipeline(SwitchIngressParser(), SwitchIngress(), SwitchIngressDeparser(), SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;

Switch(pipe) main;

