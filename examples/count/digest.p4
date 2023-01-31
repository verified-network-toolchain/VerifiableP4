#include <core.p4>
#include <tna.p4>
#include "common/headers.p4"
#include "common/util.p4"

/* A simple digest of header fields. */
struct digest_t {
    ipv4_addr_t src_addr;
    ipv4_addr_t dst_addr;
}

struct metadata_t {
    bit<32> num_pkt;
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

control SwitchIngress(inout header_t hdr,
                      inout metadata_t ig_md,
                      in ingress_intrinsic_metadata_t ig_intr_md,
                      in ingress_intrinsic_metadata_from_parser_t ig_intr_prsr_md,
                      inout ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md,
                      inout ingress_intrinsic_metadata_for_tm_t ig_intr_tm_md)
                      {

    Register<bit<32>, bit<1>>(32w1, 32w0) reg_counter;
    RegisterAction<bit<32>, bit<1>, bit<32>>(reg_counter) regact_counter = {
        void apply(inout bit<32> val, out bit<32> rv) {
            val = (val + 32w1);
            rv = val;
        }
    };
    action act_counter() {
        ig_md.num_pkt = regact_counter.execute(1w0);
    }
    table tbl_counter {
        actions = {
            act_counter();
        }
        default_action = act_counter();
        size = 1;
    }

    apply {
        tbl_counter.apply();
        if (ig_md.num_pkt[9:0] == 10w0) {
            ig_intr_dprsr_md.digest_type = 1;
        }
    }
}

control SwitchIngressDeparser(packet_out pkt,
                              inout header_t hdr,
                              in metadata_t ig_md,
                              in ingress_intrinsic_metadata_for_deparser_t ig_intr_dprsr_md)
                              {
    Digest<digest_t>() digest;

    apply {
        // Generate a digest, if digest_type is set in MAU.
        if (ig_intr_dprsr_md.digest_type == 1) {
            digest.pack({hdr.ipv4.src_addr, hdr.ipv4.dst_addr});
        }
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

