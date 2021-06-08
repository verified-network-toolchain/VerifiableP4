/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;

header myHeader_t {
    bit firstBit;
    bit<7> padding;
}

struct metadata {
    bit<4> counter;
}

struct headers {
    myHeader_t myHeader;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {

    state start {
	packet.extract(hdr.myHeader);
        transition accept;
    }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    // counter(32w1, CounterType.packets_and_bytes) myCounter;
    register<bit<4>>(32w2) myCounter;


    action drop() {
        myCounter.read(meta.counter, 0);
        myCounter.write(0, meta.counter + 1);
        standard_metadata.egress_spec = 0; // drop_port := 0
        // mark_to_drop(standard_metadata);
    }

    action do_forward(egressSpec_t port) {
        myCounter.read(meta.counter, 1);
        myCounter.write(1, meta.counter + 1);
        standard_metadata.egress_spec = port;
    }

    table forward {
        key = {
            hdr.myHeader.firstBit: exact;
        }
        actions = {
            do_forward;
            drop;
        }
        size = 2;
        default_action = drop();
        const entries = {
            (1) : do_forward(48);
        }
    }

    apply {
        if (hdr.myHeader.firstBit == 1) {
            do_forward(48);
        } else {
            drop();
        }

        //if (hdr.myHeader.isValid()) {
        //    forward.apply();
        //}
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    /* empty */
    apply {  }
}


/*************************************************************************
***********************  D E P A R S E R  *******************************
*************************************************************************/

control MyDeparser(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.myHeader);
    }
}


/*************************************************************************
************************  C H E C K S U M ********************************
*************************************************************************/

control MyVerifyChecksum(inout headers hdr, inout metadata meta) {  
    /* empty */ 
    apply {  }
}

control MyComputeChecksum(inout headers  hdr, inout metadata meta) {
    /* empty */
    apply {  }
}

/*************************************************************************
***********************  S W I T C H  *******************************
*************************************************************************/

V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
