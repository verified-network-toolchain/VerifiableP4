/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

header myHeader_t {
    bit<8> firstByte;
}

struct metadata {
    /* empty */
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


control Increment(inout bit<8> var) {
    apply {
        var = var + 1;
    }
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    bit<8> x = 2;
    Increment() incr;
    apply {
        incr.apply(x);
        hdr.myHeader.firstByte = x;
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
