/* -*- P4_16 -*- */
#include <core.p4>
#include <v1model.p4>

/*************************************************************************
*********************** H E A D E R S  ***********************************
*************************************************************************/

typedef bit<9>  egressSpec_t;

header myHeader_t {
    // In: rw = 0 => BF.query; rw = 2 => BF.add
    // Out: rw = 0 => not in BF; rw = 1 => in BF
    bit<8> rw; 
    bit<16> data;
}

struct custom_metadata_t {
    bit<32> index0;
    bit<32> index1;
    bit<32> index2;
    bit<1> member0;
    bit<1> member1;
    bit<1> member2;
}

struct headers {
    myHeader_t myHeader;
}

/*************************************************************************
*********************** P A R S E R  ***********************************
*************************************************************************/

parser MyParser(packet_in packet,
                out headers hdr,
                inout custom_metadata_t meta,
                inout standard_metadata_t standard_metadata) {

    state start {
        packet.extract(hdr.myHeader);
        transition accept;
    }
}


/*************************************************************************
**************  I N G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

#define HASH_BASE 10w0
#define HASH_MAX 10w1023
#define NUM_HASH 3
#define NUM_ENTRY 32w1024
#define PAD0 3w3
#define PAD1 5w5
#define PAD2 7w7

register<bit<1>>(NUM_ENTRY) bloom0;
register<bit<1>>(NUM_ENTRY) bloom1;
register<bit<1>>(NUM_ENTRY) bloom2;

control Add(inout headers hdr, inout custom_metadata_t meta) {
    apply{
        hash(meta.index0, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD0}, HASH_MAX);
        hash(meta.index1, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD1}, HASH_MAX);
        hash(meta.index2, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD2}, HASH_MAX);

        bloom0.write(meta.index0, 1);
        bloom1.write(meta.index1, 1);
        bloom2.write(meta.index2, 1);
    }
}

control Query(inout headers hdr, inout custom_metadata_t meta) {
    apply{
        hash(meta.index0, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD0}, HASH_MAX);
        hash(meta.index1, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD1}, HASH_MAX);
        hash(meta.index2, HashAlgorithm.crc16, HASH_BASE, {hdr.myHeader.data, PAD2}, HASH_MAX);

        bloom0.read(meta.member0, meta.index0);
        bloom1.read(meta.member1, meta.index1);
        bloom2.read(meta.member2, meta.index2);

        hdr.myHeader.rw = (bit<8>) (meta.member0 & meta.member1 & meta.member2);
    }
}

control MyIngress(inout headers hdr,
                  inout custom_metadata_t meta,
                  inout standard_metadata_t standard_metadata) {

    /* apply forwarding logic */
    action do_forward(egressSpec_t port) {
        standard_metadata.egress_spec = port;
    }
    
    apply {
        if (hdr.myHeader.isValid()) {
            do_forward(1);
            if (hdr.myHeader.rw == 0) {
                Query.apply(hdr, meta);
            } else if (hdr.myHeader.rw == 2) {
                Add.apply(hdr, meta);
            }
        }
    }
}

/*************************************************************************
****************  E G R E S S   P R O C E S S I N G   *******************
*************************************************************************/

control MyEgress(inout headers hdr,
                 inout custom_metadata_t meta,
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

control MyVerifyChecksum(inout headers hdr, inout custom_metadata_t meta) {  
    /* empty */ 
    apply {  }
}

control MyComputeChecksum(inout headers  hdr, inout custom_metadata_t meta) {
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
