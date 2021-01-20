#include <core.p4>
#include <v1model.p4>

bit<16> max(in bit<16> left) {
    if (left > 256)
        return left;
    return 256;
}

error {
    test1,
    test2
}

error {
    test3,
    test4
}

match_kind {
    test1,
    test2
}

match_kind {
    test3,
    test4
}


control c(out bit<16> b) {
// Not allowed
//    error {
//        test3,
//        test4
//    }

//    match_kind {
//        test3,
//        test4
//    }

    apply {
	b = max(10);
    }
}

control ctr(out bit<16> b);
package top(ctr _c);

top(c()) main;
