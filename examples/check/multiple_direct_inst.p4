bit<16> max(in bit<16> left) {
    if (left > 256)
        return left;
    return 256;
}


control c(out bit<16> b) {
    action a(inout bit<16> b2, bit<16> d) {
        b2 = d;
    }
    table t {
        actions = { a(b); }
        default_action = a(b, 0);
    }
    apply {
    	b = 0;
        t.apply();
	b = max(10);
    }
}

control d(out bit<16> b) {
    c() ci;
    apply {
	ci.apply(b);
	ci.apply(b);
    }
}

control ctr(out bit<16> b);
package top(ctr _c1, ctr _c2);

top(c(), c()) main;
