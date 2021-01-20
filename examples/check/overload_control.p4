bit<16> max(in bit<16> left) {
    if (left > 256)
        return left;
    return 256;
}


control c(out bit<16> b) {
    apply {
	b = max(10);
    }
}

control c(out bit<16> b, out bit<16> d) {
    apply {
	b = max(10);
	d = 0;
    }
}

control ctr(out bit<16> b);
package top(ctr _c);

top(c()) main;
