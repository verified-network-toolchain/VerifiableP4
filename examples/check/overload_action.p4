action max(in bit<16> left, in bit<16> right, out bit<16> output) {
    if (left > right)
        output = left;
    output = right;
}

action max(in bit<16> left, out bit<16> output) {
    if (left > 256)
        output = left;
    output = 256;
}


control c(out bit<16> b) {
    apply {
        max(10, 12, b);
	max(10, b);
    }
}

control ctr(out bit<16> b);
package top(ctr _c);

top(c()) main;
