extern void testext(in bit<1> check, in bit<1> check2);
extern void testext(in bit<1> check, in bit<1> check1);


control c(out bit<16> b) {
    apply {
        testext(check=1, check2=1);
	testext(check=1, check1=1);
	b = 0;
    }
}

control ctr(out bit<16> b);
package top(ctr _c);

top(c()) main;
