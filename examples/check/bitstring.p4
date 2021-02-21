#include <core.p4>
header h { }
control c(out bit<32> x) {
    apply {
        bit<8> bits = 255;
        bit<7> subbits = bits[5:-1];
        x = 1;
    }
}
control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;
