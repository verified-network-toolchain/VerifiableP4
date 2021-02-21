#include <core.p4>
header h { }
control c(out bit<32> x) {
    apply {
        h[4] stack;
        h[5] s1;
        bit<32> sz = stack.size;
        x = sz;
    }
}
control Simpler(out bit<32> x);
package top(Simpler ctr);
top(c()) main;
