typedef bit<8> PortId;
control c(inout PortId p) {
    apply {
        p = p + 1;
    }
}

typedef bit<4> PortId;
control d() {
    apply{
        c() ci;
        bit<8> x = 4;
        ci.apply(x);
    }
}
