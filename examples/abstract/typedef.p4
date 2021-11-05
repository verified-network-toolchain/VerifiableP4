/*
Copyright 2016 VMware, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

typedef bit<4> PortId;

extern Checksum16<C> {
    Checksum16(C param);
    void run(in bit<16> ix);  // internally calls f
    @synchronous(run) abstract bit<16> f(in C ix, in PortId p);
}

typedef bit<8> PortId;

control c(inout bit<16> p) {
    Checksum16<bit<16>>(16w32) cntr = {

        bit<16> f(in bit<16> ix, in PortId p) {  // abstract method implementation
            return ix+2;
        }
    };

    apply {
        cntr.run(6);
    }
}

control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;


/* Similarly
typedef bit<4> PortId;
extern Checksum16 {
    Checksum16();
    bit<16> f(in PortId p);
}

typedef bit<8> PortId;
control c(inout bit<16> p) {
    Checksum16() cs;
    apply {
        cs.f(8w10);
    }
}

control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;
*/