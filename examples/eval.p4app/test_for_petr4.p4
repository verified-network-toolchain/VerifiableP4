/*

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

#include <core.p4>
#include <v1model.p4>

header hdr {
    bit<16> input;
    int<16> output;
    bit<32> output2;
}

struct meta {
    tuple<bool, bit<1>> x;
}

enum bit<8> E {
  e1 = 1,
  e2 = 2
}

struct S {
    bit<32> a;
    bit<32> b;
}

struct S1 {
    E a;
    bit<32> b;
}

struct S2 {
    bit<8> a;
    bit<32> b;
}

enum bit<16> E2 {
  e3 = 1,
  e4 = 2
}

const bit<16> k1 = 1;
const int<16> k2 = 1;
const int k3 = 1;
const E2 k4 = E2.e3;

header H1 {
  bit<8> f;
}
header H2 {
  bit<16> g;
}
header_union U {
  H1 h1;
  H2 h2;
}

type bit<8> NewT;

control compute(inout hdr h) {

    apply {

        NewT test3;
        hdr test4;

        E e = E.e1;

    }
}

#include "arith-inline-skeleton.p4"