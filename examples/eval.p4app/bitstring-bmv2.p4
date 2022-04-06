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
    table table_test {
        key = { h.input : ternary; 
                h.output : ternary; }
        actions = { NoAction; }
        const entries = {
            (k1 &&& k1, _)    : NoAction();
            (k4 &&& k4, _)    : NoAction();
            (k1 &&& k4, _)    : NoAction();
            (k4 &&& k1, _)    : NoAction();
            (k3 &&& k3, _)    : NoAction(); // Spec does not allow int in masking operation.
            (k3 &&& k1, _)    : NoAction(); // Spec does not allow implicit casts in masking operation.
            (_ , k2 &&& k2)   : NoAction(); // Spec does not allow int<> in masking operation.
            (_ , k2 &&& k3)   : NoAction(); // Spec does not allow int<> in masking operation.
            // (_, k1 &&& k1) : NoAction(); // error: Entry: Cannot unify bit<16> to int<16>
            // (_, k2 &&& k1) : NoAction(); // error: Entry: Cannot unify bit<16> to int<16>
        }
    }

    table table_test_2 {
        key = { h.input : range; 
                h.output : range; }
        actions = { NoAction; }
        const entries = {
            (k1 .. k1, _)    : NoAction();
            (k4 .. k4, _)    : NoAction();
            (k1 .. k4, _)    : NoAction();
            (k4 .. k1, _)    : NoAction();
            (_ , k2 .. k2)   : NoAction();
            (k3 .. k3, _)    : NoAction(); // Spec does not allow int in range operation.
            (k3 .. k1, _)    : NoAction(); // Spec does not allow implicit casts in masking operation.
            (_ , k2 .. k3)   : NoAction(); // Spec does not allow implicit casts in masking operation.
        }
    }

    apply {

        bit<8> x;
        x[1:0] = 1;
        bit<8> test1 = 32w0[21s7:0];
        bit<4> test2 = 16[3:0];
        NewT test3;
        hdr test4;
        table_test.apply();
        table_test_2.apply();
        E e = E.e1;
        // bit<16> x1 = 16w0 << E.e1;
        // bit<8> x2 = -E.e1; 
        // bit<4> x3 = E.e1[3:0];     
        bool x4 = 8w0 == E.e1;
        bit<8> x5 = 8w0 | E.e1;
        // bit<8> x6 = E.e1 << 3;     // Allowed in the spec; but not in BMV2: << left operand of shift must be a numeric type, not E
        // bit<16> x7 = E.e1 ++ 8w0;  // BMV2: Concatenation not defined on E and bit<8>
        // bit<4> x8 = 8w0[4 : E.e1];   // BMV2: bit indexes must be compile-time constants
        // x9 = 10 << e;

        // bool b1_ = { a = 1, b = 2 } == { a = 1, b = 2 }; // BMV2: error: ==: cannot compare initializers with unknown types
        bool b1 = { a = 8w1, b = 8w2 } == { a = 8w1, b = 8w2 };
        bool b2 = (S) { a = 1, b = 2 } == { a = 1, b = 2 };
        // bool b3 = { a = 1, b = 2 } == (S) { a = 1, b = 2 }; // BMV2: error: ==: Cannot unify struct S to unknown struct
        bool b4 = (S) { a = 1, b = 2 } == (S) { a = 1, b = 2 };

        bool b5 = { 1, 2 } == { 10w1, 2 };

        S s1 = { a = 1, b = 2 };
        S s2 = { a = 100, b = 2 };
        bool b6 = s1 == { a = 1, b = 2 };
        bool b7_ = s1 == (S) { a = 1, b = 2 };
        bool b7 = (S) { a = 1, b = 2 } == s1;
        bool b8 = s1 == s2;

        tuple<bit<8>, bit<8>> t1 = {1, 2};
        tuple<bit<8>, bit<8>> t2 = {1, 2};

        bool b9 = t1 == { 1, 2 };
        bool b10 = t1 == t2;

        bool b11 = s1 == { 1, 2 };

        bool b12 = {1, 2} == (S){ a = 1, b = 2 };

        // bool b13 = {1, true}[1];

        tuple<int, bit<8>> t3 = {1, E.e1};
        tuple<int, E> t4 = {1, E.e1};
        // bool b16 = t3 == t4;

        bool b14 = t1 == t3;

        S1 s3 = { a = E.e1, b = 2 };
        S2 s4 = { a = E.e1, b = 2 };
        // bool b15 = s3 == s4;

        hash(h.output2, HashAlgorithm.crc16, 32w0x00, {h.input}, 32w0xFFFFFFFF);
        //hash(h.output, HashAlgorithm.identity, 8w0x00, {h.input}, 24w0x123455);
        // bool i = true;
        // int<8> j = -128;
        // bit<8> k = 1;
        // h.f = (-16)[15:0];
        //h.paddings = 0;

        U u;
        H1 my_h1 = { 8w0 }; // my_h1 is valid
        u.h1 = my_h1;

        H2 my_h2;
        u.h2 = my_h2;
        if (u.h1.isValid()) {
            h.output = (int<16>)(16w0xDCBA);
        } else {
            h.output = (int<16>)(16w0x0101);
        }

    }
}

#include "arith-inline-skeleton.p4"