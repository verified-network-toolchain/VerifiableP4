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

#include <core.p4>
#include <v1model.p4>

enum bit<8> Suits {
    Spade = 0,
    Diamond = 1,
    Heart = 2,
    Club = 3
}

header hdr {
    bit<32> f;
    varbit<8> g;
}

control compute(inout hdr h) {
    apply {
    	bool i = true;
    	int<8> j = -1;
        hdr[5] tmp;
        tmp[0].f = h.f + 1;
        h.f = tmp[j].f;
    }
}

#include "arith-inline-skeleton.p4"
