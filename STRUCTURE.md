# Structure of Verifiable P4

## Petr4 (external)

The formal semantics of the P4 programming language is defined in the
[P4light](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light)
folder of the
[Petr4](https://github.com/verified-network-toolchain/petr4/tree/poulet4)
project. It has 4 sub-folders:

### [Architecture](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Architecture)

This folder contains the semantics of different targets supported by
the current system, such as
[V1 Model](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Architecture/V1ModelTarget.v)
and
[Tofino](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Architecture/Tofino.v).

### [Syntax](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Syntax)

This folder contains the definition of abstract syntax tree (AST) and
the value type of the P4 programming language used in the Verifiable
P4.

### [Semantics](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Semantics)

[Semantics.v](https://github.com/verified-network-toolchain/petr4/blob/b4a332e47a58359b5622eeb0936caa59f676c187/deps/poulet4/lib/P4light/Semantics/Semantics.v)
contains the big-step operational semantics.

[Interpreter.v](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Semantics/Interpreter.v)
is the reference interpreter.

[InterpreterSafe.v](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Semantics/InterpreterSafe.v)
is the correctness proof of the reference interpreter.

### [Transformations](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Transformations)

TODO

## Program Logic

The program logic and related tactics are defined in the
[core](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/core)
folder.

## Verification Examples

Our verification of the sliding-window Bloom filter, including the p4
source code, can be found in the
[sbf](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/sbf)
folder. The count-min-sketch example can be found in the
[cms](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/cms)
folder.
