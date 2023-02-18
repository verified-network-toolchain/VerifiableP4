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
P4. It corresponds to Section 3.1 of the paper.

### [Semantics](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Semantics)

This folder corresponds to Section 3.2 of the paper. In particular,

- [Semantics.v](https://github.com/verified-network-toolchain/petr4/blob/b4a332e47a58359b5622eeb0936caa59f676c187/deps/poulet4/lib/P4light/Semantics/Semantics.v)
contains the big-step operational semantics.

- [Interpreter.v](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Semantics/Interpreter.v)
is the reference interpreter.

- [InterpreterSafe.v](https://github.com/verified-network-toolchain/petr4/blob/poulet4/deps/poulet4/lib/P4light/Semantics/InterpreterSafe.v)
is the correctness proof of the reference interpreter.

### [Transformations](https://github.com/verified-network-toolchain/petr4/tree/poulet4/deps/poulet4/lib/P4light/Transformations)

TODO

## Program Logic

The program logic and related tactics are defined in the
[core](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/core)
folder. It corresponds to Section 3.3 of the paper.

## Verification Examples

### [Sliding-Window Bloom Filter](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/sbf)

**Theorem 1** in Section 2.1 is scattered in
[`LightFilter.v`](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/sbf/LightFilter.v),
named `query_insert_same`, `query_insert_other`, `query_clear`,
`ok_insert`, `ok_clear` and `ok_empty`.

**Theorem 2** in Section 2.2 is scattered in
[`verif_Filter_all.v`](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/sbf/verif_Filter_all.v),
named `Filter_insert_body`, `Filter_query_body` and
`Filter_clear_body`.

### [Count-Min-Sketch](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/cms)

This folder is about our another example, the
count-min-sketch. Theorems similar to **Theorem 1** and **Theorem 2**
can be found in
[`LightModel.v`](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/cms/LightModel.v)
and
[`verif_CMS_all.v`](https://github.com/verified-network-toolchain/VerifiableP4/tree/master/examples/cms/verif_CMS_all.v)
