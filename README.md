# Verifiable P4
## Installation
There are two options to install Verifiable P4.
### Backend-only installation
This approach only installs the backend of Verifiable P4, which includes the operational semantics, program logic, and proof automation. With this installation, one can verify programs that are already translated into a Coq AST or check existing proofs.

The following steps install Verifiable P4<br>
TODO
### Full installation

This approach installs the the full Verifiable P4.

1. Install OPAM 2 following the official [OPAM installation
   instructions](https://opam.ocaml.org/doc/Install.html). Make sure
   `opam --version` reports version 2 or later.
   
2. Create a new switch such as `artifact` and add Coq repository
```
opam switch create artifact 4.14.0
eval $(opam env --switch=artifact)
opam repo add coq-released https://coq.inria.fr/opam/released
```

3. Install dependencies for petr4
```
opam install coq bignum coq-equations coq-compcert coq-vst-zlist coq-record-update
opam install alcotest cstruct-sexp js_of_ocaml-lwt js_of_ocaml-ppx ppx_import
opam install core_unix core_kernel ppx_deriving_yojson ANSITerminal p4pp
```

4. Install `petr4`: in a proper directory
```
git clone https://github.com/verified-network-toolchain/petr4.git --branch poulet4-resolve
cd petr4
make; make install
```

5. Install dependencies for Verifiable P4
```
opam install coq-hammer coq-vst
```

6. Make Verifiable P4: in another proper directory
```
git clone https://github.com/verified-network-toolchain/VerifiableP4.git
cd VerifiableP4
make
```

## Workflow
1. Translate a P4 program into Coq AST
```
./ast_gen.sh name_of_program.p4
```
2. Start to verify a program<br>
TODO
