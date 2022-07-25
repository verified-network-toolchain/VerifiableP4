# Verifiable P4
## Installation
There are two options to install Verifiable P4.
### Backend-only installation
This approach only installs the backend of Verifiable P4, which includes the operational semantics, program logic, and proof automation. With this installation, one can verify programs that are already translated into a Coq AST or check existing proofs.

The following steps install Verifiable P4<br>
TODO
### Full installation
This approach installs the the full Verifiable P4.
1. Install `petr4`: in a proper directory
```
git clone https://github.com/verified-network-toolchain/petr4/tree/poulet4 --branch poulet4
cd petr4
make; make install
```
2. Install Verifiable P4
```
git clone https://github.com/verified-network-toolchain/VerifiableP4.git
make; make install
```

## Workflow
1. Translate a P4 program into Coq AST
```
./ast_gen.sh name_of_program.p4
```
2. Start to verify a program<br>
TODO
