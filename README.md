# ProD3
## Running P4 code in Petr4
### Environment set-up
You can follow the instructions from the link below to **install Petr4 from source**.
https://github.com/cornell-netlab/petr4/#installing-from-source

### Running examples
Run the parser to generate AST in JSON format:
```sh
petr4 typecheck basic.p4 -I ../../includes -json > AST.json
```
Run the parser to generate AST in a pretty format:
```sh
petr4 typecheck basic.p4 -I ../../includes -pretty -v > AST
```
Run the interpreter:
```sh
petr4 run basic.p4 -ctrl-json ctrl.json -pkt-str <a packet in hex, e.g. 2A2A2A2A2A2A2A2A2A2A2A2A21> -I ../../includes/ -T v1 > eval_result
```

## Running P4 code on v1model target
### Environment set-up
Current examples adopts the environment set-up of the P4 tutorials. You can follow the instructions from the link below to set up the virtual machine, and then clone this repository to the vm.
https://github.com/p4lang/tutorials

### Running examples
In your shell, run:
```sh
make run
```
This will:

- compile basic.p4, and
- start the topology in Mininet and configure the switch with the appropriate P4 program + table entries, and
- configure all hosts with the commands listed in topology/topology.json

You should now see a Mininet command prompt, and you can bring up the hosts with
```sh
mininet> xterm h1 h2
```
and use scapy commands to send & receive packets:
```sh
scapy> sendp(Ether(src='00:00:00:00:00:00', dst='FF:00:00:00:00:00')/IP(), iface='eth0')
scapy> sniff(iface='eth0', prn=lambda x:x.show())
```
Type exit to leave each xterm and the Mininet command line. Then, to stop mininet:
```sh
make stop
```
And to delete all pcaps, build files, and logs:
```sh
make clean
```
### Note
In the count example, to read the counter values of the P4 program at runtime, you can open another shell and run the starter code:
```sh
sudo ./mycontroller.py
```
This will build the connection to the switch and print the counters every 2 seconds.
