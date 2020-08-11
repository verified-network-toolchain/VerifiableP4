# ProD3
## Environment set-up
Current examples adopts the environment set-up of the P4 tutorials. You can follow the instructions from the link below to set up the virtual machine, and then clone this repository to the vm.
https://github.com/p4lang/tutorials

# How to run examples?
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
