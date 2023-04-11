sampler.p4 is a simple P4 program that sends packets out of a fixed port and copies a digest of their header fields to a packet using the multicast engine.

- ``sampler.p4`` -- the P4 program
- ``sampler.py`` -- control plane to configure multicast

### Credit

Files modified based on Jsonch's multicast example.

### Usage

#### with makefile

##### ASIC simulator test
1. install the tofino sde and make sure $SDE and $SDE_INSTALL are set
2. compile sampler.p4 (``make build``)
3. run the test workload (``make test``)
4. the result should be: original packet out of port 128, sampled record out of port 129

##### on physical switch
1. change COLLECTOR_PORT in sampler.py to the switch CPU port
2. on the switch, compile sampler.p4 (``make build``)
3. launch bf_switchd and the control plane script (``make hw``)

##### with your own build environment
1. compile sampler.p4
2. launch the compiled project in bf_switchd
3. run the sampler.py control script to add multicast rules: 
'''
# from the directory with sampler.py, run:
$SDE_INSTALL/bin/bfshell -b sampler.py
'''