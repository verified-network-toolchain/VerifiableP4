GENERATOR_PORT = 196 # the port that the generator is attached to

import sys, os, subprocess
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/libs")
sys.path.append("/home/vagrant/VerifiableP4/examples/sampler/libs")
from controldriver import *
clib_driver_so = find_clib_driver_file(dict(globals()))
c = Controller(clib_driver_so)

c.start_periodic_pktgen(b'\x01\x02\x03\x04' + b'\x55'*124, timer_ns=1_000_000_000, pktgen_port=GENERATOR_PORT, generator_id=1)
c.close()
print ('control startup complete.')
