def add_mc_nodes(c, COLLECTOR_PORT,COLLECTOR_REPLICA_ID,COLLECTOR_MULTICAST_GROUP):
  packet_replicas = [(COLLECTOR_PORT, COLLECTOR_REPLICA_ID)]
  c.add_multicast_group(COLLECTOR_MULTICAST_GROUP, packet_replicas)


COLLECTOR_PORT = 129 # the port that the collector is attached to
COLLECTOR_MULTICAST_GROUP = 1 # the multicast group that includes the collector's port
COLLECTOR_REPLICA_ID = 123 
# replica_id is an arbitrary 16-bit value -- the P4 program just test != 0

import sys, os
sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/libs")
sys.path.append("/home/vagrant/VerifiableP4/examples/sampler/libs")
from controldriver import *
clib_driver_so = find_clib_driver_file(dict(globals()))
c = Controller(clib_driver_so)

add_mc_nodes(c, COLLECTOR_PORT,COLLECTOR_REPLICA_ID,COLLECTOR_MULTICAST_GROUP)
c.close()
print ('control startup complete.')



# # Control plane of the multicast sampler

# COLLECTOR_PORT = 129          # the port that the collector is attached to
# COLLECTOR_MULTICAST_GROUP = 1 # the multicast group that includes the collector's port
# COLLECTOR_REPLICA_ID = 123    # replica_id is an arbitrary 16-bit value; 0 is reserved for the original packet

# import sys, os
# sys.path.append(os.path.dirname(os.path.realpath(__file__))+"/libs")
# # Problem 1: recognizing relevant paths
# sys.path.append("/home/vagrant/VerifiableP4/examples/sampler/libs")

# from controldriver import *

# # Crete the controller object
# # Problem 2: was locals() in the original code
# clib_driver_so = find_clib_driver_file(dict(globals()))
# c = Controller(clib_driver_so)

# # This ports up function is designed for Jsonch testbed
# # def ports_up():
# #   if ((len(sys.argv) > 1) and (sys.argv[1] == 'ports_up')):
# #     c.port_up(128, pal_port_speed_t.BF_SPEED_10G, pal_fec_type_t.BF_FEC_TYP_NONE)
# #     c.port_up(129, pal_port_speed_t.BF_SPEED_10G, pal_fec_type_t.BF_FEC_TYP_NONE)

# # Add a multicast group with identifier COLLECTOR_MULTICAST_GROUP
# # that replicates the packet 1 time. The 1st replica should go to 
# # port COLLECTOR_PORT and should have its egress_rid metadata 
# # set to value COLLECTOR_REPLICA_ID.
# # def add_mc_nodes():
# packet_replicas = [(COLLECTOR_PORT, COLLECTOR_REPLICA_ID)]
# c.add_multicast_group(COLLECTOR_MULTICAST_GROUP, packet_replicas)

# # Problem 3: global variables are only recognized as local, so not accessible in functions
# # add_mc_nodes()
# c.close()
# print('Multicast rules entered.')
