# Omni-Paxos Specification
This is a TLA+ specification of the Omni-Paxos protocol. It is written in PlusCal and follows the pseudo-code from the paper with some additional variables needed for model checking. Furthermore, the Ballot Leader Election and clients are modeled as an external process `ble_client` that generates events to the servers.

## Model Checking
To model check it, open the specification in the TLA+ Toolbox and add a new model. Make sure to check `Validity` and `UniformAgreement` as invariants. The third property `Integrity` is checked with assertions (see comments in the code). Furthermore, turn off `deadlock` checking since there will be some executions in the model checker where the processes do `await`on certain messages that do not correspond to the real message flow.

We managed to model check with the `NSERVERS = 3`, `NPROPOSALS = 3`, `MAXB = 3` in ~20 minutes. This checks a cluster of 3 servers with 3 proposals over 3 ballot numbers i.e., leader changes.
