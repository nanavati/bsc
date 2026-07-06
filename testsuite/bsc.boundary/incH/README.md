# incH: -suggest-contract (increment H / A25 migration aid)

`bsc -suggest-contract` prints a paste-able `contract_<Ifc>` literal derived
from the inferred schedule: the declarable CF/SB/SBR freedoms (ME/P pairs
omitted) plus constant-readiness facts. Test 1 checks the emitted block for a
module with a distinctive schedule; test 2 round-trips the suggestion --
pasted beside the interface, the identical member compiles green against it.
