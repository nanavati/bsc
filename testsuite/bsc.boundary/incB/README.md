# bsc.boundary/incB

Sealing soundness (A100) for implementation groups: sealing a member's
boundary at the declared contract drops the member's accidental
scheduling freedoms (the parent's rule order follows the declaration,
verified against an unsealed counterfactual, and the design simulates
under both selections); alternates must match the group pinout exactly
(extra module arguments are rejected at the group site); and the
`impls.json` manifest carries a normalized pinout record.  The sEXT
(external-conflict) rejection is documented but disabled -- see
incB.exp for why it is not constructible from source today.
