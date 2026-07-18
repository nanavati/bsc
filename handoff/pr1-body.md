## Summary

`getIOProps` labels an argument inout `unused` whenever its net is
re-exposed at an interface inout — one net at two pins, mislabeled at
one of them:

```bsv
module sysArgToIfc #(Inout#(int) i_in) (InoutIFC);
   interface i_out = i_in;   // i_in reported "unused"
endmodule
```

The cause is not a deliberate convention: the interface-inout
definitions (`io_ds` in the `ASPackage`) are missing from `getIOProps`'
use tracking (`wireMap_in` records submodule inputs and module outputs
as sinks; `defuseMap` is built only from the ordinary defs), so the
argument pin appears to have no uses at all. The mislabel is recorded
in the `.bo` wrapper attributes and propagates up parent compiles: a
parent passing its own inout argument into such a child reports its
pin `unused` too (e.g. `mkT` in `bsc.bluetcl/commands/Test.bsv`).

The fix records the signals referenced by the interface-inout
definitions as live `inout` sinks, mirroring the existing
`output_pairs` entry for outputs. Both pins of the net are now
reported live.

## Testing

- `testsuite/bsc.verilog/portprops/InoutProps_ArgToIfc` golden updated
  (`io_arg IO 32 unused` → `io_arg IO 32 inout`); the directory passes.
- Affected golden files regenerated; the testsuite directories that
  exercise inout feedthroughs (`bsc.verilog/inout`,
  `bsc.names/portRenaming/*`, `bsc.bluetcl/*`) pass.
- Note: an inout argument that is genuinely unconnected is still
  reported `unused` (`InoutProps_UnusedArg` is unchanged).
