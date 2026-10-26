# Cosmos DB consistency model

`swscop.tla` is Scenario 1 from [Azure/azure-cosmos-tla](https://github.com/Azure/azure-cosmos-tla),
pinned to [source revision `a8357c9`](https://github.com/Azure/azure-cosmos-tla/blob/a8357c9c0a8d0ed710c68a64bc3a9ed0dc860a8a/scenario1/swscop.tla).
See the [upstream explanation](https://github.com/Azure/azure-cosmos-tla/blob/a8357c9c0a8d0ed710c68a64bc3a9ed0dc860a8a/scenario1/README.md).
These CFG files were reconstructed locally from the source constants and invariants.
The Veil translation is [CosmosDB.lean](../../../Examples/TLA/CosmosDB.lean).

The upstream model is copyright Microsoft Corporation and is distributed under
the MIT license. [LICENSE](LICENSE) is an unmodified copy of the license at the
pinned revision; it also covers the upstream material adapted or quoted in the
Veil translation. The local TLA+ source differs only in source/license comments
and trailing whitespace; its PlusCal algorithm and generated TLA+ are unchanged.
The locally reconstructed CFGs are not files supplied by the upstream project.

The source assumes `NumClients = 1` and `MaxNumOp < 10`. All configurations here
respect those assumptions and perform finite safety checking without symmetry,
views, state constraints or depth bounds. `CHECK_DEADLOCK FALSE` allows the client
to finish at `Done`, where no further action is enabled.

## Run TLC

With Java and `tla2tools.jar`, run from the repository root:

```sh
cd Benchmarks/TLA/CosmosDB
TLA_JAR=/absolute/path/to/tla2tools.jar
java -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC \
  -workers 1 -noGenerateSpecTE -metadir /tmp/cosmosdb-tlc \
  -config properties-Bounded_Staleness-3-1.cfg swscop.tla
```

Replace the CFG filename to select another case. A successful complete check prints
`Model checking completed` and `0 states left on queue`. An invariant violation
prints its name and a counterexample, and exits with a nonzero status.

## Property checks and bug reproduction

`properties-*.cfg` checks all five source invariants with `MaxNumOp = 3`:

| CFG | Expected result |
| --- | --- |
| `properties-Strong-3-1.cfg` | All invariants hold; 26 distinct states |
| `properties-Session-3-1.cfg` | All invariants hold; 26 distinct states |
| `properties-Bounded_Staleness-3-0.cfg` | All invariants hold; 26 distinct states |
| `properties-Bounded_Staleness-3-1.cfg` | `Strong` violation after 8 transitions |
| `properties-Eventual-3-1.cfg` | `Strong` violation after 8 transitions |
| `properties-Consistent_Prefix-3-1.cfg` | `Strong` violation after 8 transitions |

The last three cases write `1`, receive its acknowledgement, then read `0`.
The final database is `<<0, 1>>`, but the client's last read is `0`.
This is the upstream model's intended demonstration of weaker consistency,
not evidence of a Cosmos DB implementation bug.

For deeper counterexamples, select either of these CFGs. They check only the
original `Bounded_Staleness` invariant, so the earlier `Strong` violation does not
stop the search; the source actions are unchanged.

| CFG | Expected violation | Transitions / trace states |
| --- | --- | --- |
| `bug-Eventual-Bounded_Staleness-3-1.cfg` | `Bounded_Staleness` | 16 / 17 |
| `bug-Eventual-Bounded_Staleness-3-2.cfg` | `Bounded_Staleness` | 24 / 25 |

For `K = 2`, the third write produces database `<<0, 1, 2, 3>>`; returning `0`
falls outside its last three entries. Increasing `MaxNumOp` alone does not postpone
the earliest `Strong` counterexample. The historical Veil setting `MaxNumOp = 20`
is outside the source assumption and is not represented by a CFG here.

## Complete state counts

`counts-*.cfg` checks `Eventual`, `Consistent_Prefix` and `Session`, allowing full
exploration even where freshness properties fail. Filenames encode mode, `MaxNumOp`
and `K`. With `MaxNumOp = 3, K = 1`, TLC and Veil agree at:
Eventual **143**, Consistent Prefix **143**, Session **26**, Bounded Staleness **79**,
and Strong **26**. The additional Bounded Staleness cases give **26** states for
`MaxNumOp = 3, K = 0`, and **2** for `MaxNumOp = 0, K = 1`.
Counts from runs that stop at a violation are incomplete and should not be compared.

The six corresponding Veil commands are commented out in `CosmosDB.lean`;
uncomment one and run `lake build Examples.TLA.CosmosDB`. They check all declared
invariants using the default `Nat` fingerprints and search configuration. The deeper
cases require an isolated check of `Bounded_Staleness`. Agreement on these finite cases
is validation evidence, not a proof of equivalence.

## Reproduce the comparison

With Python 3, Java, Lake and the repository's Lean dependencies available, run:

```sh
python3 Benchmarks/TLA/CosmosDB/check.py --tla-jar /path/to/tla2tools.jar
```

The script downloads the pinned source and license, checks the source comparison
described above, builds the translation, and runs all 15 CFGs against TLC and Veil.
It generates temporary Lean modules from the current translation, changing only
the module name and selected invariants to match each CFG. The source invariants
`Eventual` and `Consistent_Prefix` are identical, so both map to Veil's `Eventual`.
The five source consistency modes remain distinct choices in both models.

The comparison script explicitly selects `interpreted` mode, sequential search
and `UInt64` fingerprints, with no depth bound. TLC uses one worker and no symmetry
or state constraints. Completed runs must agree on distinct-state counts; failing
runs must agree on the violated
invariant and counterexample length. The script retains commands, logs, generated
Lean code and input hashes under a temporary directory printed on startup; use
`--output DIR` to choose a new output directory. Network access is needed to
retrieve the fixed upstream files.

TLC 2.20 and Veil, with the script settings above, agreed on all 15 configurations:
10 completed runs (including the seven count configurations above) and five
expected violations (8, 8, 8, 16 and 24 transitions). State/action review also
checked FIFO messages, the 1-based to 0-based index shift, updates that use newly
received messages, and the inclusive `K + 1` entry window for bounded staleness.
These checks do not compare entire reachable graphs, prove equivalence, or check
liveness or fairness; the source specifies no fairness or liveness property here.
