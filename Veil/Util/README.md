# `Veil/Util`

Generic helpers that are not specific to Veil. Some of them replace code Veil
used to get from mathlib, since Veil no longer depends on mathlib.

## Namespace rule

**Nothing in this directory may declare into the root namespace, or into a
namespace owned by another library (`List`, `Equiv`, `Function`, ...).**

Two libraries cannot be imported together if they declare the same name, so a
`List.mem_sublists` here would stop a downstream project from importing Veil
alongside mathlib. Helpers therefore live in `Veil.List`, `Veil.Tactic`,
`Veil.Deriving`, `Veil.ProxyType`, `Veil.TermReduce`.

Generated implementation helpers follow the same rule: use `Veil.generatedName` to
construct names under `Veil.Generated.<family>.<fully-qualified-type>.<role>`.
Proxy and enum deriving must not add helpers named `proxyType`, `proxyTypeEquiv`,
or `enumList` to the user's type namespace. Lean's own generated declarations,
such as `<type>.ctorIdx`, are referenced rather than recreated.
Trace registrations use a `veil.*` prefix; a surrounding namespace does not qualify
an explicitly quoted registration name. The proxy syntax is `veil_proxy_equiv%`,
so it cannot be confused with Mathlib's `proxy_equiv%`.

The cost is that dot notation is unavailable for them: write
`Veil.List.nodup_of_pairwise h`, not `h.nodup`. That is intentional -- dot
notation would require declaring into `List`.

Note that `namespace Veil.List` makes the bare name `List` refer to
`Veil.List`, so these files say `open _root_.List` to reach the real one.

Files predating the mathlib removal (`ListSplit.lean`, `Meta.lean`,
`EnvExtensions.lean`, `ShardedSetUInt.lean`, `SortedArray.lean`,
`SortedList.lean`, `TreeSetMisc.lean`) still declare into `OrdList`,
`OrdArray`, `Array`, `Std.TreeSet` and `Lean`. Those names were already
coexisting with mathlib before the migration, so they are left alone; do not
add new ones.

## Adapted from mathlib

Baseline: mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` (v4.32.0), the
revision pinned before mathlib was dropped. Both projects are Apache-2.0; each
file keeps the upstream copyright header.

### Near-verbatim copies

Sync these if the upstream file gets a fix. The namespace and `module` header
differ; `ProxyType.lean` also uses Veil-owned generated names, syntax, and tracing.

| File | Upstream |
| --- | --- |
| `ProxyType.lean` | `Mathlib/Tactic/ProxyType.lean` |
| `SplitIfs.lean` | `Mathlib/Tactic/SplitIfs.lean` |
| `SetTactic.lean` | `Mathlib/Tactic/Set.lean` |
| `TermReduce.lean` | `Mathlib/Util/TermReduce.lean` |

### Subsets

| File | Upstream | What was taken |
| --- | --- | --- |
| `EnumList.lean` | `Mathlib/Tactic/DeriveFintype.lean` | `mkFintypeEnum`, renamed `mkEnumList`; it generates the constructor list and its lookup lemmas, and no longer produces a `Fintype` instance |
| `Tactics.lean` | `Mathlib/Tactic/Basic.lean` | the `introv` elaborator |
| `Tactics.lean` | `Mathlib/Tactic/DefEqTransformations.lean` | the `whnf` tactic |
| `UnhygienicCasesM.lean` | `Mathlib/Tactic/CasesM.lean` | predates the migration; adds names for the new hypotheses |

### Restated

Statements match upstream; the proofs are written against Lean core and
Batteries instead of mathlib's order and finset hierarchy. Treat upstream as a
reference, not as something to copy from.

| File | Upstream | Declarations |
| --- | --- | --- |
| `Destutter.lean` | `Data/List/Destutter.lean`, `Data/List/Defs.lean` | `destutter`, `destutter'` and their lemmas |
| `Permutations.lean` | `Data/List/Defs.lean` | `permutationsAux2`, `permutationsAux`, `permutations` |
| `Equiv.lean` | `Logic/Equiv/Defs.lean`, `Logic/Equiv/Prod.lean`, `Logic/Function/Defs.lean` | `Equiv` and its API, `sigmaEquivProd`, `Function.Injective`/`LeftInverse`/`RightInverse` |
| `List.lean` | `Data/List/Pi.lean` | `pi`, `mem_pi` |
| `List.lean` | `Data/List/Defs.lean` | `dedup` -- like mathlib, it keeps the **last** occurrence of a duplicate |
| `List.lean` | `Data/List/Dedup.lean` | `mem_dedup`, `nodup_dedup` |
| `List.lean` | `Data/List/Sublists.lean` | `mem_sublists` |
| `List.lean` | `Data/List/Nodup.lean` | `nodup_of_pairwise` (`Pairwise.nodup`), `nodup_filter` (`Nodup.filter`), `nodup_flatMap` |
| `List.lean` | `Data/List/Sort.lean` | `sublist_of_subperm_of_pairwise`, `eq_of_pairwise_of_mem_iff` (`Pairwise.eq_of_mem_iff`) |

`List.filter_count_overlap` and `List.filter_count_mono` are Veil's own; they
replace the Finset cardinality arguments in the quorum proofs.

## Known overlap with mathlib: tactic syntax

`set`, `split_ifs`, `introv`, `whnf`, `beta%` and `delta%` are
declared here with the same tokens mathlib uses. The declarations live in
Veil's namespaces, so importing both libraries is not an error, but each token
then parses into a choice node that Lean resolves by trying both elaborators.

Keeping mathlib's spelling is deliberate: these are the names users already
know, and the repository uses them in several dozen places. If the ambiguity
ever becomes a problem, rename the tokens here rather than the declarations.
