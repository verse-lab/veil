# Applied action atoms: `E(a x)` / `T(a x)` with theory-supplied arguments

The Veil-side companion to `LTLLib/EdgeLabels.md` §11 (the Veil side) and §12.10 (the per-edge cost of
edge labels). §11 landed `E(a)`/`T(a)`; this note is about the half of the applied form that does not
work, why, and what it costs to fix.

Written against the tree at `liveness-mc` (2026-09-22). No code was changed while writing it; every
claim marked **[C]** was read off the committed generated C in `.lake/build/ir`, every claim marked
**[S]** off the Lean source, and everything else is inference and is labelled as such.

## The one-line summary

An `E`/`T` argument must be a **closed term** today. The matcher is `isMatch : l → Bool` and never
receives a `ρ`, so an argument that reads the background theory is simply out of scope. Fixing it is
cheap and can be made **provably free on the hot path**, but only if the theory is staged out of it —
the naive `ρ → l → Bool` reintroduces exactly the per-edge constant §12.10 spent three rounds removing.

`ltl-bench` does not wait for that fix: it splits the offending actions so every atom is unapplied
(§6.1). That is a re-encoding of three models, not a language change, and it is exact.

## 1. What is blocked, precisely

Three models in `ltl-bench/veil/LtlBench/SuiteAEnabled/` — `ChangRoberts`, `EWD840`,
`SimpleAllocator` — are the only ones whose fairness is *per-instance* rather than per-action, and
all three want to write it directly:

```lean
liveness [clientsWillObtainFair]
  ((□ ◇ ¬ T(stutter))
   ∧ (□ (◇ ¬ E(Return c1) ∨ ◇ T(Return c1)))
   ∧ ((□ ◇ E(Allocate c0)) → (□ ◇ T(Allocate c0))))
  → □ (⌜ resSet.contains r0 (unsatisfy c0) ⌝ → ◇ ⌜ resSet.contains r0 (alloc c0) ⌝)
```

`c0`, `c1` are `immutable individual : client`; `n0 n1 n2 : node` and `one max_node : node` are the
same in the other two. All of them fail to elaborate with "unknown identifier", which is why the
three models carry §6.1's split instead.

**The rule.** An argument works iff it is closed. `DiningPhilosophers` writes `E(loop (0:Phil))` and
compiles, because `abbrev Phil := Fin NP` is a plain Lean abbrev, not a Veil `type` — the module is
monomorphic in it and `(0 : Phil)` is a closed term. Anything theory-derived fails: an
`immutable individual`, an `immutable function` application, a `theory ghost`.

## 2. Why — and why the obvious explanation is wrong

`SuiteAEnabled/Main.lean` blames `derivedFrom` / `LivenessAtomSpec.assertionName?`: an individual
referenced only inside an `E(…)` "never becomes a parameter of the generated definition". That is a
red herring. **[S]** `Module.mkDerivedDefinitionsParamsMapFn` (`Module/Util/Basic.lean:388`) uses
`derivedFrom` only to collect `extraParams`, which are the extracted `Decidable` instances. It has no
say over which values are in scope.

The actual mechanism is scope, in two steps.

**[S]** `immutable individual c0 : client` becomes a **field of the `Theory` structure**
(`Module/Util/StateTheory.lean:61`, `Module.immutableComponents`). It is not a module parameter and
therefore not a binder of anything.

**[S]** `Module.generateLivenessDefinitions` (`Module/Elaborators.lean:680-728`) emits

```lean
def clientsWillObtainFair <mod.parameters ++ extraParams ++ enumParams> :
    LivenessProperty ρ σ (Label …) :=
  { atoms := [ …, .taken `T(Allocate) (fun lbl => decide (lbl = Label.Allocate c0)), … ], φ := … }
```

from `mkIsMatch` at `Elaborators.lean:687-697`. The binders are sorts, `instantiate` instances, ρ and σ.
There is no `th : ρ` anywhere, so `c0` resolves to nothing.

`⌜ … ⌝` atoms do not have this problem because they go the long way round: `defineAssertion` →
`Module.mkVeilTerm` → `withTheory` / `withTheoryAndState`
(`Module/Util/Assertions.lean:186-225`), which wraps the user term in `Theory.casesOn` and so puts
every theory field in scope by name. The `E`/`T` branch added at `Elaborators.lean:624-631` skips that
machinery entirely — deliberately, since an unapplied atom needs nothing from the state.

So: **`enabled`/`taken` are the only atoms in the language that cannot see the theory.**

## 3. Where the matcher is actually called

Two sites, both hot, both **[S]** in `LivenessMC/Interface.lean`:

| site | frequency | per call |
|---|---|---|
| `LivenessProperty.stateLabel` (`:42`) | once per product state | `enabledHere.any isMatch` per `.enabled` atom |
| `LivenessProperty.edgeLabel` (`:54`) | **once per successor** | fold over *all* atoms, `isMatch lbl` per `.taken` |

`LTLLib.TGBAProduct.expand` calls `sysLabel p.1` and `sysSucc p.1` back-to-back, once per product state
(§9), so `stateLabel` is per state. `edgeLabel` is reached through `sysStepsLabelled`'s `some` branch
and runs per successful step.

**[C]** `Interface.c`, `edgeLabel___redArg`, is one `lean_alloc_closure` plus a `List.foldl` over the
whole atom list, per edge:

```c
x_5 = lean_alloc_closure(edgeLabel___redArg___lam__0, 4, 2);
x_7 = l_List_foldl___redArg(x_5, x_6, x_3);          // x_3 = p.atoms
```
```c
  if (lean_obj_tag(x_4) == 2) {                      // .taken
    x_11 = lean_apply_1(x_10, x_1);                  // isMatch lbl
    ... insertIfNew ...
```

That is the budget the fix has to live inside.

## 4. The trap: why `isMatch : ρ → l → Bool` is the wrong fix

**[C]** Today's applied matcher compiles to the best possible thing, because the target is closed.
`SuiteAEnabled/DiningPhilosophers.c`:

```c
LEAN_EXPORT uint8_t ..._nobodyStarvesFair___redArg___lam__1(lean_object* x_1) {
  x_2 = ..._lam__1___closed__0;                      // `Label.loop 0`, lifted to a static
  x_3 = ..._instDecidableEqLabel_decEq___redArg(x_1, x_2);
  return x_3; }
```

`Label.Allocate th.c0` is not closed, so it cannot be lifted. Widen the field to `ρ → l → Bool` and the
body becomes a `ctor_get` + `alloc_ctor` + `dec_ref` **per edge per atom**.

Nor can you hoist it with a `let`. Lean's LCNF maximizes a declaration's arity: `fun th => let t := …;
fun lbl => …` compiles to arity 2 with the `let` inside the body, so `t` is recomputed on every full
application. This is the same eta-expansion that bit `edgeMarks` (`Product.lean`, the PERF comment) and
`edgeLabelOf` (§12.10c), and it is why `edgeLabelling` returns an `Option` rather than a function.

**The invariant to respect: a staged value must have a non-function type.** Then the first application
is saturating and cannot be duplicated into the per-call path.

## 5. The recommended fix

Two extra constructors, carrying the target as *data*:

```lean
inductive LivenessAtom (ρ σ l : Type) where
  | state     (p : SafetyProperty ρ σ)
  | enabled   (name : Name) (isMatch : l → Bool)   -- resolved; unchanged
  | taken     (name : Name) (isMatch : l → Bool)   -- resolved; unchanged
  | enabledOf (name : Name) (target : ρ → l)       -- new: pre-resolution
  | takenOf   (name : Name) (target : ρ → l)       -- new

@[inline] def eqLabel [BEq l] (t : l) : l → Bool := fun lbl => lbl == t

def LivenessAtom.forTheory [BEq l] (th : ρ) : LivenessAtom ρ σ l → LivenessAtom ρ σ l
  | .enabledOf n mk => .enabled n (eqLabel (mk th))   -- `mk th : l`, saturating: runs once
  | .takenOf   n mk => .taken   n (eqLabel (mk th))
  | a => a
```

`LivenessProperty.forTheory` maps that over `atoms`, guarded by an `any` so a property with no `*Of`
atom is returned unchanged (same object, no list rebuild). `edgeLabelling` and `sysLabelOf` resolve once
and hand a fully-resolved property downstream.

### Why this is neutral by construction

- `stateLabel` and `edgeLabel` **do not change**. The `.enabled`/`.taken` branches are byte-identical;
  the two new tags land in the existing catch-all. A `lean_obj_tag` switch over 5 cases costs what one
  over 3 costs.
- New work is one `List.map` and one `Label` allocation per applied atom, **once per check**.
- Every model that works today hits the guard and pays nothing at all.
- `.taken`'s payload becomes `eqLabel t` (a closure over a heap `Label`) rather than
  `decide (· = <static>)`. Both are `lean_apply_1` + `decEq`; one extra pointer hop, once per edge, on
  the atoms that were previously impossible to write.

### Elaborator side

Replace `mkIsMatch`'s applied branch (`Elaborators.lean:695-697`) with a theory-bound target:

```lean
mod.withTheoryAndStateTermTemplate [(.theory, th, true)] (some labelT)
  (fun _ _ => `($(mkIdent (labelTypeName ++ actionName)) $args*))
```

wrapped in `fun (th : ρ) => …`. Same template `withTheory` uses; it already takes a `motiveType`, so a
non-`Prop` result is supported. Emit the `*Of` form for **every** applied atom, closed arguments
included — one closure allocation per check is not worth a "does this term mention the theory?" test.

### Scope of the change

| file | what |
|---|---|
| `LivenessMC/Interface.lean` | 2 constructors, `forTheory`, `name`/`isEdgeAtom`/`has*Atoms` cases |
| `LivenessMC/LivenessMC.lean` | `edgeLabelling` gains `th`; `let p := p.forTheory th` in each `check*` |
| `Module/Representation.lean` | `LivenessAtomSpec` unchanged in shape; carries the same args |
| `Module/Elaborators.lean` | `mkIsMatch` applied branch, ~15 lines |
| `ltl-bench/veil/LtlBench/Harness.lean:157` | one line, `edgeLabelling th p` |

One lemma: `(p.forTheory th).isEdgeAtom = p.isEdgeAtom` and `(p.forTheory th).φ = p.φ`, so `checkFair`'s
`hprune : pruneRegionsAvoidEdgeAtoms p = true` still licenses the route. `List.getElem?_map` plus a tag
case split. `isEdgeAtom_of_mem_edgeLabel` and `steps_edgeAtom` are untouched.

**Make the Harness change a compile error, not a silent resolution.** An unresolved `.takenOf` reaching
`edgeLabel` would read `false` and quietly produce a wrong verdict. §12.11 is the standing lesson about
benchmarks measuring the wrong thing; a type error is cheaper than another round of that.

## 6. What shipped in `ltl-bench`, and two fixes that would retire it

### 6.1 Shipped: split the action, one nullary copy per instantiation

`ltl-bench/veil/LtlBench/SuiteAEnabled/{SimpleAllocator,ChangRoberts,EWD840}.lean` bake the
instantiation into the action, so the label is nullary and the atom needs no argument:

```lean
action Allocate_c0 {
  let c := c0          -- the only new line; the body below is verbatim
  …
}
```

`let c := c0` elaborates because **an action body is elaborated with the theory in scope** — that is
the whole asymmetry of §2. Only the `E`/`T` *argument* position lacks it. A leading `let` also keeps
any `require` at the action's outermost level, so guard extraction is unaffected (`Request` in
`SimpleAllocator` already had `let S :| …` before its `require`s).

Counts, which is what makes this a re-encoding rather than a different model:

| model | split | labels before | labels after |
|---|---|---:|---:|
| `SimpleAllocator` | `Allocate`, `Return` over `client = Fin 2` | 7 | 7 |
| `ChangRoberts` | `send` (3), `relay` (3×3) over `node = Fin 3` | 13 | 13 |
| `EWD840` | `PassToken` over `node = Fin 3` | 17 | 17 |

Each split is **exhaustive** over its sort, so the label sets are in bijection: same states, same
edges, same verdicts. Three things to keep in mind:

- **Replace, never add.** Leaving the parameterized action alongside the copies doubles every one of
  its transitions.
- **Keep the copies that can never fire.** `EWD840`'s `PassToken_zero` is disabled by its own
  `require i ≠ seq.zero`, but dropping it would shrink `Enumeration.allValues Label` and so the
  per-state `tr` enumeration — which is exactly the cost the suite measures.
- **The generated code does differ from the `SuiteA` twin**: N specialized bodies rather than one
  parameterized one. The transition systems are isomorphic, but a few percent of timing delta on
  those three rows is attributable to the encoding, not to `E`/`T`. Say so when reporting them.

Only actions named by an *applied* atom need splitting. `SimpleAllocator`'s `Request` and `EWD840`'s
`SendMsg`/`Deactivate` keep their parameters — no atom names them, or only a bare `T(SendMsg)` does.

### 6.2 Possible fix A: `param`, plus a conditional `deriving` on `Instantiation`

`Module/Syntax.lean:117-144`: `param` values are *universal parameters of `State`, `Theory` and
`Label`* — binders of the generated liveness definition — so `param c0 : client` puts `c0` in scope
and `E(Allocate c0)` elaborates as written.

**It does not work today.** `#gen_state` reports ``failed to generate `Inhabited` instance for
`Instantiation` ``. `Module.mkInstantiationStructure` emits a **closed** structure:

```lean
structure Instantiation where
  client : Type ; … ; c0 : client ; c1 : client   deriving Inhabited, Repr
```

A bare `Type` field is fine — core has `instance : Inhabited (Sort u) := ⟨PUnit⟩`
(`Init/Prelude.lean:815`). What fails is `c0 : client`: the handler asks for `Inhabited client` with
`client` an **fvar, a field of the structure being defined**. Instance binders attach to
*parameters*, so there is no position to supply one — "just add `Repr client` somewhere" has no
answer. (`param m : Fin (n+1)` survives because `Inhabited (Fin (n+1))` is a genuine instance for
every `n`; `Inhabited client` for an opaque fvar is not. `State` and `Theory` elaborate fine — they
are emitted first and no field of theirs is sort-typed.)

*The fix, written and then reverted* (the benchmark run did not want a frontend change mid-sweep):
in `Module.mkInstantiationStructure` (`Module/Util/Assemble.lean`), drop the `deriving` clause
exactly when a `param`'s type mentions a sort.

```lean
private partial def syntaxMentionsAny (names : Std.HashSet Name) : Syntax → Bool
  | .ident _ _ n _ => names.contains n || names.contains n.eraseMacroScopes
  | .node _ _ args => args.any (syntaxMentionsAny names)
  | _ => false
…
  let sortNames : Std.HashSet Name := Std.HashSet.ofArray <| mod.parameters.filterMap fun p =>
    match p.kind with | .sort _ => some p.name | _ => none
  let dependsOnSort := mod.parameters.any fun p =>
    match p.kind with | .userParameter => syntaxMentionsAny sortNames p.type.raw | _ => false
  if dependsOnSort then `(structure $instantiationType where $[$fields]*)
  else `(structure $instantiationType where $[$fields]* deriving $[$instances:ident],*)
```

Safe because **nothing consumes either instance**: `Instantiation` occurs in exactly three places
tree-wide, all type ascriptions on a record literal or an `Expr` (`Assemble.lean:208`,
`Elaborators.lean:917`, `:954`). The derived `Repr` would be useless anyway — the `Type` fields are
erased at runtime, which is why `VeilCTI.sortInstInfo` carries the sort names separately
(`Core/UI/Verifier/InductionCounterexample.lean`). Every module in the tree keeps both instances: no
existing `param` is sort-typed.

Pure elaboration, nothing on the model-checking path, so no performance risk — but `Assemble.lean` is
deep in the frontend, so it rebuilds all of Veil and everything downstream.

Even with this, `param` is the *lesser* fix: it moves the value from the `Theory` into the
`Instantiation`, lengthens every call site, and still cannot express `E(relay n0 _)`. §5 is the one
that makes the language right.

### 6.3 Rejected: concretize the sort

As `DiningPhilosophers` does (`abbrev Node := Fin 3`). Certain to work, but it makes the model
monomorphic where the `SuiteA` twin is polymorphic-then-specialized, so the rows stop being
comparable — which defeats the purpose of the parallel suite.

## 7. Three findings that matter more than the argument question

### 7.1 `sysLabelOf` is eta-expanded: `hasEnabledAtoms` runs per state — live regression

**[S]** `LivenessMC.lean:244-249` puts the `if p.hasEnabledAtoms` above `fun st`. **[C]** the compiler
pulled `st` in anyway:

```c
LEAN_EXPORT lean_object* ..._sysLabelOf___redArg(x_1, ..., x_7) {   // x_6 = th, x_7 = st
  x_8 = ..._LivenessProperty_hasEnabledAtoms___redArg(x_5);         // scanned per state
```

So every property — including ones with no `E` at all — scans the atom list once per product state.
This is exactly the bug §12.10(c) documented for `edgeLabelOf` and fixed by reifying the decision as an
`Option`; `sysLabelOf` never got the same treatment. **[C]** the fix is known to work: `edgeLabelling`
compiles to `edgeLabelling___redArg(lean_object* x_1)` — arity 1, not eta-expanded, because it returns
an `Option` rather than a function.

Same shape of fix, and it is a win rather than a cost.

### 7.2 `E(…)` doubles the dominant Veil callback

**[S]** `enabledLabels` (`LivenessMC.lean:183`) runs a second full `sys.tr th st`. `tr` is
`List.flatMap` over `Enumeration.allValues Label`, executing the extracted action for every label
(`Action/Extract.lean`, `assembleEnumerableTransitionSystem`) — the measured dominant Veil-side cost.
`TGBAProduct.expand` calls `sysLabel` then `sysSucc` back-to-back on the same state, so a **one-entry
memo on `tr` keyed by `st` collapses it exactly**. §11's "Cost" section proposed this; it is still open.

Consequence for the `SuiteAEnabled` sweep: rows whose properties mention `E(…)` should show roughly 2×
the Veil-callback share of their `T`-only siblings, and this is **not** attributable to the atom
encoding being wrong. Their `SuiteA` twins encode ENABLED as a hand-written state predicate, which is
cheap. Do not misread the difference as a defect in `E`.

### 7.3 `edgeLabel` is still a per-successor fold

§11 specified a `HashMap l (HashSet Nat)` table over `Enumeration.allValues`; §12.10 records it as still
open. It is cheap now: `tr` already walks `allValues Label` once per state, so building the table once
per check costs strictly less than a single `tr` call, and the `Veil.Enumeration l` instance is already
required at `enumerableTransitionSystem`. This replaces the per-edge closure allocation and atom-list
fold of §3 with one lookup.

Tail risk worth stating: |Label| is the number of action instances, so a model with a large label space
and a small reachable state space would pay for the table without amortizing it. Every model in the
suites is far from that, but the guard is easy (build lazily, or only above a size threshold).

## 8. Partial instantiation, as a follow-on

`SuiteAEnabled/ChangRoberts.lean` hand-unrolls `∃o, relay(self,o)` into
`T(relay n0 n0) ∨ T(relay n0 n1) ∨ T(relay n0 n2)` because `E`/`T` take either zero arguments or all of
them. `T(relay n0 _)` would collapse 8-atom disjunctions to 2 per conjunct, and atom count drives
tableau size — so this is plausibly a **larger** speedup than anything in §7.

It does not fit `target : ρ → l`. The representation that does, and that keeps §4's invariant, is
`targets : ρ → Array l` (or a `HashSet l`) — the prefix expanded against `Enumeration.allValues` at
resolution time, resolving to a membership test. That also composes with §7.3's table. Worth shaping the
constructor for this now even if the feature waits.

## 9. Test coverage

`VeilTest/ActionAtoms.lean` has 22 cases and **not one applied `E`/`T`**. The applied path is exercised
only by `DiningPhilosophers` in `ltl-bench`, and only with a closed literal. Anything landing here
should add applied cases — both closed and theory-derived — to that file first.

## 10. Suggested order

0. §6.1's split is in the tree and unblocks the sweep. Nothing below is on the benchmark's critical
   path; all of it is Veil work to do afterwards.
1. Fix `sysLabelOf`'s eta-expansion (§7.1). Independent, free, and already costing every route — the
   only item here that is a regression rather than a feature.
2. Then §5, which retires the split and is perf-neutral by construction. §6.2 is the cheaper
   half-measure if §5 is too much at once.
3. §7.2 and §7.3 are the two standing wins on the `E`/`T` path; neither is blocked by the others.
4. §8 (partial instantiation) would shrink `ChangRoberts`' 8-atom disjunctions to 2 and is plausibly
   the largest win of the lot — but it needs §5's staging first.
