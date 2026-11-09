# State visualizations

A Veil module can choose a diagram for its states. Register a Lean widget with
`#set_visualizer MyStateView` inside the module, before the commands that should use
it. The same widget then appears on satisfying traces, induction counterexamples,
explicit model checker traces, and temporal counterexamples. It also works for
`unsat trace` counterexamples and `#simulate` traces.

```lean
@[widget_module]
meta def MyStateView : ProofWidgets.Component Veil.StateViewProps where
  javascript := include_str "myStateView.js"

-- Inside the Veil module, before running any checks:
-- #set_visualizer MyStateView
```

The JavaScript is a standard [Lean widget](https://github.com/leanprover-community/ProofWidgets4).
Export a React component as the default export (or set the Lean component's
`export` field to a named export). For example, a module with a numeric `counter`
field could use this file:

```js
import { createElement as h } from 'react';

export default function MyStateView({ fields, hiddenFields, children }) {
  if (typeof fields.counter !== 'number' || hiddenFields.includes('counter')) return children;
  return h('meter', { min: 0, max: 10, value: fields.counter, 'aria-label': 'Counter' });
}
```

The component receives:

| Prop | Meaning |
| --- | --- |
| `fields` | The current state's fields, keyed by name. |
| `previous` | The preceding state's fields, when available. An induction counterexample may only contain one state. |
| `theory` | The displayed background theory, including named SMT theory values or the fields supplied by a concrete display instance. |
| `instantiation` | The types and parameter values of the witness as strings, such as `{ node: "Fin 4", limit: "3" }`. The explicit checkers use the supplied instantiation. SMT witnesses use the model and omit term parameters with no assignment. |
| `transition` | The incoming action label, when known. A liveness witness projects states from the product graph without retaining action labels. |
| `showRemovals`, `hiddenFields` | The panel's display settings. |
| `children` | The standard field view. Return it when the widget cannot draw the given state. |

Field and theory values use [Veil's display encoding](../Veil/Util/ValueDisplay.lean),
including tagged sets, maps, records, and constructors. The surrounding panel
owns the trace order, action links, loop markers, and raw results. Readers can
switch back to fields at any time. A missing or failing widget leaves the field
view available.

Veil selects the widget at command elaboration and loads it through the Lean
infoview's widget API. A visualizer is presentation code: it runs only in the
infoview and does not become part of the solver or a compiled checker binary.
The standalone Veil VS Code results panel has no Lean widget session and uses
the standard view.

For concrete checks, define a `meta instance (inst : Instantiation) … :
Veil.StateViewTheory inst` to supply theory fields backed by Lean instances.
Its `fields` method returns a JSON object keyed by field name. Lean resolves
its instance arguments in the scope of the checking command. For example,
Ring supplies `btwn.btw` using the selected `Between inst.node` instance,
matching the key used by SMT witnesses.

[Ring](../Examples/Ivy/Ring.lean) and [DieHard](../Examples/Puzzles/DieHard.lean)
are working examples. Their SVG geometry and theme styles come from the
[thesis visualization branch](https://github.com/verse-lab/veil-dev/tree/claude/custom-state-visualizations-Eb5bR).
