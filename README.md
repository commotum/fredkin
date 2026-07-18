# Conservative Logic in Lean 4

This repository is developing a checked Lean 4 account of the finite,
discrete mathematics in Edward Fredkin and Tommaso Toffoli's 1982 paper
[*Conservative Logic*](fredkin-1982/fredkin-1982.md).

The verified core is intended to cover finite Boolean words, reversible maps,
Hamming-weight preservation, the paper's zero-controlled Fredkin gate,
one-to-one circuit composition, reversible realization with explicit constants
and garbage, inverse circuits, and ancilla restoration. Claims about energy,
entropy, dissipation, noise, or physical realizability do not follow merely
from finite circuit semantics and will not be stated as Lean theorems without a
separate explicit physical model.

The authoritative staged strategy, paper map, correction log, and open issues
are in [`goal-1/0-plan.md`](goal-1/0-plan.md). Work proceeds one stage at a time
under [`goal-1/0-loop.md`](goal-1/0-loop.md).

## Formal project

The Lean project is isolated in `formal/` and pins a matching Lean/mathlib
release pair. To reproduce the build:

```sh
cd formal
lake update
lake exe cache get
lake build ConservativeLogic.Audit.Guardrails
lake build ConservativeLogic.Audit.Finite
lake build ConservativeLogic.Audit.Fredkin
lake build ConservativeLogic.Audit.Circuit
lake build
```

Stages 1 through 4 are complete under Lean/mathlib `v4.32.0`. The public import
`ConservativeLogic` now exports finite Boolean states, Hamming weight and block
additivity, separate reversibility and weight-preservation predicates, bundled
reversible/conservative maps, conservative wire permutations, the unit wire's
identity-on-values semantics with separate one-step delay metadata, and the
paper-convention Fredkin gate. It also exports a balanced feed-forward circuit
grammar with only identity, unit wire, Fredkin, explicit bijective structural
reindexing, exact-width serial composition, and disjoint tensor composition.
Circuit evaluation is a conservative equivalence. A separate static
`PathDelay` relation records individual routes, while `HasLatency` and
`MeetsPaperCombinationalTiming` certify one common unit-wire latency across
every existing boundary path. Structural permutations are zero-delay
meta-level port reindexings, not synthesized routing circuits. The grammar is
not claimed to be the paper's feedback-capable directed-graph model, and its
timing layer is not a tick, trace, transition, stream, or physical-routing
semantics. Explicit
constants, garbage, and initialized auxiliary wires enter next through the
Stage 5 realization interface. The focused audit commands are explicit because
diagnostic leaves are intentionally not imported by the public root.
