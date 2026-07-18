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
lake build
lake build ConservativeLogic.Examples
lake build ConservativeLogic.Audit.Guardrails
lake build ConservativeLogic.Audit.Finite
lake build ConservativeLogic.Audit.Fredkin
lake build ConservativeLogic.Audit.Circuit
lake build ConservativeLogic.Audit.Realization
lake build ConservativeLogic.Audit.Simulation
lake build ConservativeLogic.Audit.Inverse
lake build ConservativeLogic.Audit.Uncompute
lake build ConservativeLogic.Audit.Completeness
lake build ConservativeLogic.Sequential
lake build ConservativeLogic.Audit.Sequential
lake build ConservativeLogic.Billiard
lake build ConservativeLogic.Audit.Billiard
lake build ConservativeLogic.Audit.Axioms
python3 ConservativeLogic/Audit/completeness_groups.py
```

The default build is deliberately first: it compiles only the finite public
root.  The later commands explicitly opt into examples, diagnostic audits,
registered semantics, and sampled billiard geometry.

## Entry points and theorem correspondence

| Import or document | Purpose |
|---|---|
| `ConservativeLogic` | Stable finite Boolean, circuit, realization, inverse, uncompute, and clean-completeness API |
| `ConservativeLogic.Examples` | Small consumer examples using only the stable finite root |
| `ConservativeLogic.Sequential` | Opt-in synchronous state, trace, delayed-feedback, and paper-example semantics |
| `ConservativeLogic.Billiard` | Opt-in constrained collision interfaces and sampled Figure 14 geometry |
| `ConservativeLogic.Audit.Axioms` | Non-public aggregate `#print axioms` target for the main theorem families |
| [`goal-1/0-plan.md`](goal-1/0-plan.md) | Canonical paper-claim map, correction statuses, exact declarations, and unresolved/out-of-model inventory |

Representative theorem families include `hammingWeight_append` and
`WeightPreserving.zeroCount`; `PaperFredkin.table`; `Circuit.eval_*`,
`Circuit.wireOfLength_hasLatency`, and the path-timing predicates;
`Realization.Realizes` and `Simulation.SourceCircuit.compile_realizes`;
`Circuit.inverse_eval` and `Ancilla.compute_copy_uncompute_spec`;
`fredkin_complete_conservative` and `middleLayerSwap_not_circuit`; the opt-in
`Sequential.ConservativeMachine` trace/flux/closure results; and the opt-in
`Billiard.Interaction.equiv`, legal scattering, sampled-clearance, and
`Billiard.Figure14.output_refines_collision` results.  The canonical map gives
the fully qualified declarations and records every corrected, disproved, open,
or out-of-model paper claim.

Stages 1 through 12 are complete under Lean/mathlib `v4.32.0`. The public import
`ConservativeLogic` now exports finite Boolean states, Hamming weight and block
additivity, the derived false-wire count `N₀ = width - N₁`, separate
reversibility and weight-preservation predicates, bundled
reversible/conservative maps, conservative wire permutations, the unit wire's
identity-on-values semantics with separate one-step delay metadata, and the
paper-convention Fredkin gate. It also exports a balanced feed-forward circuit
grammar with only identity, unit wire, Fredkin, explicit bijective structural
reindexing, exact-width serial composition, and disjoint tensor composition.
Circuit evaluation is a conservative equivalence. A separate static
`PathDelay` relation records individual routes, while `HasLatency` and
`MeetsPaperCombinationalTiming` certify one common unit-wire latency across
every existing boundary path. Structural permutations are zero-delay
meta-level port reindexings, not synthesized routing circuits. The grammar can
also construct a one-bit wire of every finite length, with static identity
semantics and exact unit-wire latency.  It is not claimed to be the paper's
feedback-capable directed-graph model, and its
timing layer is not a tick, trace, transition, stream, or physical-routing
semantics.

Stage 5 adds an exhaustive five-block realization layout with fixed source,
returned-clean scratch, argument, result, and explicit garbage. `Realizes`
states equality of the circuit's complete output, and its constraint theorems
derive target/garbage injectivity, target-fiber capacity bounds, and exact
Hamming-weight balance. The public API also includes routed one-Fredkin
realizations of AND, OR, NOT, and constrained FAN-OUT. FAN-OUT consumes source
`(0,1)`, selects `(a,a)`, and retains `¬a` as garbage; it is not an
unrestricted copy gate.

Stage 6 adds an indexed conventional source language with explicit fixed block
constants, discard, AND, OR, NOT, FAN-OUT, bijective port permutation, serial
composition, and disjoint tensor. A total structural compiler translates every
such finite acyclic term to the existing target grammar. Its theorems state
the exact fixed source, complete argument-dependent garbage, zero scratch, full
initialized-slice equality, exact Fredkin count, and abstract latency zero.
Serial composition carries earlier garbage unchanged; tensor uses proved
four-block permutations and never duplicates an input implicitly. Because the
target still includes zero-delay structural `WirePerm` nodes, this is a
Fredkin-plus-reindexing construction for the named grammar—not a pure physical
routing theorem, a proof that every Boolean function has a source term, or the
paper's sequential universality claim.

The public Figure 7 reconstruction separately checks the complete map
`(0,0,0,A₀,A₁,X) ↦ (Y₀,Y₁,Y₂,Y₃,A₁,A₀)` with three Fredkins and seven unit
wires. It constructs a delay-two route for every distinguished
argument/result pair and proves that every grammar-induced route between those
ports has delay two. A zero-delay source/result counterroute then proves that
the full six-wire boundary does not satisfy the later global equal-latency
criterion.

Stage 7 adds a total structural inverse for every balanced `Circuit`. It leaves
identity, unit wire, and the paper Fredkin constructor unchanged, inverts
active structural permutations, reverses serial order, and preserves tensor
block order. `inverse_eval` identifies the complete static boundary map with
`Conservative.inverse`; double inversion and both semantic cancellation
directions are proved. `PathDelay.inverse` and `pathDelay_inverse_iff` reverse
route endpoints without changing unit-wire count, so common-latency
certificates are preserved. A latency-`L` forward/inverse round trip has
latency `L + L`; the unit-wire round trip evaluates to identity but has latency
two. These are feed-forward expression theorems, not inversion of Figure 19's
feedback graph, oriented `t ↦ -t` execution, or physical time-reversal
invariance.

Stage 8 adds an explicit `2n`-wire result register and one real routed Fredkin
spy per result bit. Canonical `(a,0,1)` is actively mapped to the paper gate's
physical `(a,1,0)` order, so the proved vector equation is
`(x,0ⁿ,1ⁿ) ↦ (x,x,¬x)`. Given a concrete full-state `Realizes` witness, the
public compute-copy-uncompute circuit restores the exact packed scratch,
source, and argument register and returns `(f(x),¬f(x))`; transient midpoint
garbage is uncomputed rather than hidden. The construction is globally
reversible and Hamming-weight preserving, and its exact Fredkin count is twice
the supplied circuit count plus the result width. The unpadded timing theorem
is deliberately limited to zero-latency supplied circuits: a checked unit-wire
example has both delay-two and delay-zero boundary paths. No arbitrary-function
synthesis, all-zero-scratch conversion, delay padding, feedback, traces,
physical routing, or thermodynamic conclusion follows from this stage.

Stage 9 separates semantic completeness from fixed-basis synthesis.  A
classical Hamming-layer construction supplies Figure 25's suppressed total
conservative extension and proves that direct same-register realization by an
arbitrary conservative gate is exactly bijectivity plus Hamming-weight
preservation.  Independently, an explicit pattern-controlled last-pair swap is
compiled to paper Fredkin gates plus structural reindexing, uses a visible
mixed clean ancillary prefix, returns that prefix exactly, excludes every
`unitWire`, and has zero path latency.  Structural conjugation realizes every
transposition between states
that differ by exchanging one true and one false coordinate; Johnson-graph
connectivity and finite permutation-group closure then give
`fredkin_complete_conservative` for every finite conservative
permutation.  The witness exposes its selected finite ancilla width and exact
initialization, but the classical existential group proof is not an executable
compiler and does not claim a global linear or optimal width bound.  Finally,
every width-four circuit is proved even as a
permutation of all states, while the conservative swap `1100 ↔ 1010` is odd,
so the same-width/no-ancilla reading is formally false.  Structural wire
reindexing remains an abstract routing convention, not a synthesized physical
network; all-zero scratch, the paper's asymptotic scratch assertions, feedback,
and sequential universality remain unresolved in the finite public API.

Stage 10 adds the separate opt-in import `ConservativeLogic.Sequential`.
It defines total synchronous machines with explicit initial state, canonical
causal traces, unique trace equations, and strict input-prefix dependence.
An open conservative machine is one complete permutation
`memory ++ input ↔ nextMemory ++ output`; checked one-tick and finite-prefix
theorems state boundary flux rather than falsely preserving open memory weight
alone.  Register-separated closure stores every former output until the next
tick, preserves complete closed-state Hamming weight at every finite time, and
has an explicit reversible finite iterate.  Complete output histories plus
terminal memory retrodict finite open runs, a semantic result deliberately
kept distinct from literal graph reversal and physical time reversal.

The circuit-backed sequential bridge accepts only a feed-forward core proved
to have zero path latency, because static `Circuit.eval .unitWire` does not
execute stored state.  A structural-swap delay cell proves the exact one-tick
offset.  The Figure 8 reconstruction uses one paper Fredkin and explicit
output routing, exposes arbitrary initialization, visible `Q`, and the `?`
garbage wire, and proves its full tick and characteristic trace.  Figure 9's
printed accumulator recurrence is checked separately and its complete tick is
proved bijective but nonconservative.  Figure 11 is reconstructed as an actual
six-wire, two-Fredkin zero-latency core with three explicit register bits; its
per-tick `(x,0,1)` source, all three outputs, pipeline initialization, and
printed `y(t+2)=y(t+1) xor x(t)` recurrence are checked.  Figure 10's
factor-five slowdown, time-multiplexing schedule, the general sequential
compiler, literal Figure 19 graph inversion, NAND-comparable complexity, and
physical conclusions remain documented rather than inferred.  The sequential
umbrella is intentionally not imported by `ConservativeLogic` or
`ConservativeLogic.API`.

Stage 11 adds the separate opt-in import `ConservativeLogic.Billiard`.  The
paper's interaction and switch tables are unequal-width maps, so each is an
equivalence from two input bits onto an explicit four-state valid-output
subtype—not an ordinary balanced `Conservative` gate.  Their selected inverses,
ball-count preservation, valid cardinalities, raw-interface cardinality
obstructions, and increases in vacant rails are checked.  A four-channel local
collision exchanges only the straight pair `0110` and deflected pair `1001`;
its total identity behavior on other masks is labeled an algebraic completion,
while its selected legal subtype excludes unselected multi-ball events.  The
initialized `(0,q,p,0)` slice refines the complete interaction output.

Finite products of legal collision sites provide deterministic,
involutive, count-preserving simultaneous scattering only for independent
owned channels.  Directed routes use a rotated integer lattice, with explicit
sampled mirror turns, a same-endpoint-position detour adding four ticks, and
global-time crossover predicates.  The detour has different boundary
directions and is therefore not a general drop-in wire-delay gadget.
The naked crossing conflicts when simultaneous.  A one-tick stagger avoids an
equal sampled center but fails the radius-derived squared-distance threshold;
a two-tick stagger satisfies that sampled threshold.  Figure 14 has a complete
coordinate trace: every active ball makes four unit lattice moves, all integral
frames preserve ball count and meet the sampled squared-distance threshold,
the right-angle turn
occurs exactly on input `11`, and the full final frame observes
`(pq,!p q,p !q,pq)`.  These are discrete sampled certificates, not continuous
hard-ball, swept-clearance, elastic, mirror-mechanics, or physical-energy
theorems.

Figures 15 and 17 provide no coordinates or numerical latency, while Figure
18 says steering/timing mirrors and unit wires are not explicitly indicated
and leaves its bridge/trivial crossover obligations unproved.  Accordingly,
the library does not claim Figure 17/18 physical refinement, arbitrary mirror delay, a general
billiard layout compiler, P8 packing bounds, physical time reversal, or any
thermodynamic conclusion.  The billiard umbrella is not imported by the finite
or sequential APIs.

Stage 12 stabilizes declaration ownership and namespaces, adds the derived
`N₀` view and arbitrary finite one-bit wire chains requested by the paper map,
and supplies a finite-root consumer plus an aggregate axiom audit.  These are
API and correspondence repairs; they add no physical routing, continuous
mechanics, hidden resource, or stronger universality claim.

The focused audit commands are explicit because diagnostic leaves are
intentionally not imported by the public root.
