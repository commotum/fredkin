# 6-SIMULATION

## Current Facts

- Stage 5 is complete at clean synchronized commit `e65f939`. A cached default
  `lake build` succeeds with 773 jobs. No Stage 6 `Simulation` source,
  translation, example, or audit module exists at this baseline.
- `Circuit n` remains a balanced, feed-forward, one-to-one target grammar. Its
  only value-processing constructor is the paper Fredkin; `permute` is an
  explicit bijective structural reindexing. There is no unequal-width gate,
  semantic-function injection, implicit fan-out, weakening, feedback, or
  sequential state.
- Stage 5 `Layout` and `Realizes` account for complete initialized-slice
  boundaries. The stable AND/OR/NOT/FAN-OUT witnesses are actual `Circuit 3`
  terms with exact source and garbage functions; constrained FAN-OUT consumes
  `(0,1)` and returns `(a,a)` plus `¬a`.
- Section 4 replaces conventional AND, OR, NOT, and FAN-OUT elements one for
  one by Section 3 conservative realizations. It requires external constants
  and garbage sinks, calls the result a general existence proof, and explicitly
  disclaims optimization of gate count, delay stages, or source/sink lines.
- The paper states Section 4 for sequential networks and informally discusses
  delay elements, slowdown, streams, and time multiplexing. The current Lean
  library has no transition/stream/feedback semantics, so Stage 6 can verify
  only a corrected finite feed-forward fragment; the sequential claim remains
  Stage 10.
- Figure 7 is a three-Fredkin, three-zero-source 1-to-4 demultiplexer with
  external arguments `(A₀,A₁,X)`, binary-indexed selected outputs
  `(Y₀,Y₁,Y₂,Y₃)`, and sink `(A₁,A₀)`. Its gates are
  `F(A₁,X,0)`, `F(A₀,0,A₁∧X)`, and
  `F(A₀,0,¬A₁∧X)`. The seven closed-triangle unit wires give
  latency two from arguments to results, but complete-boundary path delays
  vary, so the paper correctly calls the drawing formally sequential and does
  not establish its later global combinational criterion.

## Updated Assumptions

- Use an explicitly indexed conventional source grammar
  `SourceCircuit inputWidth outputWidth`. Its primitive syntax should include a
  fixed block constant `BitState k : 0 → k`, explicit block discard `k → 0`,
  AND, OR, NOT, explicit FAN-OUT,
  bijective structural permutation, exact serial composition, and disjoint
  tensor. There is no generic function constructor. `tensor c c` receives two
  disjoint input blocks; reusing one input requires a `fanout` node.
- Include constant and discard nodes rather than assuming Cartesian structural
  rules. Translation turns a source constant into an explicitly initialized
  target source wire, and turns a source discard into explicit target garbage.
  Width-indexed blocks are only a finite shorthand for tensoring one-wire
  nodes: the constant payload is fixed data, not an argument-dependent function
  or arbitrary semantic gate.
- Exclude source delays, feedback, registers, traces, streams, and state. A
  delay node must not be represented by source identity, and no Stage 6 theorem
  may claim the paper's sequential universality, slowdown, or time-multiplexing
  conclusions.
- Define recursively exact `sourceWidth` and `garbageWidth` costs for the
  selected construction. Primitive costs follow the Stage 5 layouts. For
  serial composition, append both source blocks and retain downstream garbage
  followed by upstream garbage. For tensor, use disjoint source and garbage
  blocks. Prove the resulting width balance structurally rather than hiding it
  in an existential.
- Translation may use named active block `WirePerm` values to move contiguous
  source/argument/result/garbage blocks to the next subcircuit. Those
  permutations must be ordinary wire-index bijections with application laws;
  they may not contain arbitrary state equivalences or hide ancillas.
- Build a constructive compilation function and prove its complete `Realizes`
  theorem by structural induction. No recursive case may project away earlier
  garbage, feed argument-dependent garbage back as a constant, or duplicate a
  result wire without an explicit translated FAN-OUT node.
- Count the compiled paper Fredkin constructors exactly if a small structural
  cost function remains proof-friendly. Structural permutations, identities,
  constants, and discards are not Fredkin gates; no physical routing cost is
  inferred for meta-level permutations.
- Since every compiled target term contains only zero-delay Fredkin,
  structural identity, and structural permutation nodes, test a static
  `Circuit.HasLatency ... 0` theorem. This is only the Stage 4 abstract path
  metric and not a routed-wire or sequential timing result.
- Reconstruct Figure 7 independently as an exact complete six-wire
  realization, not merely as a result-only truth table. Use binary address
  order `A₁A₀`, sink order `(A₁,A₀)`, and the checked distinction
  between its latency-two argument/result interface and nonuniform complete
  boundary timing.

The checked complete Figure 7 initialized slice is

```text
(0,0,0,A₀,A₁,X) ↦ (Y₀,Y₁,Y₂,Y₃,A₁,A₀)
```

where `Y₀ = ¬A₀ ∧ ¬A₁ ∧ X`, `Y₁ = A₀ ∧ ¬A₁ ∧ X`,
`Y₂ = ¬A₀ ∧ A₁ ∧ X`, and `Y₃ = A₀ ∧ A₁ ∧ X`.  This
ordering yields the eight complete regressions
`000↦0000|00`, `001↦1000|00`, `010↦0000|10`,
`011↦0010|10`, `100↦0000|01`, `101↦0100|01`,
`110↦0000|11`, and `111↦0001|11` when rows are written as
`A₀A₁X ↦ Y₀Y₁Y₂Y₃ | A₁A₀`.

## Big Picture Objective

Prove a finite, constructive replacement theorem for an explicitly defined
ordinary feed-forward Boolean circuit language. Every conventional constant,
discard, nonlinear gate, and FAN-OUT node must translate to an actual Stage 4
Fredkin circuit with recursively computed source and garbage blocks, exact
full-state semantics, and only the resource/timing claims supported by the
construction.

## Detailed Implementation Plan

- Add `ConservativeLogic.Simulation.Source` with:

  ```text
  Simulation.SourceCircuit
  SourceCircuit.eval
  SourceCircuit.logicGateCount
  ```

  The constructors and equations must make constant introduction, discard, and
  FAN-OUT visible and preserve input/output widths through serial/tensor terms.
- Add `ConservativeLogic.Simulation.Fredkin` with explicit block-reindexing
  helpers and recursively computed construction data:

  ```text
  SourceCircuit.sourceWidth
  SourceCircuit.garbageWidth
  SourceCircuit.sourceState
  SourceCircuit.garbage
  SourceCircuit.simulationLayout
  SourceCircuit.compile
  SourceCircuit.source_garbage_balance
  SourceCircuit.compile_realizes
  Circuit.fredkinCount
  SourceCircuit.compile_fredkinCount
  SourceCircuit.compile_hasLatency_zero
  ```

  Exact names may be adjusted after compile probes, but the public surface must
  retain all information above. Primitive clauses must reuse the Stage 5
  realizations rather than restating an unchecked target equation.
- Add a narrow Figure 7 example leaf, tentatively
  `ConservativeLogic.Simulation.Demultiplexer`, with a complete target,
  address-echo garbage, three-zero source, actual three-Fredkin `Circuit 6`,
  full `Realizes` theorem, complete Boolean regression, Fredkin-count theorem,
  and precisely scoped static timing statement.
- Extend the thin API/root only with stable Stage 6 leaves. Add
  `ConservativeLogic.Audit.Simulation` as a non-public diagnostic.
- Update the README, authoritative plan, paper map, and correction log only
  after the final statements and verification matrix are checked.

## Build Structure

- `Simulation/Source.lean` imports only the narrow state/wire-permutation
  surface needed for source syntax and semantics. It knows nothing about
  Fredkin compilation, realization, timing, or diagnostics.
- `Simulation/Fredkin.lean` imports the source language, Stage 5 primitive
  realizations, and Stage 4 timing only where required. It owns block routing,
  exact construction resources, the compiler, and the induction theorems.
- `Simulation/Demultiplexer.lean` imports the compiler or its narrow target
  dependencies and owns only the Figure 7 reconstruction.
- `Audit/Simulation.lean` imports the public API and remains diagnostic-only.
- `API.lean` and the root remain thin re-exports. Stage 7 inverse syntax,
  Stage 8 uncomputation, Stage 9 arbitrary conservative-map synthesis, Stage 10
  sequential semantics, and physical models are forbidden in this stage.

Focused and adjacent commands:

```text
cd formal
lake build ConservativeLogic.Simulation.Source
lake build ConservativeLogic.Simulation.Fredkin
lake build ConservativeLogic.Simulation.Demultiplexer
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Simulation
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Simulation
```

## Boundary Checks

- Source-language boundary: conventional irreversibility is represented only
  by named source primitives. There is no arbitrary `BitState m → BitState n`
  constructor, implicit Cartesian copy, implicit discard, or hidden constant.
- Target-language boundary: compilation returns an actual `Circuit` built from
  the existing six constructors. It cannot inject the source evaluator or an
  arbitrary reversible/conservative equivalence as a target gate.
- Resource boundary: `sourceWidth`, `sourceState`, `garbageWidth`, and the full
  garbage function are explicit. Scratch remains width zero for this
  replacement construction. Exact Fredkin count excludes structural
  permutations; no gate-depth, routed-wire, source/sink optimality, or
  asymptotic claim is inferred.
- Composition boundary: serial composition must preserve upstream garbage
  untouched while feeding only the selected upstream result to the downstream
  argument. Tensor composition uses disjoint inputs. Every inter-block reorder
  is a bijective `WirePerm` with a checked active-direction equation.
- FAN-OUT boundary: source `fanout` is unequal-width ordinary syntax; its
  compiler clause is the width-three constrained Stage 5 circuit with fixed
  `(0,1)` source and complement garbage. It is never treated as `Circuit 1` or
  a reversible map on the selected result.
- Timing boundary: source syntax has no delay/state. Any latency-zero theorem
  reports only explicit `unitWire` count in the abstract feed-forward target;
  it does not certify the paper's Figure 7 routed delays or Section 4 slowdown.
- Stage boundary: no inverse circuit, compute-copy-uncompute, total conservative
  completion, feedback transition, stream, billiard, entropy, or energy
  declaration may enter the Stage 6 public surface.

## No-Cheating Checks

- Print the exact `SourceCircuit` constructors and guard that an arbitrary
  semantic function, implicit one-to-two coercion, or mismatched serial/tensor
  boundary cannot be constructed.
- Inspect and test every resource recurrence, including width zero, nested
  serial composition, nested tensor, explicit constant, and explicit discard.
- Prove source/garbage width balance by induction and audit its axioms; do not
  use bounded evaluation for the general theorem.
- Test all source primitive evaluation equations and representative composite
  terms. A term that needs the same value twice must visibly contain `fanout`.
- Check active block-permutation direction with asymmetric states and prove
  general append/split application laws used by the compiler.
- Prove the general full-state compiler theorem by induction. Scan the
  definition for projections, existential garbage, `Classical.choose`,
  arbitrary state `Equiv`, duplicated variables standing for physical wires,
  or a source-evaluator fallback.
- Check the exact compiler clause for every source constructor. In particular,
  constant becomes source, discard becomes garbage, and FAN-OUT reuses
  `fredkin_realizes_fanout`.
- Exhaust Figure 7's eight argument rows against the complete packed six-wire
  output, including address echo. Separately inspect the three fixed Fredkin
  occurrences and the declared output ordering.
- Audit every `decide`; allow it only for fixed finite regressions, never the
  structural simulation/resource/timing proofs.
- Run `#print axioms` on source semantics laws, width balance, compiler
  realization, Fredkin count, latency, Figure 7 realization, and principal
  negative audit theorems.
- Scan for source delays disguised as identity, hidden fan-out/discard,
  arbitrary target injection, future-stage declarations, diagnostic imports in
  the public API, broad/internal imports, proof holes, and project axioms.

## Completion Requirements

- The public API exports an indexed finite source language whose conventional
  constants, discard, and FAN-OUT are explicit, with no feedback/delay/state or
  arbitrary semantic-gate constructor.
- A total structural compiler covers every source constructor and returns an
  actual Stage 4 target circuit with exact recursively computed source state,
  garbage function, widths, and zero scratch.
- A general theorem proves `Realizes` for the compiler by structural induction,
  with complete output equality and no discarded intermediate garbage.
- Exact width balance, exact Fredkin count, and only a correctly qualified
  static timing result are proved. Any unsupported gate depth, physical routing,
  source/sink optimality, slowdown, or sequential claim is explicitly absent.
- Source constant, discard, FAN-OUT, serial, tensor, permutation, and width-zero
  cases have representative evaluation/resource regressions. Negative tests
  reject implicit fan-out, hidden weakening, arbitrary semantic injection, and
  ill-typed composition.
- Figure 7 has a complete checked realization with all three zero sources, four
  result wires, address-echo garbage, correct output order, three actual
  Fredkins, and a timing statement no stronger than the formal model supports.
- Focused/public/full and uncontended clean builds, exhaustive fixed examples,
  proof-hole/project-axiom/shortcut scans, main-result axiom audits,
  `git diff --check`, complete diff inspection, and a clean synchronized
  worktree all pass.
- The paper map and correction log replace the paper's informal §4 sequential
  claim only for the proved finite feed-forward source grammar and carry the
  stateful translation, delay normalization, slowdown, streams, and resource
  optimization obligations forward to Stage 10.

## Stage Results

**Stage status: in progress.** Repository/paper facts and the preimplementation
contract are recorded. Lean design probes and the Figure 7 port/order audit are
next; no Stage 6 repository declaration has yet been added.
