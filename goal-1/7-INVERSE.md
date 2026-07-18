# 7-INVERSE

## Current Facts

- Stage 6 is complete at clean synchronized commit `011b189`. The cached
  default `lake build` succeeds with 777 jobs under Lean/mathlib `v4.32.0`.
  The worktree and `origin/master` are synchronized at this baseline.
- `Circuit n` is already a balanced, feed-forward, six-constructor expression
  grammar. Every term has equal input/output width and evaluates to a bundled
  `Conservative n`; there is no arbitrary semantic gate, unequal boundary,
  contraction, weakening, feedback, state, trace, or recursive wire.
- `Conservative.inverse` packages the inverse equivalence with a proved
  Hamming-weight-preservation law. `WirePerm.onState_inverse` proves that the
  active state action of `wiring.symm` is the inverse of `wiring`.
  `PaperFredkin.map_involutive` proves the printed Fredkin gate is self-inverse,
  while the unit wire's static value map is identity.
- `PathDelay` is a static relation on grammar-induced boundary routes. It
  assigns one nonnegative delay unit to `unitWire`, zero to Fredkin/identity/
  structural permutation, adds across serial composition, and keeps tensor
  routes within their original block. `HasLatency` and
  `MeetsPaperCombinationalTiming` state the common-path condition separately
  from static evaluation.
- No `Circuit/Inverse.lean`, `Audit/Inverse.lean`, syntactic circuit inverse,
  inverse-path theorem, or inverse public API exists at this baseline.
- Section 7.1 defines a paper-network inverse by reversing each wire direction
  and replacing each gate by its inverse. Figure 19 is a directed-graph example
  that includes feedback; the compute/uncompute argument that follows instead
  assumes a combinational network with no feedback and equal unit-wire count on
  every boundary path.
- Figures 19–21 mirror the network horizontally while preserving top-to-bottom
  port order. Thus the checked expression inverse must reverse serial order,
  retain tensor block order, use `wiring.symm` for active structural
  permutations, and reuse only the actually self-inverse primitives.
- The paper's forward/inverse composite is an identity only in static
  input-output behavior. A latency-`L` term followed by its inverse has abstract
  latency `L + L`; two forward instances of the same unit-wire syntax do not
  become a zero-delay wire. Footnote 3 separately warns that invertibility does
  not imply physical time-reversal invariance.

## Updated Assumptions

- Define `Circuit.inverse : Circuit n → Circuit n` by structural recursion
  over exactly the existing six constructors. Width preservation is enforced
  by its type rather than by an existential transport or an additional width
  theorem.
- Map identity, unit wire, and paper Fredkin to themselves; map
  `permute wiring` to `permute wiring.symm`; map `seq first second` to
  `seq (inverse second) (inverse first)`; and map tensor componentwise without
  exchanging its left/right blocks.
- Prove static inverse correctness for every `Circuit`, without a timing
  hypothesis, because the type already enforces a balanced feed-forward term
  built only from bijective primitives and structural permutations. The paper's
  word *combinational* is matched separately by timing preservation.
- Prove exact route reversal before global latency preservation:
  a path from `input` to `output` with delay `d` becomes a path from `output`
  to `input` with the same `d`. The serial proof must explicitly commute its
  two nonnegative delay summands after reversing order.
- Prove semantic, not syntactic, cancellation. The free expression
  `seq circuit (inverse circuit)` is generally not `identity`; it merely
  evaluates to the identity equivalence, and its latency is the sum of the two
  passes.
- Keep the inverse of `unitWire` as the same syntax only as a static
  value/path-count proxy with exchanged path endpoints. Do not introduce
  negative delays, an oriented wire, a tick semantics, `t ↦ -t`, or a
  physical time-reversal theorem in this stage.
- Do not define inverse for `SourceCircuit`: its constants, discard, AND, OR,
  NOT, and FAN-OUT terms are generally unequal-width or nonbijective. Stage 8
  will instead apply the balanced target-circuit inverse to a complete
  realization.
- Do not import the Stage 6 compiler merely to prove optional Fredkin-count
  preservation. `Circuit.fredkinCount` currently belongs to the higher
  `Simulation.Fredkin` layer, and gate count is not required for the paper's
  inverse claim. Avoid reversing the dependency hierarchy for that extra fact.

## Big Picture Objective

Construct the exact syntactic inverse of every supported balanced feed-forward
circuit and prove that it is the inverse static boundary equivalence. Separately
prove that grammar paths reverse endpoints without changing their unit-wire
count, so the paper's equal-path combinational criterion is preserved at this
corrected expression-language scope.

## Detailed Implementation Plan

- Add `ConservativeLogic.Circuit.Inverse` with the stable public surface:

  ```text
  Circuit.inverse
  Circuit.inverse_identity
  Circuit.inverse_unitWire
  Circuit.inverse_fredkin
  Circuit.inverse_permute
  Circuit.inverse_seq
  Circuit.inverse_tensor
  Circuit.inverse_inverse
  Circuit.inverse_involutive
  Circuit.inverse_eval
  Circuit.eval_inverse_eval
  Circuit.eval_eval_inverse
  Circuit.PathDelay.inverse
  Circuit.pathDelay_inverse_iff
  Circuit.HasLatency.inverse
  Circuit.hasLatency_inverse_iff
  Circuit.MeetsPaperCombinationalTiming.inverse
  Circuit.meetsPaperCombinationalTiming_inverse_iff
  Circuit.HasLatency.seq_inverse
  Circuit.HasLatency.inverse_seq
  Circuit.UniformLatencyCircuit.inverse
  ```

  Exact names may change only if a compile-checked conflict requires it. The
  public semantic theorem must remain equality with
  `Conservative.inverse (Circuit.eval circuit)`, not merely a one-sided
  injectivity consequence.
- Prove double inversion structurally. Prove one structural cancellation
  direction first, including tensor via `split`/`append`, then use inverse
  uniqueness to establish the bundled evaluation equality and derive both
  public pointwise cancellation laws.
- Prove `PathDelay.inverse` by induction on the circuit/path structure. Derive
  the biconditional by reversing twice, then derive both directions of latency
  and global combinational-timing preservation.
- Give the uniform-latency certificate wrapper a proof-only inverse constructor
  with the same width and latency. It remains a certificate, not execution
  semantics.
- Add `ConservativeLogic.Audit.Inverse`, importing only the public API, with
  guarded failures, asymmetric value/path regressions, negative timing checks,
  public-surface checks, and axiom prints.
- Re-export only `Circuit.Inverse` through `API.lean` and the public root.
  Keep `Audit.Inverse` non-public. Update README, the authoritative plan, paper
  map, and correction log after final theorem statements are checked.

## Build Structure

- `Circuit/Inverse.lean` imports only `Circuit.Semantics` and `Circuit.Timed`.
  It owns structural inversion, static semantic correctness, path reversal,
  timing preservation, and the certificate constructor. It must not import
  realization, simulation, ancilla, sequential, billiard, or audit modules.
- `Audit/Inverse.lean` imports `ConservativeLogic.API` and remains a diagnostic
  consumer. It owns bounded examples, guarded failures, negative results, and
  `#print axioms` commands.
- `API.lean` and `ConservativeLogic.lean` remain thin public re-exports and
  documentation. Existing core syntax/semantics/timing modules are not edited.
- Stage 8 copy/uncompute, Stage 9 synthesis/completeness, Stage 10 feedback and
  oriented transition semantics, and physical models are forbidden here.

Focused and adjacent commands:

```text
cd formal
lake build ConservativeLogic.Circuit.Inverse
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Inverse
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Inverse
```

## Boundary Checks

- Syntax boundary: `inverse` must inspect the existing `Circuit` term and emit
  only its six constructors. It may not inspect `eval`, synthesize an arbitrary
  semantic equivalence, choose a circuit existentially, or route through the
  Stage 6 compiler.
- Serial/tensor boundary: serial order reverses because function-composition
  order reverses. Tensor order does not reverse because horizontal mirroring
  exchanges endpoints but preserves the declared vertical block order.
- Wiring boundary: active port movement uses `wiring.symm`; an involutive swap
  is insufficient as the only regression, so a non-self-inverse three-cycle is
  required.
- Semantic boundary: cancellation is equality of complete balanced boundary
  maps and loses no wire. It is not equality of syntax and does not project a
  selected result or ignore garbage.
- Timing boundary: inverse paths exchange boundary endpoints and retain the
  same `Nat` count. Forward/inverse composition adds latencies; there is no
  negative time or delay cancellation.
- Paper-model boundary: the theorem covers only the corrected feed-forward
  expression grammar. It does not invert Figure 19's feedback graph, an open
  stateful transducer, or a constrained partial physical gate.
- Stage boundary: no spy/copy layer, compute-copy-uncompute term, ancilla
  restoration theorem, arbitrary conservative completion, feedback transition,
  stream, billiard, entropy, or energy declaration may enter Stage 7.

## No-Cheating Checks

- Print `Circuit` and `Circuit.inverse`; confirm the former still has exactly
  six constructors and the latter has exactly six structural clauses with no
  evaluator, semantic gate, choice, or fallback branch.
- Check inverse reduction on every constructor, including width-zero identity
  and empty permutation. Guard that `Circuit.inverse` cannot accept
  `SourceCircuit.fanout` or an arbitrary state function.
- Use a non-self-inverse three-cycle to distinguish forward from inverse active
  port movement. Use a noncommuting Fredkin/permutation serial term to fail if
  serial order is not reversed.
- Test tensor with asymmetric block widths and with different equal-width
  behaviors, proving that inputs remain disjoint and blocks are not exchanged.
- Prove and exercise both static cancellation directions on arbitrary circuits;
  separately show the unit-wire round trip is not structural identity and has
  latency two despite evaluating to identity.
- Construct an asymmetric delayed/permuted route and check the exact forward
  and inverse endpoint/delay pair. Test that inversion preserves both a uniform
  positive-latency term and rejection of a nonuniform tensor.
- Audit the serial path proof for the explicit `Nat.add_comm` step. Do not use
  exhaustive evaluation for inverse correctness, double inversion, path
  reversal, or timing preservation.
- Scan the public inverse leaf for `Realization`, `Simulation`, `Ancilla`,
  `Sequential`, `Billiard`, `Classical.choose`, semantic circuit injection,
  physical time-reversal claims, proof holes, project axioms, and forbidden
  declaration modifiers.
- Run `#print axioms` on double inversion, bundled inverse evaluation, both
  cancellations, path reversal/iff, latency/timing preservation, round-trip
  latency, and the uniform-certificate inverse.

## Completion Requirements

- The public API exports a total width-preserving structural inverse over all
  six `Circuit` constructors, with named reduction laws and syntactic double
  inversion.
- `inverse_eval` proves equality with the inverse complete conservative
  equivalence for every source term. Both semantic cancellation directions are
  separately checked; no selected-output or existential statement substitutes
  for complete-map equality.
- `PathDelay.inverse` and its biconditional prove exact endpoint reversal with
  unchanged unit-wire count. `HasLatency` and
  `MeetsPaperCombinationalTiming` are preserved in both directions, including
  the certificate wrapper.
- Round-trip timing is stated honestly: latency `L` becomes `L + L`, and a
  concrete unit-wire round trip evaluates to identity while having latency two
  and remaining syntactically nonidentity.
- Zero width, non-involutive permutation direction, noncommuting serial order,
  tensor block order/disjointness, primitive inversion, asymmetric path
  reversal, uniform timing, and nonuniform timing all have checked regressions.
- No inverse is claimed for unequal-width source syntax, feedback graphs,
  traces/streams, constrained partial gates, or physical time reversal. The
  API imports no diagnostic module and the inverse leaf has only narrow
  dependencies.
- Focused/public/full and uncontended clean builds, fixed regressions, guarded
  negative checks, proof-hole/project-axiom/fallback/import scans, main-result
  axiom audits, `git diff --check`, complete diff inspection, and a clean
  synchronized worktree all pass.
- The paper map and correction log distinguish the checked static/path inverse
  from Figure 19 graph reversal, `t ↦ -t`, feedback execution, and physical
  time-reversal invariance; those obligations remain Stage 10 or out of scope.

## Stage Results

**Stage status: complete (2026-07-17), from baseline `011b189`.** Stage 8 was
not started.

- `Circuit.inverse` is a total width-preserving structural recursion over all
  six constructors. Identity, unit wire, and Fredkin remain unchanged; active
  permutations use `.symm`; serial order reverses; and tensor block order is
  retained. The six reduction laws, `inverse_inverse`, and
  `inverse_involutive` expose those facts directly.
- `inverse_eval` proves equality with the inverse complete `Conservative`
  equivalence for every balanced term. `eval_inverse_eval` and
  `eval_eval_inverse` prove both complete-state cancellation directions; the
  structural proof keeps both tensor blocks and introduces no hidden wire,
  fan-out, ancilla, garbage projection, semantic gate, or chosen circuit.
- `PathDelay.inverse` reverses exact boundary endpoints while preserving the
  same `Nat` delay. Its serial case explicitly commutes the two delay summands,
  and tensor paths stay in their original block. The path, `HasLatency`, and
  `MeetsPaperCombinationalTiming` biconditionals follow, as does the proof-only
  `UniformLatencyCircuit.inverse` constructor.
- Both round-trip timing theorems state `L + L`, never zero-delay
  cancellation. The audited unit-wire round trip evaluates to identity, is
  syntactically nonidentity, has an explicit delay-two path and uniform latency
  two, and rejects latency zero. At width zero, `HasLatency` is vacuous and
  nonunique; inversion only preserves a supplied certificate and claims no
  latency uniqueness.
- The diagnostic audit guards rejection of unequal-width `SourceCircuit`
  FAN-OUT and arbitrary state functions. It checks width-zero syntax and
  timing, a non-involutive three-cycle in both value and path directions,
  noncommuting serial order, asymmetric and equal-width tensor block retention,
  tensor cross-block exclusion, primitive values/timing, delayed endpoint
  reversal, uniform positive timing, and preservation of nonuniform rejection.
- Axiom prints contain no project axiom or proof hole. The constructor
  reductions are axiom-free; the remaining public results use only the
  expected Lean/mathlib foundations among `propext`, `Classical.choice`, and
  `Quot.sound`.
- Verification passed under Lean/mathlib `v4.32.0`: focused
  `Circuit.Inverse` build (706 jobs), public API/root build (778 jobs), inverse
  audit (777 jobs), cached default build (778 jobs), and an uncontended
  `lake clean` followed by the complete default build (778 jobs) and inverse
  audit (777 jobs). Proof-hole, project-axiom, fallback, dependency, hidden
  resource, and future-stage scans; `git diff --check`; and complete diff
  inspection passed. The completion checkpoint is committed and pushed with a
  clean worktree synchronized to `origin/master`.
- The result is deliberately scoped to the corrected balanced feed-forward
  expression grammar. It does not invert Figure 19's feedback graph, define
  oriented or `t ↦ -t` execution, establish physical time-reversal invariance,
  invert unequal-width source syntax, or implement compute-copy-uncompute.
