# 4-CIRCUITS

## Current Facts

- Stage 3 is complete at synchronized commit `50c1269`; the worktree was clean
  when this stage began. A cached `lake build` still succeeds with 707 jobs.
- The public API supplies balanced `Conservative n` maps, ordered block
  append/split with Hamming-weight additivity, active bijective `WirePerm`
  semantics, `UnitWire.value` with separate `delay = 1`, and the exact
  paper-convention `PaperFredkin.conservative` map.
- At that baseline no circuit syntax, evaluator, feed-forward timing relation,
  equal-latency predicate, or Stage 4 diagnostic existed.
- Direct inspection of the extracted paper and PDF pp. 225, 227–229, and
  244–245 confirms that P6 restricts composition to one-to-one substitution;
  fan-out belongs inside an explicit signal-processing element.
- Section 2.5's literal circuit is a directed graph of instantaneous gates and
  positive-length delayed wires. It permits feedback and memory, so a
  serial/tensor term language is not automatically equivalent to that model.
- Section 7.1 calls a network combinational only when it has no feedback and
  every existing external-input-to-external-output path traverses the same
  number of unit wires. Figure 7 gives only the narrower
  argument-to-result-path fact and calls its network formally sequential.
- The ordinary abstract circuit model in §2.5 has balanced external port
  counts. It tacitly includes the unit wire and instantaneous identity gate in
  realizability bases, but does not declare arbitrary wire permutations to be
  free physical circuits; later constrained rail encodings are a separate
  interface issue.

## Checked Design Decisions

- Use `Circuit n`, where the single index is both input and output width. Every
  admitted primitive is balanced, so mismatched serial composition,
  contraction, and weakening should be ill-typed rather than represented by a
  checker after the fact.
- Fix the Stage 4 basis to structural identity, unit wire, paper Fredkin,
  explicit bijective structural port reindexing, exact-width serial
  composition, and disjoint tensor. Do not add an `ofFunction`, `ofEquiv`,
  `ofReversible`, `ofConservative`, or generic semantic-gate constructor that
  would trivialize later realization and synthesis stages.
- Treat `Circuit.permute` as zero-delay meta-level boundary reindexing with the
  existing active `WirePerm` convention. It is not a Fredkin synthesis theorem,
  routed crossover, or physical wire network.
- Let `Circuit.eval : Circuit n → Conservative n` reuse Stage 3 primitives.
  Reversibility and weight preservation remain separately exposed facts even
  though evaluation returns their bundle.
- Model static topology with a `PathDelay` relation. Unit wire contributes its
  exact delay one, Fredkin/identity/structural permutation contribute zero,
  serial paths add, and tensor paths remain in disjoint blocks. This is timing
  metadata only, not tick, trace, transition, stream, or feedback semantics.
- Define the selected paper combinational-timing criterion by existence of one
  latency shared by every existing boundary path. At width zero this is
  vacuously true; use zero as the canonical exhibited latency without claiming
  latency uniqueness or literal graph correspondence.
- A scalar maximum depth is insufficient, and requiring every syntax subtree
  to be balanced is too strong. The whole circuit
  `(unit ⊗ id); (id ⊗ unit)` must be accepted at latency one even though each
  intermediate tensor is unequal-latency.

## Big Picture Objective

Add a reusable balanced feed-forward circuit language whose only composition
operations consume ports one-to-one, give it exact static conservative
semantics, and formalize the paper's stronger equal-unit-wire-path condition
without claiming a graph, feedback, inverse-network, realization, or physical
routing result.

## Detailed Implementation Plan

- Add `ConservativeLogic.Circuit.Syntax` with the fixed constructors:

  ```text
  Circuit.identity (n : Nat) : Circuit n
  Circuit.unitWire : Circuit 1
  Circuit.fredkin : Circuit 3
  Circuit.permute (σ : WirePerm n) : Circuit n
  Circuit.seq (first second : Circuit n) : Circuit n
  Circuit.tensor (left : Circuit m) (right : Circuit n) : Circuit (m + n)
  ```

  Document that the inductive grammar is feed-forward, tensor blocks are
  ordered/disjoint, and permutation is structural rather than synthesized.
- Add `ConservativeLogic.Circuit.Semantics` with reusable disjoint tensor
  closure for `Reversible` and `Conservative`, then define bundled circuit
  evaluation. Expected stable laws include:

  ```text
  Reversible.tensor
  Reversible.tensor_apply_append
  Conservative.tensor
  Conservative.tensor_apply_append
  Circuit.eval
  Circuit.eval_identity
  Circuit.eval_unitWire
  Circuit.eval_fredkin
  Circuit.eval_seq
  Circuit.eval_tensor
  Circuit.eval_permute
  Circuit.eval_isReversible
  Circuit.eval_weightPreserving
  ```

  Tensor proofs must use `BitState.split`/`append` and
  `hammingWeight_append`; tensor must never feed the same block to both
  children. Fredkin and unit-wire equations must reuse their Stage 3 bundles,
  not duplicate their truth functions.
- Add `ConservativeLogic.Circuit.Timed` with:

  ```text
  Circuit.PathDelay c input output delay
  Circuit.HasLatency c delay
  Circuit.MeetsPaperCombinationalTiming c
  Circuit.UniformLatencyCircuit n delay
  ```

  plus base path rules, serial addition, tensor left/right embeddings, general
  latency closure for identity/unit/Fredkin/permutation/serial/equal-latency
  tensor, a blockwise serial/tensor theorem strong enough to certify
  compensated paths, and certificate-only constructors for the uniform-latency
  wrapper. The wrapper is not a timed execution semantics.
- Extend `ConservativeLogic.API` and the root with the three stable leaves.
  Diagnostics must not be publicly imported.
- Add `ConservativeLogic.Audit.Circuit` with guarded failures for mismatched
  serial widths and nonbijective reindexing; zero-width checks; asymmetric
  Fredkin, tensor-order, non-self-inverse permutation, and noncommuting serial
  evaluations; and exact timing regressions.
- The timing regressions must show:

  - structural identity and unit wire have the same value map but latencies
    zero and one respectively;
  - `unit ⊗ unit` has latency one;
  - acyclic `unit ⊗ id` does not meet the paper's equal-path timing criterion;
  - `(unit ⊗ id); (id ⊗ unit)` has latency one;
  - unequal arrivals followed by instantaneous Fredkin remain nonuniform.
- Update `README.md`, `goal-1/0-plan.md`, and this report only with results
  supported by completed proofs and verification.

## Build Structure

- `ConservativeLogic/Circuit/Syntax.lean` imports only the reversible core and
  owns the fixed grammar. It contains no semantics or future-stage interfaces.
- `ConservativeLogic/Circuit/Semantics.lean` imports the syntax and Stage 3
  primitive leaves. It owns tensor closure, evaluation, and static
  reversibility/conservation theorems.
- `ConservativeLogic/Circuit/Timed.lean` imports the syntax and unit-wire
  metadata. It owns path-delay/equal-latency facts but no state evolution.
- `ConservativeLogic/API.lean` remains a thin stable re-export. Internal leaves
  do not import it.
- `ConservativeLogic/Audit/Circuit.lean` imports the public API and remains
  diagnostic-only.

Focused and adjacent builds:

```text
cd formal
lake build ConservativeLogic.Circuit.Syntax
lake build ConservativeLogic.Circuit.Semantics
lake build ConservativeLogic.Circuit.Timed
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Circuit
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Circuit
```

The final verification reruns the following source classes (with narrower
follow-up patterns for constructor, reindexing, duplicate-semantics,
future-stage, `decide`, and diagnostic-leak inspection):

```sh
rg -n --glob '*.lean' '\bsorry\b|\badmit\b|^[[:space:]]*axiom\b' \
  ConservativeLogic ConservativeLogic.lean
rg -n --glob '*.lean' \
  '^[[:space:]]*(unsafe|opaque|partial|noncomputable)\b' \
  ConservativeLogic ConservativeLogic.lean
rg -n '^import ConservativeLogic$|^import ConservativeLogic\.(API|Audit)(\.|$)|^import Mathlib$|^import Mathlib\.Tactic' \
  ConservativeLogic/Circuit
rg -n '^[[:space:]]*\|' ConservativeLogic/Circuit/Syntax.lean
git diff --check
```

## Boundary Checks

- Model boundary: `Circuit` is a corrected feed-forward expression grammar,
  not the paper's arbitrary directed graph. There is no graph normalization,
  feedback, transducer, memory, trajectory, or closed-system theorem.
- Linearity boundary: serial composition consumes exactly one whole boundary;
  tensor consumes distinct left/right blocks; permutation is an equivalence.
  No constructor duplicates, discards, contracts, weakens, or invents a port.
- Basis boundary: the only value-processing gate constructor is the exact
  paper Fredkin. Unit wire and identity remain syntactically and temporally
  distinct even though their static value maps agree.
- Permutation boundary: structural port reindexing is explicit, active, and
  zero-delay. It is neither a physical routing layout nor synthesized from the
  Fredkin basis; later completeness statements must expose it as an allowance.
- Semantic boundary: `eval` is a finite boundary-value map. Its static
  conservation theorem does not establish the paper's closed trajectory
  invariant or open stream behavior.
- Timing boundary: paths count explicit unit-wire constructors. Gate,
  structural identity, and structural permutation contribute no wire delay.
  The timing layer has no execution clock or oriented time reversal.
- Combinational boundary: every syntax term is feed-forward, but only terms
  satisfying `MeetsPaperCombinationalTiming` are certified against the global
  all-existing-path latency clause. That name does not classify the term as a
  literal paper graph. Figure 7 is not certified without its full source/sink
  path evidence.
- Stage boundary: do not add inverse syntax, realization partitions,
  constants, garbage, scratch, ancillas, sequential state, billiard geometry,
  universality, or resource measures.

## No-Cheating Checks

- Inspect and `#print` the complete `Circuit` constructor surface. Guard that
  `Circuit.seq Circuit.unitWire Circuit.fredkin` cannot elaborate.
- Guard that an arbitrary `Fin 2 → Fin 2` cannot be supplied to
  `Circuit.permute`; only `WirePerm 2` is accepted.
- Scan for arbitrary-map injection names (`ofFunction`, `ofMap`, `ofEquiv`,
  `ofReversible`, `ofConservative`, generic semantic gate) and for
  copy/fan-out/drop/discard/contraction/weakening constructors.
- Prove tensor evaluation on arbitrary appended blocks and test asymmetric
  fixed inputs, including a zero-width side, so block aliasing or reversal is
  detected.
- Test active permutation direction with a non-self-inverse three-cycle and
  serial direction with noncommuting circuits.
- Derive general reversibility from the bundled equivalence and derive general
  weight preservation separately from primitive preservation and tensor block
  additivity. Do not infer either property from the other.
- Inspect every `decide` use; it is allowed only for bounded diagnostic states
  and guarded compile failures, never for arbitrary-width semantics or timing.
- Use actual `PathDelay` witnesses to reject unequal latency. Do not substitute
  maximum depth, local subtree balance, or evaluator equality for the
  all-path condition.
- Run `#print axioms` on both tensor closure laws, all six evaluation laws,
  general reversibility/conservation, serial/tensor path composition, latency
  closure, and named unequal/compensated regressions.
- Scan for later-stage declarations and for any claim that structural
  permutation is physical/synthesized or that the syntax corresponds to every
  paper graph.

## Completion Requirements

- The public root exports the fixed-width grammar, evaluator, and static timing
  predicates but no diagnostic module.
- Constructor signatures make mismatched serial connections and nonbijective
  reindexing ill-typed; constructor inspection and guarded failures cover this.
- Evaluation agrees generally with identity, Stage 3 unit/Fredkin semantics,
  first-then-second serial order, disjoint ordered tensor, and the active
  permutation action.
- Every circuit has a separately exposed bijectivity proof and Hamming-weight
  preservation proof, including width zero.
- Path timing counts unit wires exactly, composes serially, remains block-local
  under tensor, and distinguishes zero-delay structural identity from a
  delay-one unit wire.
- Fixed timing theorems accept equal and compensated paths and reject acyclic
  unequal paths, including unequal arrivals at Fredkin.
- Documentation states the corrected feed-forward scope, structural
  permutation policy, all-external-path criterion, Figure 7 limitation, and
  absence of sequential/physical claims.
- Focused builds, public consumer build, full build, uncontended clean rebuild,
  guarded negative checks, fixed evaluations, path-property tests,
  proof-hole/project-axiom/forbidden-shortcut scans, main-result axiom audits,
  `git diff --check`, complete diff inspection, and a clean worktree all pass.
- The plan/paper map records exact declarations, advances CL-002 only for
  static path length, records CL-005 as partial/open for Figure 7, and resolves
  the feed-forward/structural-permutation part of CL-017 without claiming graph
  equivalence or physical routing.

## Stage Results

**Stage status: complete (2026-07-17).** Stage 4 started from clean synchronized
commit `50c1269` and now supplies the public balanced circuit, evaluation, and
static path-timing surfaces without importing its diagnostic leaf.

### Implemented declaration surface

- `ConservativeLogic.Circuit.Syntax` defines exactly six constructors:
  `identity`, `unitWire`, `fredkin`, `permute`, `seq`, and `tensor`. A single
  width indexes both boundaries. Serial composition therefore requires equal
  widths, while `WirePerm n` makes reindexing bijective by construction.
- `ConservativeLogic.Circuit.Semantics` adds ordered disjoint tensor closure for
  `Reversible` and `Conservative`, including direct and arbitrary-append
  application laws. `Circuit.eval` reuses `UnitWire.value`,
  `PaperFredkin.conservative`, and `WirePerm.conservative`; equations cover all
  constructors. `eval_isReversible` and `eval_weightPreserving` expose the two
  general properties separately.
- `ConservativeLogic.Circuit.Timed` defines the recursive relation
  `PathDelay`, the global predicate `HasLatency`, the existential criterion
  `MeetsPaperCombinationalTiming`, and the proof-carrying wrapper
  `UniformLatencyCircuit`. Unit wire contributes exactly one; structural
  identity, Fredkin, and structural permutation contribute zero; serial paths
  add; tensor paths stay in one ordered block.
- `HasLatency.seq` and `HasLatency.tensor` prove ordinary uniform closure.
  `HasLatency.compensatedTensorSeq` is deliberately stronger than local
  balance: it proves global blockwise compensation across two nonuniform tensor
  layers.
- `ConservativeLogic.API` and the root re-export the three stable circuit
  leaves. `ConservativeLogic.Audit.Circuit` remains non-public.

The first dependent-inductive `PathDelay` probe could not eliminate cleanly
across the pinned Lean toolchain's dependent `m + n` indices. The checked final
form is instead a structurally recursive proposition with the same public
route witnesses and substantially simpler serial/tensor elimination. This is a
representation correction, not a weakening of the timing criterion.

### No-cheating and regression evidence

- Guarded elaboration failures reject
  `Circuit.seq Circuit.unitWire Circuit.fredkin` and reject an arbitrary
  nonbijective `Fin 2 → Fin 2` as a permutation argument. Constructor printing
  confirms there is no generic function/equivalence/conservative-map injection
  and no copy, contraction, weakening, discard, feedback, or unequal-arity
  constructor.
- General tensor equations on appended blocks, a zero-width tensor, an
  asymmetric Fredkin input, a non-self-inverse active three-cycle, and two
  noncommuting serial examples detect block aliasing, reversed tensor order,
  passive permutation drift, and reversed serial order.
- `eval_ne_copyFirst` proves that no `Circuit 2` evaluation equals the explicit
  noninjective overwrite-copy endomap. This is a semantic obstruction in
  addition to the constructor audit; initialized reversible copy remains a
  Stage 5 realization task.
- Structural identity and unit wire evaluate to the same static value map but
  have latencies zero and one. `unit ⊗ unit` has latency one;
  `unit ⊗ identity` fails the common-latency criterion;
  `(unit ⊗ identity); (identity ⊗ unit)` has latency one; and unequal arrivals
  followed by instantaneous Fredkin still fail the criterion.
- Width zero is covered both semantically and temporally. Its all-path
  criterion is vacuous, with zero used only as a canonical witness rather than
  a uniqueness theorem.

### Verification record

All commands ran under `formal/` with Lean/mathlib `v4.32.0`:

| Check | Result |
|---|---|
| `lake build ConservativeLogic.Circuit.Syntax` | passed, 701 jobs |
| `lake build ConservativeLogic.Circuit.Semantics` | passed, 704 jobs |
| `lake build ConservativeLogic.Circuit.Timed` | passed, 703 jobs |
| `lake build ConservativeLogic.API ConservativeLogic` | passed, 710 jobs |
| `lake build ConservativeLogic.Audit.Circuit` | passed, 709 jobs |
| adjacent cached `lake build` | passed, 710 jobs |
| `lake clean` followed by `lake build` | passed from scratch, all 718 jobs |
| post-clean `lake build ConservativeLogic.Audit.Circuit` | passed, all 709 jobs |

After the documentation foldback, a final cached default build again passed all
710 jobs and the circuit audit replayed all 709 jobs with the same constructor
and axiom output.

The diagnostic prints the complete constructor and public certificate surfaces.
Its `#print axioms` audit covers tensor closure/application, all evaluator laws,
general reversibility and weight preservation, path composition, base and
closure latency theorems, compensated timing, uniform-certificate serial/tensor
constructors, unequal/compensated regressions, and the copy obstruction. The
reported dependencies are only the expected Lean/mathlib foundations
`propext`, `Classical.choice`, and `Quot.sound` where applicable. No declaration
uses `sorryAx` or a project-defined axiom.

Final source scans find no `sorry`, `admit`, project `axiom`, forbidden
`unsafe`/`opaque`/`partial`/`noncomputable` declaration modifier, broad internal
import, arbitrary semantic-injection constructor, contraction/weakening/fan-out
constructor, nonbijective reindexing API, duplicate Fredkin/unit truth
implementation, future-stage interface, or diagnostic import leak. Every
stable-leaf import remains narrow. Stage 4 uses `decide` only in eight bounded
diagnostic examples; no stable circuit leaf contains it. `git diff --check`
passes, and the complete stage diff was inspected before handoff.

### Paper-map disposition and Stage 5 handoff

- P6's one-to-one composition rule is enforced by the grammar. Arbitrary fan-out
  is absent; later copy must consume explicitly initialized auxiliary wires and
  expose every output.
- The static `Circuit.eval_weightPreserving` theorem advances §§2.3–2.5 only for
  boundary-value circuit evaluation. It does not prove the paper's closed
  trajectory invariant or open transducer behavior.
- `PathDelay` advances CL-002 only for static unit-wire path length. Oriented
  inversion, execution, and physical time reversal remain open.
- On the corrected feed-forward grammar, `MeetsPaperCombinationalTiming`
  implements §7.1's global equal-delay clause as a separate predicate,
  partially resolving CL-005. Figure 7's narrower argument-to-result statement
  remains insufficient to certify all source/sink paths.
- CL-017 is resolved for the Stage 4 scope: `Circuit` is explicitly a corrected
  feed-forward expression grammar, and `permute` is explicit zero-delay
  structural boundary reindexing. No graph correspondence, feedback model,
  routed crossover, physical wire network, or permutation synthesis theorem is
  claimed.
- Stage 5 must add realization partitions for constants, arguments, results,
  garbage, and scratch without changing this fixed circuit basis or treating
  ignored outputs as dropped wires.
