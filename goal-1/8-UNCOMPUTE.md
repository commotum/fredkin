# 8-UNCOMPUTE

## Current Facts

- Stage 7 is complete at clean synchronized commit `ccab07c`. The cached
  default `lake build` succeeds with 778 jobs under Lean/mathlib `v4.32.0`.
- `Circuit` is a balanced feed-forward six-constructor grammar. Every term is
  a complete conservative equivalence; it has no arbitrary semantic gate,
  implicit FAN-OUT, discard, feedback, state, or hidden wire.
- `Realization.Layout` names returned scratch, consumed fixed source,
  argument, selected result, and complete transient garbage. Its canonical
  full equation is
  `(scratch,source,argument) → (scratch,result,garbage)`.
- `Realizes` fixes scratch and source independently of the argument and proves
  equality of the entire circuit output. In the paper's Figure 23 role split,
  `source` corresponds to the workspace constants `c`, while `garbage`
  corresponds to the midpoint `g`; the already-returned `scratch` is a stronger
  interface block carried by the library.
- `Circuit.inverse` is total on this balanced grammar.
  `eval_inverse_eval` proves complete static cancellation, while inverse paths
  retain their nonnegative unit-wire delay and round-trip latencies add.
- `Realization.Primitive.fredkinFanoutCircuit` already checks the initialized
  physical slice `(a,1,0) → (a,a,¬a)`. It is a full width-three Fredkin
  circuit, not a map `a ↦ (a,a)`.
- `Simulation.SourceCircuit.compile` can lift explicit FAN-OUT syntax to actual
  Fredkin-plus-structural-reindexing circuits with complete sources, garbage,
  exact Fredkin count, and zero explicit-unit-wire latency. General four-block
  structural routing is already proved by `middleSwapWiring_on_append`.
- No `Ancilla/Uncompute.lean`, `Audit/Uncompute.lean`, multi-bit spy layer,
  initialized `2n` result register, or compute-copy-uncompute theorem exists at
  this baseline.
- In §7.1 and Figures 20–23, a combinational realization `φ` takes fixed
  constants `c` and argument `x` to transient garbage `g` and result `y=f(x)`;
  `φ⁻¹` restores `(c,x)` from `(g,y)`. Applying one spy per result bit
  lets `y` continue into `φ⁻¹` while exposing `y` and `¬y` externally.
- Figure 24's result register has exactly `2n` wires, initialized as a top
  all-zero half and bottom all-one half and returned as the ordered pair
  `(y,¬y)`. Each input/output pair has weight one.
- Table (2) makes the paper's Fredkin zero-controlled. Therefore physical data
  inputs `(1,0)` yield data outputs `(a,¬a)` under control `a`, whereas the
  literal Figure 22 drawing labels its side inputs `(0,1)` but its outputs
  `(a,¬a)`. The checked reconstruction must explicitly swap the canonical
  `(a,0,1)` register order to physical `(a,1,0)`.
- The paper supplies no proof that all-zero scratch loses no generality, no
  fixed-basis synthesis for arbitrary `f` here, and no delay-padding scheme for
  the enlarged Figure 23 boundary. Those remain Stage 9, Stage 10, or outside
  the finite theorem surface.

## Updated Assumptions

- Prove a general static theorem from an explicit `Realizes` witness. Do not
  quantify over an arbitrary Boolean function without also accepting its
  concrete balanced realizing circuit, source, complete garbage, and proof.
- Use the canonical full boundary
  `(scratch,source,argument,0ⁿ,1ⁿ)` at input and
  `(scratch,source,argument,f(argument),¬f(argument))` at output. Restoring
  `Layout.packInput` proves scratch, source, and argument restoration at once;
  the transient midpoint garbage is uncomputed rather than returned.
- Define the one-bit spy as a real Fredkin term with an explicit input
  permutation from canonical `(a,0,1)` to physical `(a,1,0)`. Lift it to `n`
  disjoint spies using only tensor/serial composition and bijective structural
  reindexing; no input variable may be reused as two circuit inputs.
- Keep `0ⁿ` and `1ⁿ` as separately named width-`n` blocks. The output
  order is the through value consumed by the inverse, then the external copy,
  then its pointwise Boolean complement.
- The final circuit is globally reversible and Hamming-weight preserving
  because it is a `Circuit`; the computation equation is only an initialized
  slice for the prescribed source/result-register constants.
- Do not state the final function as a zero-garbage `Realizes` target containing
  only `(f x,¬f x)`: for noninjective `f` that would contradict the Stage 5
  no-garbage injectivity theorem. The returned argument must remain in the
  complete boundary equation.
- Static correctness does not need a timing hypothesis. A separate timing
  theorem may cover the zero-latency case, but the unpadded positive-latency
  construction must not be claimed globally equal-path; retain a concrete
  negative regression.
- Keep the prescribed source and existing scratch arbitrary. The paper's
  attributed all-zero scratch conversion, arbitrary-function existence,
  scratch-size bounds, and Fredkin completeness remain Stage 9 obligations.

## Big Picture Objective

Construct the paper's spy layer and compute-copy-uncompute network as explicit
balanced feed-forward circuits. Prove a complete initialized-slice equation
that restores every original main-register block and replaces exactly `n`
zeros plus `n` ones with the selected result and its pointwise complement.

## Detailed Implementation Plan

- Add `ConservativeLogic.Ancilla.Uncompute` with a stable public surface for:

  ```text
  Ancilla.zeroRegister
  Ancilla.oneRegister
  Ancilla.bitwiseNot
  Ancilla.resultRegisterInput
  Ancilla.resultRegisterOutput
  Ancilla.copyPairInputWiring
  Ancilla.copyPair
  Ancilla.copyPair_spec
  Ancilla.copyRegisterCircuit
  Ancilla.copyRegister_spec
  Ancilla.copyResultCircuit
  Ancilla.copyResult_spec
  Ancilla.computeCopyUncompute
  Ancilla.compute_copy_uncompute_spec
  Ancilla.compute_copy_uncompute_conservative
  ```

  Additional exact Fredkin-count and zero-latency theorems may enter this
  surface if their structural proofs remain narrow and do not imply a physical
  routing or depth model.
- Define the result-register source as
  `append (zeroRegister n) (oneRegister n)` and its output as
  `append value (bitwiseNot value)`. Prove their exact weights and support
  width zero without a separate fallback.
- Prove `copyPair_spec` from Table (2)'s actual physical input `(a,1,0)` after
  the named canonical input permutation. Check both Boolean rows independently.
- Construct the all-width copy layer from `n` disjoint Fredkins and explicit
  block/interleaving permutations. Its complete equation must retain the
  through value and expose both copy and complement.
- Embed that layer around a `Layout` midpoint without assuming source width
  equals garbage width. Prove exact action on
  `append (layout.packOutput scratch result garbage) resultRegisterInput`.
- Define the final serial circuit as forward realization on the main register,
  copy layer at its result block, and structural inverse on the main register,
  with the `2n` result register kept explicit throughout.
- Derive the complete specification from `Realizes`, the copy-layer equation,
  and `Circuit.eval_inverse_eval`; expose global reversibility/conservation as
  separate whole-map facts.
- Add `ConservativeLogic.Audit.Uncompute`, importing only the public API, with
  guarded failures, zero-width and exact port-order rows, a noninjective AND
  instance, arbitrary nonzero source/restored-scratch checks, transient-garbage
  disappearance, result/complement checks, resource checks, the delayed
  unpadded timing counterexample, public-surface checks, and axiom prints.
- Re-export only `Ancilla.Uncompute` through `API.lean` and the public root.
  Keep `Audit.Uncompute` non-public. Update README, the authoritative plan,
  paper map, and correction log only after theorem statements compile.

## Build Structure

- `Ancilla/Uncompute.lean` imports the existing constructive simulation/block
  routing layer and `Circuit.Inverse`. It owns only finite register constants,
  the explicit spy/copy circuits, the generic realization transformation,
  complete static correctness, and any exact syntax/timing corollaries.
- `Audit/Uncompute.lean` imports `ConservativeLogic.API` and remains a
  diagnostic consumer. It owns bounded rows, negative timing/copy checks,
  guarded failures, and `#print axioms` commands.
- `API.lean` and `ConservativeLogic.lean` remain thin public re-exports and
  documentation. Existing State, Circuit, Realization, Simulation, and Inverse
  modules are not edited.
- Stage 9 arbitrary-function completion, all-zero scratch conversion,
  fixed-basis universality, and asymptotic claims; Stage 10 feedback/delay
  scheduling; Stage 11 physical models; and thermodynamic conclusions are
  forbidden here.

Focused and adjacent commands:

```text
cd formal
lake build ConservativeLogic.Ancilla.Uncompute
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Uncompute
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Uncompute
```

## Boundary Checks

- Copy boundary: a single `a` controls a full width-three Fredkin whose other
  inputs are explicit `0` and `1`; it is never used twice as input syntax.
- Port boundary: canonical `(a,0,1)` is actively routed to Table (2)'s physical
  `(a,1,0)`. An omitted swap must fail at `a=false` by exchanging copy and
  complement.
- Register boundary: the input is exactly two contiguous blocks `0ⁿ` then
  `1ⁿ`; interleaving for Fredkin ports and regrouping at output are explicit
  bijective wire permutations, not hidden state functions.
- Midpoint boundary: source width and transient garbage width may differ. The
  copy layer touches the named result block only and retains scratch/result/
  garbage until the inverse consumes the exact complete midpoint.
- Final-equation boundary: the output includes restored scratch, source, and
  argument plus both `f x` and `¬f x`. No selected projection or existential
  garbage statement substitutes for equality of the complete state.
- Semantic boundary: the circuit is a global conservative equivalence for all
  states, while the claimed target equation requires the initialized source and
  result register. Do not claim the selected noninjective `f` is reversible.
- Timing boundary: general correctness is static. The unpadded construction is
  globally equal-path only when separately proved; positive forward latency is
  not silently canceled or balanced.
- Stage boundary: no arbitrary semantic circuit, all-zero scratch theorem,
  finite weight-layer completion, Fredkin universality, feedback, stream,
  billiard, entropy, energy, or complexity declaration may enter Stage 8.

## No-Cheating Checks

- Print the final circuit and exact Fredkin-count surface; confirm construction
  uses only existing `Circuit` constructors and contains one spy Fredkin per
  result bit plus the forward/inverse occurrences.
- Guard that the builder cannot accept an arbitrary state function or an
  unequal-width `SourceCircuit`; it requires a balanced target `Circuit` and a
  separate `Realizes` proof for the computation theorem.
- Check both one-bit spy rows and a deliberately unpermuted physical row so the
  Figure 22/Table (2) discrepancy cannot regress silently.
- Check `n=0` for register constants, copy circuit, final construction, and
  complete specification without invoking a special semantic fallback.
- Instantiate the generic theorem with noninjective AND. Verify arbitrary
  argument rows, exact restoration of the fixed source and returned scratch,
  result value, complement, and absence of transient AND garbage at the final
  boundary.
- Use a layout whose source and garbage widths differ and a nonzero scratch
  value so accidental identification or erasure of those blocks fails.
- Prove the result-register input/output weights match exactly. Do not use
  exhaustive evaluation for the general vector copy, generic uncompute, or
  resource theorem; bounded decision procedures are allowed only for fixed
  rows.
- Construct a positive-unit-wire-latency realization and prove the unpadded
  final circuit does not satisfy one global latency; do not treat static
  cancellation as timing cancellation.
- Scan the public leaf for semantic circuit injection, arbitrary-function
  choice, hidden source/ancilla/garbage, future-stage declarations, proof holes,
  project axioms, and forbidden declaration modifiers.
- Run `#print axioms` on the copy-pair/vector specs, embedded copy result,
  compute-copy-uncompute specification, conservation, exact resources, and any
  timing theorem/counterexample.

## Completion Requirements

- The public API exports a real one-bit Fredkin spy with its canonical-to-
  physical port permutation and a complete two-row equation.
- A constructive all-width copy layer uses exactly `n` disjoint initialized
  spies, works at `n=0`, retains the through register, and transforms
  `(value,0ⁿ,1ⁿ)` into `(value,value,¬value)` as a complete state.
- Given any explicit `Realizes` witness, the final concrete `Circuit` proves
  `(scratch,source,argument,0ⁿ,1ⁿ) →
   (scratch,source,argument,target argument,¬target argument)` with every
  width and block order stated. Source and argument are restored; transient
  garbage is absent because the exact midpoint is uncomputed.
- The construction is proved globally reversible and conservative separately
  from its initialized-slice functional equation. Exact register-weight
  accounting and any claimed Fredkin count are proved structurally.
- A zero-latency timing result or precisely weaker corrected statement is
  recorded, together with a positive-latency regression preventing an
  unsupported global combinational claim.
- Guarded arbitrary-function/source-circuit failures, Figure 22 port-order
  regression, zero width, noninjective AND, unequal source/garbage widths,
  nonzero scratch, complete result/complement, and timing boundaries all have
  checked diagnostics.
- No all-zero scratch conversion, arbitrary-function existence, fixed-basis
  completeness, asymptotic resource, feedback, physical-routing, or
  thermodynamic claim enters the theorem surface. Diagnostics remain
  non-public and dependencies remain one-way.
- Focused/public/full and uncontended clean builds, fixed regressions, guarded
  failures, proof-hole/project-axiom/fallback/dependency scans, main-result
  axiom audits, `git diff --check`, complete diff inspection, and a clean
  synchronized completion checkpoint all pass.

## Stage Results

**Stage status: complete (2026-07-17).** Stage 8 was implemented from clean
synchronized baseline `ccab07c` under Lean/mathlib `v4.32.0`.

- `ConservativeLogic.Ancilla.Uncompute` defines separately named all-zero and
  all-one halves, pointwise complement, the exact `2n`-wire input/output result
  registers, and their weights. The proof
  `hammingWeight_add_bitwiseNot` establishes the output weight for every width,
  rather than by bounded evaluation.
- `copyPairInputWiring = PaperFredkin.dataSwap` records the correction forced by
  Table (2): canonical `(a,0,1)` is routed to physical `(a,1,0)`.
  `copyPair_physical_spec` and `copyPair_spec` check the two interfaces, and the
  audit checks both Boolean rows plus deliberately unpermuted failures.
- `copyRegisterCircuit` is an explicit grouped-to-interleaved permutation,
  recursive tensor bank, and inverse regrouping. `copyRegister_spec` proves the
  complete all-width equation `(x,0ⁿ,1ⁿ) -> (x,x,not x)`, including `n = 0`,
  without reusing any input as two circuit wires.
- `copyResult_spec` embeds that bank into an arbitrary complete
  `(scratch,result,garbage)` midpoint. Its width transports use only
  `Layout.balanced`; source and garbage widths are never identified.
- From a supplied concrete `Realizes` witness,
  `compute_copy_uncompute_spec` proves
  `(scratch,source,argument,0ⁿ,1ⁿ) ->
   (scratch,source,argument,target,not target)` as equality of the entire
  state. The supplied scratch, consumed source, and argument return exactly;
  the named transient midpoint garbage is uncomputed. The returned argument
  and ancillary result/complement register remain explicit.
- `compute_copy_uncompute_isReversible` and
  `compute_copy_uncompute_conservative` state the global whole-map properties
  separately from the initialized slice. Exact syntax theorems prove one copy
  Fredkin per result bit and total count
  `count(circuit) + (resultWidth + count(circuit))`.
- `computeCopyUncompute_hasLatency_zero` is intentionally conditional on a
  zero-latency supplied circuit. The non-public actual-builder regression
  `unitWireUncompute_not_meetsPaperCombinationalTiming` constructs a delay-two
  main path and a delay-zero result-register path, refuting an unsupported
  positive-latency generalization without padding.
- `ConservativeLogic.Audit.Uncompute` imports only `ConservativeLogic.API` and
  checks guarded arbitrary-function/unequal-width builder failures, the port
  correction, missing-one conservation obstruction, zero and asymmetric
  widths, noninjective AND, nonzero scratch/source, unequal source/garbage
  widths, result width zero with a nonempty main register, transient-garbage
  disappearance, nonidentity, global properties, exact counts, and timing.

Verification evidence:

- Focused public build: `ConservativeLogic.Ancilla.Uncompute`, 772/772 jobs.
- Public API/root build: 779 jobs; cached default build: 779 jobs.
- Dedicated audit build: 778/778 jobs.
- After stopping concurrent diagnostic commands, an uncontended `lake clean`
  followed by the default build completed 787/787 jobs. The post-clean
  `ConservativeLogic.Audit.Uncompute` build completed 778/778 jobs. An earlier
  contested attempt was discarded after a reviewer compile raced the clean and
  removed an expected `.olean`; it is not counted as verification evidence.
- Public and audit `#print axioms` output contains only Lean/mathlib foundations
  `propext`, `Classical.choice`, and `Quot.sound`. Source scans find no
  executable `sorry`, `admit`, project `axiom`, `unsafe`, `opaque`,
  `Classical.choose`, `Nonempty.some`, semantic-circuit injection, or
  source-language fallback in the public leaf.
- The public leaf imports only `Circuit.Inverse` and `Simulation.Fredkin`; the
  API exports it, the root remains thin, and the audit remains non-public.
  Independent public-soundness and documentation/audit reviews found no
  remaining actionable issue.
- `git diff --check` and complete baseline-diff inspection pass. README, public
  module documentation, theorem map, paper map, module direction, and
  CL-009/CL-010/CL-020 now record the proved result and its corrected limits.

No arbitrary-function existence, all-zero-scratch conversion, fixed-basis
Fredkin completeness, asymptotic scratch/resource theorem, delay-padding
algorithm, feedback/trace semantics, physical routing, or thermodynamic claim
was added. At this Stage 8 completion baseline, Stage 9 had not started.
