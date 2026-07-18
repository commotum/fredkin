# 5-REALIZATION

## Current Facts

- Stage 4 is complete at synchronized commit `16562ab`; the worktree was clean
  when this stage began, and a cached default `lake build` succeeds with 710
  jobs.
- `Circuit n` is balanced and feed-forward. Its only value-processing gate is
  the paper Fredkin; identity, unit wire, bijective structural reindexing,
  exact-width serial composition, and disjoint tensor are the other
  constructors. There is no function/equivalence injection, contraction,
  weakening, implicit fan-out, or unequal-width circuit constructor.
- `Circuit.eval : Circuit n → Conservative n` exposes a globally bijective and
  Hamming-weight-preserving static map. `BitState.append`/`split` give ordered
  adjacent blocks and `hammingWeight_append` gives exact block additivity,
  including width zero.
- PDF pp. 229–230 defines realization schematically as
  `φ : (c,x) ↦ (y,g)`: source `c` is fixed independently of argument `x`,
  result `y` equals the target function, and sink/garbage `g` may depend on
  `x`. The diagram is a partition, not a physical-port ordering theorem.
- Direct inspection of Figures 4 and 6 under Table (2)'s ordered,
  zero-controlled Fredkin convention gives these complete slices:

  ```text
  AND:     (a,b,0) ↦ (a, a∧b, ¬a∧b), result y₁
  OR:      (a,1,b) ↦ (a, a∨b, ¬a∨b), result y₁
  NOT:     (a,1,0) ↦ (a, a, ¬a),    result y₂
  FAN-OUT: (a,1,0) ↦ (a, a, ¬a),    results (v,y₁)
  ```

  All unselected outputs are garbage. In particular, Figure 6(b,c)'s visually
  listed constants `0,1` route to physical data ports `(x₁,x₂)=(1,0)`; using
  `(0,1)` would exchange the copy and complement outputs.
- Section 3 source constants are consumed initialized inputs, not returned
  scratch. Later §7 scratch is a fixed initialized register promised back
  unchanged by a larger inverse/uncompute construction. The `(0ⁿ,1ⁿ)` result
  register overwritten by `(y,¬y)` is not clean scratch.
- A compile-only `/tmp` probe under the pinned toolchain validates a five-block
  layout, equality-transported full output packing, complete-state realization,
  complete-output and target/garbage injectivity, cardinality inequalities,
  scratch-cancelled Hamming-weight balance, and the four routed primitive
  equations. This probe is not a repository declaration or verification result.

## Updated Assumptions

- Use one explicit `Layout` with widths for source, clean scratch, argument,
  result, and garbage. Canonical input order is
  `(source,scratch,argument)` and canonical output order is
  `(result,scratch,garbage)`. A stored equality between those total widths
  accounts for every wire.
- A basic Figure 5 source/sink realization is the specialization with scratch
  width zero. Keeping scratch in the general interface makes restoration a
  full-state equality rather than prose, but Stage 5 does not construct the
  inverse/uncompute network from §7.
- Define `Realizes` with explicit source constants, initial scratch, target
  function, and complete garbage function. Do not existentially hide garbage
  or define realization as result projection alone.
- Canonical blocks are contiguous only in the semantic interface. Each
  primitive circuit must expose the active `WirePerm 3` values that route those
  blocks to the paper's physical `(u,x₁,x₂)` ports and route selected results
  back first. These are structural reindexings, not synthesized or timed wire
  layouts.
- General reversibility should imply that `(target argument, garbage argument)`
  is injective; clean scratch cannot distinguish arguments because it is fixed
  and returned. Consequently argument-independent garbage forces the target
  itself to be injective and yields the corresponding finite-cardinality bound.
- General conservation should imply
  `weight source + weight argument = weight result + weight garbage`; restored
  scratch cancels from both sides. This is static Hamming-weight accounting,
  not entropy, energy, or trajectory conservation.

## Big Picture Objective

Add a reusable, exhaustive static realization interface for ordinary
cross-width Boolean functions and prove the paper's four one-Fredkin examples
with every initialized input, selected result, returned scratch condition, and
garbage output made explicit—especially the constrained nature of FAN-OUT.

## Detailed Implementation Plan

- Add `ConservativeLogic.Realization.Core` with:

  ```text
  Realization.Layout
  Layout.inputWidth
  Layout.outputWidth
  Layout.packInput
  Layout.packOutput
  Realization.ArgumentIndependent
  Realization.Realizes
  ```

  `packInput` and `packOutput` must include all five blocks. Equality transport
  may reconcile the two balanced total-width expressions but may not add,
  remove, or permute a hidden wire.
- Add general theorem surface:

  ```text
  Layout.packInput_argument_injective
  Layout.hammingWeight_packInput
  Layout.hammingWeight_packOutput
  Realizes.completeOutput_injective
  Realizes.targetGarbage_injective
  Realizes.card_argument_le_resultGarbage
  Realizes.target_injective_of_argumentIndependentGarbage
  Realizes.card_argument_le_result_of_argumentIndependentGarbage
  Realizes.weight_balance
  ```

  The cardinality proofs must come from the proved injective maps, not from a
  width arithmetic shortcut. The conservation proof must use
  `Circuit.eval_weightPreserving` and `hammingWeight_append`.
- Add `ConservativeLogic.Realization.Primitive` with explicit fixed-width state
  builders, target functions, garbage functions, source constants, layouts,
  active input/output wirings, and actual `Circuit 3` terms for AND, OR, NOT,
  and FAN-OUT.
- Prove both complete Boolean equations and `Realizes` theorems:

  ```text
  fredkin_and_complete       fredkin_realizes_and
  fredkin_or_complete        fredkin_realizes_or
  fredkin_not_complete       fredkin_realizes_not
  fredkin_fanout_complete    fredkin_realizes_fanout
  fredkinFanoutCircuit_isReversible
  fredkinFanoutCircuit_weightPreserving
  ```

  The NOT and FAN-OUT input wiring must map canonical source `(0,1)` plus `a`
  to physical `(a,1,0)`. NOT must select physical `y₂`; FAN-OUT must select
  `(v,y₁)` and expose `y₂=¬a` as garbage.
- Extend `ConservativeLogic.API` and the root with the two stable realization
  leaves. Do not import the diagnostic module.
- Add `ConservativeLogic.Audit.Realization` with guarded impossible layouts and
  ill-typed direct width expansion, zero-width realization, all fixed primitive
  rows, explicit wiring-direction checks, argument-dependent garbage evidence,
  constrained FAN-OUT accounting, full-map reversibility/conservation checks,
  declaration inspection, and `#print axioms` on all stable main results.
- Update `README.md`, `goal-1/0-plan.md`, and this report only with facts
  supported by completed proofs and final verification.

## Build Structure

- `ConservativeLogic/Realization/Core.lean` imports the narrow circuit semantic
  leaf plus only the finite-cardinality support needed for the general
  constraint theorems. It owns no primitive truth table or diagnostics.
- `ConservativeLogic/Realization/Primitive.lean` imports the core realization
  interface and owns only the four Section 3 one-Fredkin constructions and
  their complete specs.
- `ConservativeLogic/API.lean` remains a thin stable re-export; internal leaves
  do not import it.
- `ConservativeLogic/Audit/Realization.lean` imports the public API and remains
  diagnostic-only.
- Do not add Stage 6 source-circuit syntax/translation, Stage 7 inverse syntax,
  Stage 8 compute-copy-uncompute, Stage 9 arbitrary-gate completion/synthesis,
  or any sequential/physical model.

Focused and adjacent commands:

```text
cd formal
lake build ConservativeLogic.Realization.Core
lake build ConservativeLogic.Realization.Primitive
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Realization
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Realization
```

Required scans cover proof holes/project axioms; forbidden declaration
modifiers; broad/internal imports; hidden existential garbage or result-only
projection definitions; arbitrary semantic-map/equivalence injection; omitted
layout fields; implicit copy/duplication; hard-coded alternate Fredkin logic;
unbounded `decide`; future-stage declarations; diagnostic leaks; and diff
whitespace.

## Boundary Checks

- Interface boundary: every input is source, returned scratch, or argument;
  every output is result, returned scratch, or garbage. The balance proof and
  full-state equation leave no unnamed auxiliary port.
- Source/scratch boundary: source is fixed independently of the argument but
  may be transformed. Scratch is also fixed initially and is required to
  reappear unchanged. Neither is synonymous with garbage.
- Garbage boundary: garbage has an explicit width and explicit function of the
  argument. Ignoring it observationally is not a circuit-level discard, and it
  cannot be reused as a constant unless argument independence is separately
  proved.
- Fan-out boundary: `fanoutFunction : BitState 1 → BitState 2` is only the
  selected result of a width-three conservative circuit initialized with two
  source bits. It is not a `Circuit 1`, `Circuit 2`, `Reversible 1`, or
  unrestricted equal-width copy primitive.
- Basis boundary: each primitive realization is an actual Stage 4 circuit
  containing one paper Fredkin plus explicit structural port reindexing. There
  is no `Circuit` injection of the target function or arbitrary conservative
  equivalence.
- Ordering boundary: the interface block order is a declared formal
  convention. Physical Fredkin ports and result selection are exposed by named
  active permutations; no order is guessed from vertical drawing position.
- Semantic boundary: `Realizes` is a static initialized-slice theorem. It says
  nothing about latency, physical routing, feedback, streams, energy, entropy,
  or recycling garbage.
- Stage boundary: returned scratch is represented in the interface, but no
  theorem constructs restoration beyond what a supplied realization proves.
  Inverse circuits and uncomputation remain Stages 7–8.

## No-Cheating Checks

- Print/check every `Layout` field and the full `Realizes` signature. Scan its
  definition to ensure the equality covers `Circuit.eval`'s whole output and
  accepts an explicit garbage function rather than an existential witness.
- Guard that a source-free layout for `BitState 1 → BitState 2` cannot be built
  with `rfl`, and guard that `Circuit 1` cannot be applied as a two-bit result.
- Check a width-zero direct realization so no positive-width assumption is
  hidden in packing, injection, cardinality, or weight proofs.
- For each primitive, test every argument row against the complete packed
  output, not only the selected result. Include direct checks of
  `F(0,1,0)=(0,0,1)` and `F(1,1,0)=(1,1,0)` to catch NOT/FAN-OUT source-order
  drift.
- Inspect the named wirings and test their active direction on asymmetric
  triples. A passive/active reversal or reversed serial order must fail a
  regression.
- Prove the FAN-OUT circuit's full map bijective and Hamming-weight preserving;
  separately show its selected unequal-width target is not being packaged as
  an equal-width reversible map.
- Give fixed arguments witnessing that AND garbage and FAN-OUT garbage depend
  on the argument. Do not label sink output reusable clean scratch.
- Audit every `decide`; allow only fixed Bool/width-three primitive regressions
  and guarded failures, never general layout/constraint proofs.
- Run `#print axioms` on packing weight laws, all general constraint theorems,
  all complete primitive equations and `Realizes` theorems, and FAN-OUT's
  global-map properties.
- Scan for arbitrary target-function injection into `Circuit`, hidden
  permutations/equivalences in `Layout`, later realization completion,
  simulation, inverse/uncompute, universality, sequential, or physical claims.

## Completion Requirements

- The public root exports an exhaustive five-block layout and full-state
  realization relation, plus the four exact Section 3 Fredkin realizations,
  but no diagnostic module.
- The type/equality surface accounts for every input and output wire and works
  when any or all blocks have width zero.
- General proofs establish complete-output and target/garbage injectivity,
  both cardinality bounds, the target-injectivity consequence for
  argument-independent garbage, and exact Hamming-weight balance with restored
  scratch cancelled.
- AND, OR, NOT, and FAN-OUT theorems state every fixed source bit, physical
  routing permutation, selected result, returned-scratch block, and garbage
  output under the paper's printed convention.
- FAN-OUT consumes source `(0,1)`, produces result `(a,a)` plus garbage `¬a`,
  and its underlying width-three circuit is proved globally reversible and
  conservative. No unrestricted copy gate or hidden duplication exists.
- Documentation distinguishes source, scratch, result, sink/garbage, static
  structural reindexing, and later restoration/recycling claims.
- Focused builds, public consumer build, full build, uncontended clean rebuild,
  guarded negative checks, complete fixed evaluations, zero-width tests,
  property and cardinality constraints, proof-hole/project-axiom/shortcut
  scans, main-result axiom audits, `git diff --check`, complete diff inspection,
  and a clean synchronized worktree all pass.
- The paper map and correction log resolve CL-004 for constrained one-bit
  FAN-OUT, advance CL-009 with the exact `(1,0)` data-port order, and leave
  garbage recycling, inverse construction, and arbitrary-function completion
  to their named later stages.

## Stage Results

**Stage status: in progress.** The paper/interface contract and compile probe
are complete; no Stage 5 repository Lean declaration has yet been added.

### Remaining work

- Implement the two stable leaves and diagnostic with the checked signatures.
- Run the complete verification matrix and independently inspect all primitive
  rows, constraint proofs, axiom footprints, imports, and stage-boundary scans.
- Replace this section with exact results and fold only verified facts into
  `0-plan.md` and the README.
