# Stage 12: Final Correspondence and API Audit

## Status

In progress on 2026-07-18 from clean synchronized baseline `1047322`.

## Current Facts

- Stages 1--11 are complete.  The default root `ConservativeLogic` imports the
  finite API only; registered execution and billiard sampling remain separate
  opt-in umbrellas at `ConservativeLogic.Sequential` and
  `ConservativeLogic.Billiard`.
- `ConservativeLogic.API` is an import-only finite surface.  Neither it nor the
  public root imports an `Audit`, `Sequential`, or `Billiard` module.
- Eleven stage-specific non-public audit leaves exercise the representation
  probe and Stages 2--11.  They retain exhaustive fixed examples, guarded
  negative checks, general theorem applications, and stage-specific
  `#print axioms` commands.  Stage 12 adds the separate aggregate
  `ConservativeLogic.Audit.Axioms` leaf.
- The README gives reproduction commands and a narrative of the finite,
  sequential, and sampled-billiard layers.  The authoritative paper claim map,
  correction log, declaration outline, and open boundaries remain in
  `goal-1/0-plan.md`.
- `ConservativeLogic.Examples` now demonstrates compilation, complete
  compute-copy-uncompute, and clean completeness while importing only the
  stable finite root.
- The Lake default target is the finite root.  Explicit builds are therefore
  required for the sequential and billiard umbrellas, their audits, and any
  final audit/example leaves added here.
- A repository-wide source scan currently finds no project `axiom`, proof
  hole, `unsafe`, `native_decide`, `Lean.ofReduceBool`, or direct classical
  event-selection fallback.  Standard Lean/mathlib classical and quotient
  axioms reported by prior `#print axioms` output must remain distinguished
  from project assumptions.

## Updated Assumptions

- A final examples leaf should consume `ConservativeLogic`, not internal or
  diagnostic modules, so it checks the actual stable finite surface.
- Sequential and billiard examples, if added, must import only their explicit
  opt-in umbrellas and must not flow back into the default root.
- The aggregate axiom audit should select every major theorem family while
  retaining the exhaustive details in the existing stage audits; copying all
  prior examples into one high-fanout file would add no coverage.
- The correspondence review found two genuine narrow gaps:
  `zeroCount`/`WeightPreserving.zeroCount` expose the paper's derived `N₀`, and
  `Circuit.wireOfLength` with its evaluation and latency theorems handles every
  finite abstract wire length.  Neither addition expands the spatial or
  physical model.

## Big Picture Objective

Finish the reusable library with a checked consumer-facing surface and a
complete evidence trail from each in-scope paper claim to a built declaration,
corrected theorem, checked obstruction, or explicit unresolved boundary.

## Detailed Implementation Plan

1. Independently audit the paper claim map, correction log, theorem outline,
   stage reports, and exact Lean declaration names.  Normalize dispositions so
   every in-scope claim has a final status.
2. Audit namespaces, docstrings, imports, umbrella boundaries, and declaration
   ownership.  Keep the finite root and API thin and avoid changes to stable
   theorem statements unless a concrete defect is found.
3. Add a narrow finite public-consumer examples leaf.  Add separate opt-in
   examples only if they check a boundary not already visible from the finite
   consumer.
4. Add a non-public aggregate axiom leaf covering the main foundation,
   Fredkin, circuit, realization, simulation, inverse, uncompute,
   completeness, sequential, and billiard results.
5. Reconcile the README, paper map, correction log, dependency map, theorem
   outline, open obligations, and this report against the final source.
6. Run focused example/audit builds, every stage audit, the independent group
   checker, import and forbidden-shortcut scans, an uncontended clean build,
   a clean-checkout reproduction, axiom inspection, and complete baseline diff
   review.

## Build Structure

Implemented low-fanout additions and ownership repairs:

```text
ConservativeLogic/Examples.lean       finite public-root consumer examples
ConservativeLogic/Audit/Axioms.lean   aggregate main-result axiom inspection
ConservativeLogic/Circuit/Structural.lean generic transport semantics/block routing
ConservativeLogic/Circuit/Resources.lean syntax-only Fredkin counting
ConservativeLogic/Ancilla/Register.lean circuit-independent result-register states
goal-1/12-AUDIT.md                    final evidence and unresolved inventory
```

The examples leaf imports only `ConservativeLogic`.  The diagnostic axiom leaf
explicitly imports the finite, sequential, and billiard umbrellas and remains
outside every public import graph.  Generic `Circuit.cast`, structural block
routing, Fredkin counting, and result-register states were moved below the
compiler/uncompute layers without changing their stable public names.
`Completeness.Adjacent` now contains the specialized local-synthesis helpers;
generic `CleanFredkinRealization.wireConjugate` is owned with its witness type.

Focused and adjacent builds:

```text
cd formal
lake build ConservativeLogic.Examples
lake build ConservativeLogic.Audit.Axioms
lake build ConservativeLogic
lake build ConservativeLogic.Sequential ConservativeLogic.Billiard
```

## Boundary Checks

- The final audit may document an unresolved claim but may not manufacture a
  theorem simply to make the map look complete.
- Examples must use public declarations through their intended umbrella and
  may not import an internal audit to obtain hidden helpers.
- The aggregate audit is diagnostic: it must not be imported by `API.lean`,
  the root, or either opt-in semantic umbrella.
- A successful finite default build is not evidence that opt-in sequential or
  billiard modules compile; those targets remain explicit.
- `#print axioms` reports are evidence about theorem dependencies, not proof
  that documentation, resource scope, or physical interpretation is sound.
- Existing classical existence in semantic completion and synthesis is not an
  executable compiler.  The final docs must preserve that distinction.
- No examples may erase constants, garbage, scratch, retained outputs,
  latency, valid-output subtypes, sampled-clearance scope, or selected
  collision legality.

## No-Cheating Checks

- Scan all Lean sources for proof holes, project axioms, unsafe/native
  evaluation shortcuts, and unclassified direct choice/fold fallbacks.
- Inspect every import edge into `ConservativeLogic`, `API`, `Sequential`, and
  `Billiard`; prove by source scan that audits/examples do not flow backward.
- Check all exact declaration names cited in the paper map and theorem outline
  by compiling consumer examples and the aggregate axiom leaf.
- Retain exhaustive Fredkin/interface truth rows, zero-width cases, fan-out
  source/garbage checks, timing counterexamples, width-four obstruction,
  sequential initialization/flux checks, and billiard legality/clearance
  distinctions in their existing audits.
- Run the dependency-free completeness group checker independently of Lean.
- Inspect every physical, energy, entropy, dissipation, time-reversal,
  arbitrary-delay, routing, and complexity hit in public source documentation;
  no such hit may be an unsupported theorem claim.
- Compare the entire Stage 12 diff against baseline `1047322`, not merely the
  latest autosave commit.

## Completion Requirements

- Every in-scope paper claim has a built declaration, corrected theorem,
  checked disproof, or clearly labeled unresolved/out-of-model disposition.
- The stable finite consumer examples compile using only `ConservativeLogic`;
  any opt-in examples preserve their separate boundaries.
- The aggregate axiom leaf covers every major result family and reports no
  unexplained project assumption.
- Public modules have stable names, appropriate ownership, minimal imports,
  and no diagnostic dependency or hidden fallback implementation.
- README and plan explain model boundaries, Fredkin convention, entry points,
  theorem correspondence, resources, exclusions, and exact reproduction
  commands.
- Focused examples/audits, every prior audit, the independent group checker,
  default and opt-in builds, clean dependency-tree and clean-checkout builds,
  scans, axiom inspection, `git diff --check`, and the complete baseline diff
  all pass.

## Stage Results

Pending implementation and final verification.
