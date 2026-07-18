# Stage 12: Final Correspondence and API Audit

## Status

Complete on 2026-07-18 from clean synchronized baseline `1047322`.

## Current Facts

- Stages 1--12 are complete.  The default root `ConservativeLogic` imports the
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
outside every public import graph.  Generic width transport, structural block
routing, Fredkin counting, and result-register states were moved below the
compiler/uncompute layers.  `Circuit.cast`, `Circuit.eval_cast`,
`Circuit.middleSwapWiring`, and `Circuit.middleSwapWiring_on_append` are the new
canonical names; the former `Simulation.castCircuit`,
`Simulation.eval_castCircuit`, `Simulation.middleSwapWiring`, and
`Simulation.middleSwapWiring_on_append` names remain exact compatibility
forwarders.
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

Stage 12 completes the goal.

### Correspondence result

- Every paper-map row now has a final prose disposition.  Every CL-001--CL-024
  correction row uses one of five explicit statuses: proved, corrected,
  disproved, open, or out-of-model.  Canonical declaration names are used
  where Lean owns a result; commentary is not presented as a theorem.
- The two narrow correspondence gaps found by the review are closed:
  `ConservativeLogic.zeroCount` and
  `ConservativeLogic.WeightPreserving.zeroCount` expose the derived fixed-width
  `N₀`, while `ConservativeLogic.Circuit.wireOfLength`,
  `ConservativeLogic.Circuit.eval_wireOfLength`, and
  `ConservativeLogic.Circuit.wireOfLength_hasLatency` give every nonnegative
  integral abstract one-wire length its value and exact latency theorem.
  Neither result asserts an independent conserved quantity, spatial layout, or
  continuous mechanics.
- The final unresolved inventory is deliberate: all-zero workspace conversion
  and the paper's global scratch bounds (CL-011/CL-012); a general sequential
  compiler and delay normalization (CL-006); the cited reversible-only
  all-zero result-register construction; fixed-CPU encoding/simulation and
  complexity bounds; P8 geometry; continuous billiard dynamics, the Figure 15
  bridge, Figures 17--18, arbitrary delay/layout composition, and physical
  clearance; and the B./D. Silver attribution (CL-024).  Infinite reservoirs,
  Turing/CA universality, and thermodynamic conclusions remain out-of-model
  rather than unresolved finite-circuit theorems.

### API and ownership result

- The local import graph is acyclic.  The finite root and `API` have no reverse
  dependency on `Audit`, `Examples`, `Sequential`, or `Billiard`; the latter
  two remain independent opt-in umbrellas.  A clean default-build artifact
  check found none of those opt-in leaves.
- `Circuit.Structural`, `Circuit.Resources`, and `Ancilla.Register` now own
  generic structural semantics, syntax-only Fredkin counts, and
  circuit-independent register states respectively.  `NoAncilla` no longer
  imports realization.  The adjacent-transposition implementation is
  canonically contained in `ConservativeLogic.Completeness.Adjacent`; all of
  its former root names remain compatibility exports, so the namespace repair
  does not break existing consumers.
- `ConservativeLogic.Examples` imports only the stable finite root and checks
  ordinary Boolean compilation, complete compute-copy-uncompute, and clean
  Fredkin realization.  `ConservativeLogic.Audit.Axioms` is an explicit
  diagnostic leaf importing the finite and opt-in umbrellas; no public module
  imports it.
- The baseline diff contains a pre-existing tracked `.DS_Store` deletion.  It
  was treated as unrelated user state and was not restored or otherwise
  modified during this stage.

### Trust and resource result

- Source review found no proof holes, project `axiom` or `constant`
  declarations, `opaque`, `unsafe`, `partial`, `noncomputable`,
  `native_decide`, `Lean.ofReduceBool`, direct choice extractor, unsafe option
  extractor, or hidden collision/event fallback.  The documented classical
  sites select finite noncanonical completeness witnesses; they are not
  executable compilation or physical dynamics.
- Circuit syntax remains balanced and disjoint.  Fan-out consumes explicit
  initialized wires and exposes complement garbage; compilation and
  compute-copy-uncompute retain their exact source, scratch, result, garbage,
  latency, and Fredkin-count qualifications.  Sequential conservation remains
  complete-boundary flux/closed-state conservation, and billiard results remain
  selected legal interfaces and sampled routes.
- The eleven stage-specific audit leaves contain 225 `#print axioms` targets;
  the aggregate leaf contains 47, for 272 total, alongside 23 guarded
  `#check_failure` probes.  Built output reports only the expected Lean/mathlib
  `propext`, `Classical.choice`, and `Quot.sound` dependencies, with several
  results depending on fewer or no axioms.  No project assumption appears.

### Reproduction evidence

From the synchronized working tree:

- `lake clean && lake build` completed successfully with 1,006 jobs.
- The combined examples, all eleven stage audits, aggregate audit, sequential
  umbrella/audit, and billiard umbrella/audit build completed successfully with
  1,030 jobs.
- `python3 ConservativeLogic/Audit/completeness_groups.py` independently
  obtained generated/full group sizes `1/1`, `2/2`, `36/36`, and
  `207360/414720` at widths one through four.  The width-four target swap
  `1100 <-> 1010` is conservative and absent from the generated group.
- Import-boundary, proof-hole, forbidden-shortcut, direct-choice, physical-word,
  and collision-fallback reviews passed.  The full diff from `1047322` was
  reviewed, and `git diff --check 1047322 --` passed.

A fresh local clone at synchronized Lean-source commit `adf79d1` then ran
`lake update`, materialized the pinned mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, and passed the default build (998
reported jobs) plus the same complete opt-in/audit target set (1,030 reported
jobs).  This clone shared no project build artifacts with the working tree.
