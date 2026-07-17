# 2-FINITE

## Current Facts

- Stage 1 is complete at commit `c510ce1`; the worktree was clean when this
  stage began.
- The pinned project uses Lean/mathlib `v4.32.0`. The public root currently
  exports no declarations, and the only Lean implementation file is the private
  Stage 1 representation probe.
- The probe compile-checks `Fin n → Bool`, filtered-`Finset.univ` Hamming
  weight, `Equiv.Perm`, `Fin.addCases`, and the rejected `Vector`/`BitVec`
  alternatives.
- Section 2.4 defines a conservative-logic gate by the conjunction of
  invertibility and conservation. Section 2.5 asserts that reversibility and
  bit conservation are independent properties, but gives no witness or proof.
- P7 asks abstractly for some additive conserved quantity. The Boolean model in
  §2.5 later selects `N₁`, the number of one-valued wires; Stage 2 may formalize
  that static count but not the later circuit-trajectory claim.
- Footnote 3 says invertibility/backward determinism does not imply invariance
  under time reversal. Stage 2 therefore formalizes bijectivity only, not an
  involution, network reversal, or physical time symmetry.

## Updated Assumptions

- Use transparent `BitState n := Fin n → Bool` and project-owned
  `hammingWeight`; retain the Stage 1 filtered-cardinality definition.
- Expose `IsReversible` and `WeightPreserving` as independent predicates on
  ordinary state maps. An `Equiv.Perm` alias and a bundled `Conservative`
  structure may package executable inverses and the conjunction, but neither
  predicate may be inferred from the other.
- Define block append/split with `Fin.addCases`, `Fin.castAdd`, and
  `Fin.natAdd`. The public API should expose projection/reconstruction laws and
  weight additivity without exposing proof-only subtype equivalences.
- Treat one-bit negation and two-bit Boolean sorting
  `(a,b) ↦ (a || b, a && b)` only as finite semantic endomap witnesses. The
  latter reuses input values at the meta-level and is not a claimed
  conservative-logic circuit or no-fan-out realization.
- Weight preservation is closed under identity and composition. An inverse is
  weight-preserving only when an actual equivalence and a preservation proof
  are supplied.
- Coordinate reindexing represents a physical-wire permutation by the explicit
  convention `output (σ i) = input i`; it is bijective and weight-preserving.

## Big Picture Objective

Build the reusable finite Boolean-state and conservative-equivalence foundation
while machine-checking, and keeping visibly separate, reversibility and
Hamming-weight preservation. The API must cover every finite width including
zero and provide the exact static lemmas later gate and circuit stages need.

## Detailed Implementation Plan

- Add `ConservativeLogic.State.Core` with `BitState`, `hammingWeight`, block
  `append`/`split`, projection and reconstruction lemmas, `appendEquiv`, and
  `hammingWeight_append`.
- Add `ConservativeLogic.Reversible.Core` with independent `IsReversible` and
  `WeightPreserving` predicates and their identity/composition laws;
  `Reversible := Equiv.Perm (BitState n)`; the bundled `Conservative`; inverse
  closure under an explicit equivalence; and `WirePerm.onState` with its
  documented action and preservation proof.
- Add `ConservativeLogic.Reversible.Independence` with one-bit negation as a
  reversible/non-weight-preserving witness and two-bit sorting as a
  weight-preserving/noninjective witness. Prove an explicit collision rather
  than relying only on a failed typeclass or cardinality argument.
- Add a thin `ConservativeLogic.API` and update the public root to re-export the
  three stable leaves.
- Add `ConservativeLogic.Audit.Finite` with zero-width examples, append/split
  checks, all fixed witness rows, a wire-permutation check, declaration checks,
  and `#print axioms` commands for the main Stage 2 results.
- Update `README.md`, `goal-1/0-plan.md`, and this report only with facts proved
  by the completed implementation and verification.

Expected stable declarations include:

- `BitState`, `hammingWeight`, `BitState.append`, `BitState.split`,
  `BitState.appendEquiv`, and `BitState.hammingWeight_append`.
- `IsReversible`, `WeightPreserving`, their identity/composition theorems, and
  inverse preservation under a `Reversible` equivalence.
- `Reversible`, `Reversible.injective`, `Reversible.surjective`, and the
  identity/composition/inverse constructors.
- `Conservative` with identity/composition/inverse constructors and explicit
  `toEquiv`/`weight_preserving` fields.
- `WirePerm`, `WirePerm.onState`, `WirePerm.onState_weightPreserving`, and
  `WirePerm.conservative`.
- `Independence.flipOne`, `Independence.sortTwo`, their exact property theorems,
  an explicit two-input collision, and existential independence theorems stated
  with both standalone predicates.

## Build Structure

- `ConservativeLogic/State/Core.lean` owns only finite state, partitions, and
  static weight facts.
- `ConservativeLogic/Reversible/Core.lean` depends on the state leaf and owns
  semantic map predicates/bundles and wire reindexing.
- `ConservativeLogic/Reversible/Independence.lean` is a proof/example leaf so
  fixed-width exhaustive proofs do not burden the foundational state module.
- `ConservativeLogic/API.lean` and `ConservativeLogic.lean` are thin public
  re-export layers. Internal modules must not import them.
- `ConservativeLogic/Audit/Finite.lean` is diagnostic-only and is not imported
  by the public API.
- Stage 3 Fredkin, circuit, realization, sequential, billiard, and universality
  modules remain absent.

Focused and adjacent builds:

```text
cd formal
lake build ConservativeLogic.State.Core
lake build ConservativeLogic.Reversible.Core
lake build ConservativeLogic.Reversible.Independence
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Finite
lake build
```

## Boundary Checks

- Predicate boundary: inspect signatures to ensure `IsReversible` is
  `Function.Bijective` and `WeightPreserving` is only pointwise Hamming-weight
  equality; neither definition mentions the other.
- Bundle boundary: `Conservative` must contain both an explicit `Equiv` and an
  explicit preservation proof. Its function coercion must not hide or synthesize
  either obligation.
- Semantic/circuit boundary: `sortTwo` is documented as an ordinary endomap,
  and no declaration claims that its reused inputs constitute legal circuit
  fan-out or a conservative-logic gate.
- Wire boundary: `WirePerm.onState` accepts only an index equivalence and states
  its direction with application lemmas; no nonbijective reindexing is accepted.
- Proof boundary: exhaustive `decide` proofs are allowed only for the fixed
  one- and two-bit witnesses/tests, never for arbitrary-width closure or weight
  additivity.
- Import boundary: foundational leaves use narrow mathlib imports and do not
  import `Mathlib`, `Mathlib.Tactic`, an audit leaf, or the public API.
- Stage boundary: no Fredkin, circuit, realization, ancilla, sequential,
  billiard, physical, or resource semantics are introduced.

## No-Cheating Checks

- Prove `hammingWeight_append` for arbitrary `m` and `n`; fixed examples do not
  substitute for the general theorem.
- Check width zero explicitly in the audit leaf in addition to relying on
  polymorphic theorem signatures.
- Prove inverse preservation from the forward preservation equation evaluated
  at the actual inverse image, not from an unrelated finite enumeration.
- Prove `sortTwo_not_injective` with named distinct inputs and an explicit equal
  output; do not call the map a conservative gate.
- Check all two-bit sorting rows and both one-bit negation rows so a coordinate
  order change cannot leave only the existential headline green.
- Audit `WirePerm.onState` on a nontrivial swap and check both the documented
  direction equation and total weight.
- Scan stable Lean sources for `sorry`, `admit`, project `axiom`, `unsafe`,
  `opaque`, hidden fallback/reference implementations, and later-stage terms.
- Record `#print axioms` output for the general additivity/closure theorems and
  both independence results; classify only ordinary Lean/mathlib foundational
  axioms.

## Completion Requirements

- All planned stable and audit modules build under the pinned toolchain, and
  the public root exports the Stage 2 API without importing diagnostics.
- State, append/split, weight, predicates, bundles, closure laws, and wire
  permutation action work for arbitrary widths, with explicit zero-width
  checks.
- `hammingWeight_append`, identity/composition/inverse preservation, and wire
  permutation preservation have general proof terms.
- Both directions of semantic independence have executable named witnesses and
  proofs of exactly the advertised properties; the noninvertible witness has an
  explicit collision.
- Focused builds, audit/property checks, full `lake build`, a clean rebuild,
  proof-hole/project-axiom/forbidden-shortcut scans, main-result axiom audits,
  `git diff --check`, complete diff inspection, and final clean-worktree check
  pass.
- The plan/paper map records the exact declaration names and preserves the
  distinction between static state facts and later gate/circuit trajectories.

## Stage Results

**Stage status: in progress.** No Stage 2 Lean declaration has yet been added.

### Remaining work

- Implement the modules and compile every stated theorem signature.
- Replace any proof/API assumption contradicted by Lean with a checked fact in
  this report and `0-plan.md`.
- Run and record the complete verification matrix before marking the stage
  complete. Stage 3 must not begin in this stage.
