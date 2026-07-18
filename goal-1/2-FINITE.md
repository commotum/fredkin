# 2-FINITE

## Current Facts

- Stage 1 is complete at commit `c510ce1`; the worktree was clean when this
  stage began.
- At the start of this stage, the pinned project used Lean/mathlib `v4.32.0`,
  the public root exported no declarations, and the only Lean implementation
  file was the private Stage 1 representation probe.
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
  `BitState.appendEquiv`, and `hammingWeight_append`.
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

**Stage status: complete (2026-07-17).** Stage 2 stops at the finite static-map
boundary; no Stage 3 gate or circuit semantics were introduced.

### Implemented surface

- `ConservativeLogic.State.Core` defines transparent `BitState`, filtered-card
  `hammingWeight`, ordered `append`/`split`, both round trips,
  `BitState.appendEquiv`, `hammingWeight_zero`, and the arbitrary-width theorem
  `hammingWeight_append`.
- `ConservativeLogic.Reversible.Core` defines independent `IsReversible` and
  `WeightPreserving` predicates; `Reversible`; the explicitly two-field
  `Conservative` bundle; valid identity, serial-composition, and inverse laws;
  and the active `WirePerm.onState` action with
  `onState_apply_image : onState σ x (σ i) = x i` and a general weight proof.
- `ConservativeLogic.Reversible.Independence` proves one-bit negation reversible
  but not weight-preserving and proves two-bit Boolean sorting weight-preserving
  but noninjective using the named `leftHot`/`rightHot` collision. The module
  calls sorting only an ordinary semantic endomap, never a circuit or gate.
- `ConservativeLogic.API` and `ConservativeLogic` re-export the stable leaves.
  `ConservativeLogic.Audit.Finite` remains non-public and checks widths zero,
  nonzero append/split order, both negation rows, all four sorting rows, and both
  directions of a nontrivial two-wire swap. A three-wire non-self-inverse cycle
  distinguishes the active action from its inverse, and width-zero append,
  `appendEquiv`, state action, and conservative wire action are explicit.

The proposed name `BitState.hammingWeight_append` was corrected to the actual
root-namespace theorem `ConservativeLogic.hammingWeight_append`. No theorem was
moved merely to preserve a provisional report name.

### Verification evidence

From `formal/`, the focused builds passed:

```text
lake build ConservativeLogic.State.Core
  ✔ [699/699] Built ConservativeLogic.State.Core
lake build ConservativeLogic.Reversible.Core
  ✔ [700/700] Built ConservativeLogic.Reversible.Core
lake build ConservativeLogic.Reversible.Independence
  ✔ [701/701] Built ConservativeLogic.Reversible.Independence
lake build ConservativeLogic.API ConservativeLogic
  ✔ Built ConservativeLogic.API
  ✔ Built ConservativeLogic
lake build ConservativeLogic.Audit.Finite
  ℹ [703/703] Built ConservativeLogic.Audit.Finite
```

An uncontended `lake clean` followed by `lake build` rebuilt the dependency
slice and all public project modules successfully (`712 jobs`); rebuilding the
diagnostic audit afterward also succeeded (`703 jobs`). An earlier clean retry
overlapped a delegated audit process that had independently invoked Lake and
failed transiently while both processes emitted dependency `.olean` files. No
project declaration failed, and that concurrent attempt is not counted as the
clean-build evidence.

The audit's `#print axioms` commands cover append/split reconstruction,
`hammingWeight_append`, standalone and bundled composition/inverse preservation,
wire-action composition/inverse/preservation, and both independence directions.
Every result was axiom-free or depended on a subset of:

```text
[propext, Classical.choice, Quot.sound]
```

`IsReversible.comp` was axiom-free; structural extensionality results used
`[propext, Quot.sound]`; cardinality/preservation results used the full listed
set. These are ordinary Lean/mathlib foundational axioms; no `sorryAx` or
project-specific axiom occurs. Stable-source scans found no `sorry`, `admit`,
project `axiom`, `unsafe`, `opaque`, `partial`, `noncomputable`, umbrella
`Mathlib`/`Mathlib.Tactic` import, foundational import of the public/audit
layers, fallback implementation, or later-stage declaration. Every `decide`
occurrence is confined to the fixed one-/two-bit witness module or the finite
audit; arbitrary-width additivity and closure theorems use general proofs.

### Facts carried to Stage 3

- Stage 2 proves only static Hamming-weight additivity and preservation. Unit
  wire, Fredkin-gate, circuit, and trajectory conservation remain later proof
  obligations.
- `Reversible` means an explicitly invertible equivalence, not involutivity or
  physical time-reversal invariance.
- Semantic predicate independence is now closed, but no circuit-language
  interpretation of either witness has been claimed.
- The active physical-wire convention is fixed as `output (σ i) = input i` and
  should be reused explicitly when Stage 3 chooses triple coordinates.
