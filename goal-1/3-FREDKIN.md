# 3-FREDKIN

## Current Facts

- Stage 2 is complete at commit `1aa271a`; the worktree was clean when this
  stage began. The public API already supplies `BitState`, Hamming weight,
  `Reversible`, `Conservative`, and active `WirePerm` semantics.
- No `Gate` module, unit-wire declaration, Fredkin declaration, coordinatewise
  XOR predicate, or Stage 3 diagnostic currently exists.
- Direct inspection of PDF pp. 226–227 and the extracted Markdown confirms the
  unit-wire table `xᵗ ↦ yᵗ⁺¹` with equal bit value and Table (2)'s port order
  `(u,x₁,x₂) → (v,y₁,y₂)`.
- The eight printed Fredkin rows are `000→000`, `001→010`, `010→001`,
  `011→011`, `100→100`, `101→101`, `110→110`, and `111→111`. Thus Boolean
  `false`/paper `0` swaps the two data wires, while `true`/paper `1` leaves them
  in order.
- The paper calls Fredkin self-inverse and nonlinear. Self-inversion and
  conservation follow independently from the table. “Nonlinear” is not defined
  algebraically in the paper.
- The unit wire's aligned input/output value relation is identity, but its paper
  primitive has delay one. Two forward unit wires have delay two; the timed
  primitive is therefore not an involution merely because its value map is.

## Updated Assumptions

- Use `Fin 3` positions `0`, `1`, and `2` for `u/v`, `x₁/y₁`, and `x₂/y₂`
  respectively, exposed by a public explicitly ordered state constructor and
  projection lemmas.
- Implement the Fredkin semantic map as identity on the `true` control branch
  and the active data-index swap on the `false` branch. Repeated reads in this
  mathematical truth function specify a primitive; they do not authorize
  circuit fan-out.
- Prove involution structurally from the retained control branch and prove
  weight preservation structurally from identity/data permutation, not merely
  by trusting the eight table examples.
- Represent the unit wire by separate declarations for its conservative value
  map and numeric delay-one metadata. Do not invent a tick transition, path,
  feedback, oriented inverse, or time-reversal theorem in this stage.
- Interpret the paper's otherwise undefined “nonlinear” claim as failure of a
  stated lightweight `F₂`-linearity predicate: preservation of the all-false
  state and coordinatewise XOR. Record that this is a formal reconstruction,
  not a definition quoted from the paper or a physical theorem.
- Do not expose the common modern one-controlled Fredkin variant in the public
  API. Then no control-negation conjugacy or nonconservative control-negation
  circuit claim is needed.

## Big Picture Objective

Add reusable, convention-stable unit-wire and Fredkin value semantics, prove the
paper's complete finite truth-function claims, and settle one precise algebraic
meaning of Fredkin nonlinearity without crossing into circuit or timed dynamics.

## Detailed Implementation Plan

- Add `ConservativeLogic.Gate.UnitWire` with `UnitWire.value`,
  `UnitWire.delay`, their exact application/delay laws, and separate
  reversibility and Hamming-weight preservation theorems.
- Add `ConservativeLogic.Gate.Fredkin` with `PaperFredkin.state`, coordinate
  projections, `PaperFredkin.map`, coordinate/control laws, a parametric table
  equation, structural involution, `Reversible`/`Conservative` bundles, and
  separate reversibility/conservation theorems.
- Add `ConservativeLogic.Gate.Fredkin.Nonlinear` with lightweight
  `BitState.xor`, `BitState.falseState`, `XorLinear`, explicit intermediate
  counterexample equations, and `PaperFredkin.map_not_xorLinear`.
- Extend the thin public API/root imports with the three stable leaves. Do not
  import diagnostics publicly.
- Add `ConservativeLogic.Audit.Fredkin` with both unit-wire rows, all eight
  paper rows in printed order, asymmetric convention/order regressions, bundle
  agreement, the exact XOR counterexample, declaration checks, and main-result
  axiom audits.
- Update `README.md`, `goal-1/0-plan.md`, and this report only with results
  supported by completed proofs and verification.

Expected stable declarations include:

- `UnitWire.value`, `UnitWire.delay`, `UnitWire.value_apply`,
  `UnitWire.delay_eq_one`, `UnitWire.value_isReversible`, and
  `UnitWire.value_weightPreserving`.
- `PaperFredkin.state` with `state_control`, `state_data₁`, `state_data₂`, and
  `state_ext`, plus the explicitly semantic `PaperFredkin.dataSwap`.
- `PaperFredkin.map`, `map_control`, `map_data₁`, `map_data₂`,
  `map_of_control_false`, `map_of_control_true`, `map_state_false`,
  `map_state_true`, and `table`.
- `PaperFredkin.map_involutive`, `equiv`, `map_isReversible`,
  `map_weightPreserving`, `conservative`, `equiv_apply`, and
  `conservative_apply`.
- `BitState.xor`, `BitState.falseState`, `XorLinear`, the explicit
  `PaperFredkin.map_xor_counterexample_*` equations, the direct
  `PaperFredkin.map_xor_counterexample`, and
  `PaperFredkin.map_not_xorLinear`.

The required statement shapes are:

```text
UnitWire.value : Conservative 1
UnitWire.delay : Nat
UnitWire.delay_eq_one : UnitWire.delay = 1
UnitWire.value_apply (x : BitState 1) : UnitWire.value x = x

PaperFredkin.state (u x₁ x₂ : Bool) : BitState 3
PaperFredkin.dataSwap : WirePerm 3
PaperFredkin.map (x : BitState 3) : BitState 3
PaperFredkin.map_of_control_false (h : x 0 = false) :
  PaperFredkin.map x = WirePerm.onState PaperFredkin.dataSwap x
PaperFredkin.map_of_control_true (h : x 0 = true) :
  PaperFredkin.map x = x
PaperFredkin.table (u x₁ x₂ : Bool) :
  PaperFredkin.map (PaperFredkin.state u x₁ x₂) =
    PaperFredkin.state u (if u = true then x₁ else x₂)
      (if u = true then x₂ else x₁)
PaperFredkin.map_involutive : Function.Involutive PaperFredkin.map
PaperFredkin.equiv : Reversible 3
PaperFredkin.map_isReversible : IsReversible PaperFredkin.map
PaperFredkin.map_weightPreserving : WeightPreserving PaperFredkin.map
PaperFredkin.conservative : Conservative 3

XorLinear (f : BitState m → BitState n) : Prop
PaperFredkin.map_xor_counterexample_left :
  PaperFredkin.map
      (BitState.xor (PaperFredkin.state true false false)
        (PaperFredkin.state false true false)) =
    PaperFredkin.state true true false
PaperFredkin.map_xor_counterexample_right :
  BitState.xor
      (PaperFredkin.map (PaperFredkin.state true false false))
      (PaperFredkin.map (PaperFredkin.state false true false)) =
    PaperFredkin.state true false true
PaperFredkin.map_xor_counterexample :
  PaperFredkin.map
      (BitState.xor (PaperFredkin.state true false false)
        (PaperFredkin.state false true false)) ≠
    BitState.xor
      (PaperFredkin.map (PaperFredkin.state true false false))
      (PaperFredkin.map (PaperFredkin.state false true false))
PaperFredkin.map_not_xorLinear : ¬ XorLinear PaperFredkin.map
```

`PaperFredkin.dataSwap` is a public semantic coordinate equivalence so the
false-control theorem has an accessible statement. It is not evidence that a
wire-permutation circuit is free or synthesized.

## Build Structure

- `ConservativeLogic/Gate/UnitWire.lean` depends only on the Stage 2 reversible
  core and owns the value/delay separation.
- `ConservativeLogic/Gate/Fredkin.lean` depends only on the reversible core and
  owns the paper-convention semantic map and its static gate properties.
- `ConservativeLogic/Gate/Fredkin/Nonlinear.lean` depends on the gate leaf and
  owns the selected algebraic interpretation and counterexample, keeping it out
  of the low-dependency gate definition.
- `ConservativeLogic/API.lean` remains a thin public re-export; internal leaves
  do not import it.
- `ConservativeLogic/Audit/Fredkin.lean` imports the public API, remains
  diagnostic-only, and owns bounded row checks and `#print axioms` commands.

Focused and adjacent builds:

```text
cd formal
lake build ConservativeLogic.Gate.UnitWire
lake build ConservativeLogic.Gate.Fredkin
lake build ConservativeLogic.Gate.Fredkin.Nonlinear
lake build ConservativeLogic.API ConservativeLogic
lake build ConservativeLogic.Audit.Fredkin
lake build
lake clean
lake build
lake build ConservativeLogic.Audit.Fredkin
rg -n "sorry|admit|axiom|unsafe|opaque|partial|noncomputable" \
  ConservativeLogic ConservativeLogic.lean
git diff --check
```

## Boundary Checks

- Convention boundary: the namespace and documentation say paper convention,
  positions are public, both asymmetric swapped rows are checked, and no
  unnamed one-controlled alternate is exposed.
- Property boundary: involution/bijectivity and Hamming-weight preservation are
  separate theorems before the `Conservative` bundle is constructed.
- Timing boundary: `UnitWire.value` is an aligned port-value map and
  `UnitWire.delay` is metadata only. Neither is a sequential transition, a path
  composition theorem, or proof of `t ↦ -t` time reversal.
- Semantic/circuit boundary: conditional semantic coordinate reindexing is not
  a circuit syntax, synthesized wire permutation, fan-out, constant, garbage,
  or ancilla claim. The Fredkin semantic gate is assigned no latency.
- Algebra boundary: `XorLinear` states the chosen additive meaning explicitly;
  no Boolean-ring instance, affine/physical nonlinearity claim, or fixed-routing
  equivalence is inferred.
- Proof boundary: bounded `decide` is allowed for literal three-bit rows and the
  concrete XOR witness, but structural involution and conservation proofs must
  not be replaced by the audit table.
- Import/stage boundary: stable leaves use narrow internal imports and contain
  no public/audit imports, umbrella `Mathlib`/`Mathlib.Tactic`, circuit syntax,
  realization, sequential semantics, billiard mechanics, or universality.

## No-Cheating Checks

- Check the two unit-wire rows and delay exactly one; ensure there is no theorem
  equating same-time signals or calling the timed primitive involutive.
- Check every Table (2) row independently in paper order, not only the general
  table formula or the four symmetric rows.
- Prove the control is retained, data order on each branch, involution,
  reversibility, and weight preservation with named declarations.
- Construct `equiv` from the same raw `map` and its involution; construct
  `conservative` from that exact equivalence and the independent preservation
  proof. Audit application agreement for both bundles.
- State both sides of the XOR-additivity counterexample as explicit unequal
  three-bit states before deriving `¬ XorLinear`.
- Scan stable sources for `sorry`, `admit`, project `axiom`, `unsafe`, `opaque`,
  `partial`, `noncomputable`, fallback/reference implementations, implicit
  fan-out/circuit claims, alternate-control declarations, and later-stage terms.
- Inspect imports and every bounded `decide` occurrence. Run `#print axioms` on
  `UnitWire.value_apply`, `UnitWire.delay_eq_one`,
  `UnitWire.value_isReversible`, `UnitWire.value_weightPreserving`,
  `PaperFredkin.state_ext`, both tuple control laws, `PaperFredkin.table`,
  `PaperFredkin.map_involutive`, `PaperFredkin.map_isReversible`,
  `PaperFredkin.map_weightPreserving`, both bundles' application laws, both
  counterexample intermediate equations, `PaperFredkin.map_xor_counterexample`,
  and `PaperFredkin.map_not_xorLinear`.

## Completion Requirements

- The public root exports all planned stable declarations and no diagnostic
  module; existing Stage 2 consumers continue to build.
- Unit-wire static value identity, reversibility, conservation, and delay-one
  metadata are checked without claiming timed dynamics or time reversal.
- The exact paper ordering and all eight rows are machine checked; the raw map
  has general control laws, is involutive/bijective, and preserves weight.
- The selected coordinatewise-XOR linearity predicate is explicit, and named
  intermediate outputs prove a concrete failure of additivity and hence
  nonlinearity under that interpretation.
- Focused builds, audit/property checks, full `lake build`, an uncontended clean
  rebuild, proof-hole/project-axiom/forbidden-shortcut scans, main-result axiom
  audits, `git diff --check`, complete diff inspection, and a final clean
  worktree all pass.
- The plan/paper map records exact declarations, closes CL-001 for the default
  convention and CL-018 for the selected meaning, and leaves CL-002's oriented
  inverse/time-reversal component explicitly open.

## Stage Results

**Stage status: in progress.** No Stage 3 Lean declaration has yet been added.

### Remaining work

- Implement and compile the planned leaves without widening into Stage 4.
- Replace any declaration/proof assumption contradicted by Lean with a checked
  fact in this report and `0-plan.md`.
- Run and record the complete verification matrix before marking this stage
  complete.
