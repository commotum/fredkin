import ConservativeLogic.Billiard.Interface
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Legal discrete collision-site semantics

The paper does not provide a total lattice update for arbitrary hard-ball
configurations.  This module therefore gives a deliberately narrower
scattering abstraction.  One site alternates between two incoming rails and
the constrained four-rail interaction output.  Invalid outgoing patterns are
excluded by the state type itself.  The selected step is deterministic,
involutive, and ball-count preserving on this legal subtype.

A finite `Configuration` is a product of independent sites.  Site indices own
disjoint logical ports: this product supplies simultaneous local scattering,
not geometric routing, shared balls, mirrors, or a global hard-ball mechanics.
-/

namespace ConservativeLogic.Billiard.CollisionSite

/-- Raw phase-tagged boundary data before imposing the outgoing-rail constraint. -/
inductive RawState where
  | incoming (value : BitState 2)
  | outgoing (value : BitState 4)

namespace RawState

/-- Incoming tuples are legal; outgoing tuples must lie in the exact interaction range. -/
def Legal : RawState → Prop
  | .incoming _ => True
  | .outgoing value => Interaction.IsValidOutput value

/-- Number of occupied rails in either phase. -/
def ballCount : RawState → Nat
  | .incoming value => hammingWeight value
  | .outgoing value => hammingWeight value

end RawState

/-- A collision-site state with the phase-appropriate rail constraint retained. -/
def State := {raw : RawState // raw.Legal}

namespace State

/-- Package every two-rail incoming state as a legal site state. -/
def incoming (value : BitState 2) : State :=
  ⟨.incoming value, trivial⟩

/-- Package a constrained four-rail output as a legal site state. -/
def outgoing (value : Interaction.ValidOutput) : State :=
  ⟨.outgoing value.1, value.2⟩

/-- Number of balls in a legal collision-site state. -/
def ballCount (state : State) : Nat := state.1.ballCount

/-- One legal scattering step, alternating the incoming and outgoing phases. -/
def step : State → State
  | ⟨.incoming value, _⟩ => outgoing (Interaction.equiv value)
  | ⟨.outgoing value, legal⟩ => incoming (Interaction.decode ⟨value, legal⟩)

/-- The selected constrained scattering step is its own inverse. -/
theorem step_involutive : Function.Involutive step := by
  rintro ⟨raw, legal⟩
  cases raw with
  | incoming value =>
      apply Subtype.ext
      change RawState.incoming (Interaction.decode (Interaction.equiv value)) =
        RawState.incoming value
      have recovered : Interaction.decode (Interaction.equiv value) = value := by
        change Interaction.equiv.symm (Interaction.equiv value) = value
        exact Interaction.equiv.symm_apply_apply value
      rw [recovered]
  | outgoing value =>
      apply Subtype.ext
      change RawState.outgoing
          (Interaction.encode (Interaction.decode ⟨value, legal⟩)) =
        RawState.outgoing value
      rw [Interaction.encode_decode]

/-- The legal local step bundled as an explicit reversible permutation. -/
def stepEquiv : State ≃ State where
  toFun := step
  invFun := step
  left_inv := step_involutive
  right_inv := step_involutive

/-- One legal local scattering step preserves occupied-rail/ball count. -/
theorem step_ballCount (state : State) : ballCount (step state) = ballCount state := by
  obtain ⟨raw, legal⟩ := state
  cases raw with
  | incoming value =>
      exact Interaction.encode_weightPreserving value
  | outgoing value =>
      change hammingWeight (Interaction.decode ⟨value, legal⟩) = hammingWeight value
      have encoded := Interaction.encode_weightPreserving (Interaction.decode ⟨value, legal⟩)
      rw [Interaction.encode_decode] at encoded
      exact encoded.symm

end State

/-- An independent collision-site state at every index. -/
abbrev Configuration (sites : Type) := sites → State

namespace Configuration

/-- Simultaneously advance every independent collision site. -/
def step {sites : Type} (configuration : Configuration sites) : Configuration sites :=
  fun site => State.step (configuration site)

/-- Simultaneous independent-site scattering is involutive pointwise. -/
theorem step_involutive {sites : Type} :
    Function.Involutive (step : Configuration sites → Configuration sites) := by
  intro configuration
  funext site
  exact State.step_involutive (configuration site)

/-- The simultaneous independent-site step as an explicit equivalence. -/
def stepEquiv (sites : Type) : Configuration sites ≃ Configuration sites where
  toFun := step
  invFun := step
  left_inv := step_involutive
  right_inv := step_involutive

/-- Total number of balls across finitely many independent sites. -/
def totalBallCount {sites : Type} [Fintype sites]
    (configuration : Configuration sites) : Nat :=
  ∑ site, State.ballCount (configuration site)

/-- A simultaneous independent-site step preserves total ball count. -/
theorem totalBallCount_step {sites : Type} [Fintype sites]
    (configuration : Configuration sites) :
    totalBallCount (step configuration) = totalBallCount configuration := by
  apply Finset.sum_congr rfl
  intro site _
  exact State.step_ballCount (configuration site)

/-- Advance only one named independent site. -/
def stepAt {sites : Type} [DecidableEq sites] (selected : sites)
    (configuration : Configuration sites) : Configuration sites :=
  fun site => if site = selected then State.step (configuration site) else configuration site

/-- Updates at distinct independent sites commute; no event ordering is selected. -/
theorem stepAt_commute {sites : Type} [DecidableEq sites] {left right : sites}
    (distinct : left ≠ right) (configuration : Configuration sites) :
    stepAt left (stepAt right configuration) =
      stepAt right (stepAt left configuration) := by
  funext site
  by_cases leftSite : site = left
  · subst site
    simp [stepAt, distinct]
  · by_cases rightSite : site = right
    · subst site
      simp [stepAt, Ne.symm distinct]
    · simp [stepAt, leftSite, rightSite]

end Configuration

/-- Three occupied output rails, outside the paper's four legal interaction rows. -/
def illegalThreeBallOutput : BitState 4 :=
  Interaction.output true true true false

/-- The restricted right-angle site semantics rejects the three-ball raw event. -/
theorem illegalThreeBallOutput_not_valid :
    ¬ Interaction.IsValidOutput illegalThreeBallOutput := by
  rintro ⟨inputValue, equality⟩
  have first := congrFun equality (0 : Fin 4)
  have second := congrFun equality (1 : Fin 4)
  have third := congrFun equality (2 : Fin 4)
  cases firstValue : inputValue 0 <;> cases secondValue : inputValue 1 <;>
    simp [Interaction.encode, illegalThreeBallOutput, firstValue, secondValue] at first second third

/-- Consequently the named raw three-ball phase cannot inhabit `State`. -/
theorem illegalThreeBallOutput_not_legal :
    ¬ RawState.Legal (.outgoing illegalThreeBallOutput) :=
  illegalThreeBallOutput_not_valid

/-- Pairwise-disjoint source support required of simultaneously scheduled events. -/
def PairwiseDisjoint {particle event : Type} [DecidableEq particle]
    (support : event → Finset particle) : Prop :=
  ∀ left right, left ≠ right → Disjoint (support left) (support right)

end ConservativeLogic.Billiard.CollisionSite
