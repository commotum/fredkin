import ConservativeLogic.Billiard.Collision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

/-!
# Independent legal scattering layers

The paper does not provide a total lattice update for arbitrary hard-ball
configurations.  This module therefore lifts `Collision.allowedEquiv` only to
a finite product of explicitly independent local sites.  Every site owns its
four channels, so simultaneous scattering is deterministic, involutive, and
ball-count preserving by construction.

This product does not create paths between sites, assign a ball to two events,
or solve mirror/collision and target conflicts.  Those require a separate
spacetime schedule.  The support-disjointness predicate at the end records one
necessary scheduling condition without pretending it is sufficient geometry.
-/

namespace ConservativeLogic.Billiard.ScatteringLayer

/-- A legal local collision mask at every independent site. -/
abbrev Configuration (sites : Type) := sites → Collision.AllowedState

namespace Configuration

/-- Simultaneously advance every independent legal collision site. -/
def step {sites : Type} (configuration : Configuration sites) : Configuration sites :=
  fun site => Collision.allowedEquiv (configuration site)

/-- Simultaneous independent-site scattering is involutive pointwise. -/
theorem step_involutive {sites : Type} :
    Function.Involutive (step : Configuration sites → Configuration sites) := by
  intro configuration
  funext site
  exact Collision.allowedEquiv.symm_apply_apply (configuration site)

/-- The simultaneous independent-site step as an explicit equivalence. -/
def stepEquiv (sites : Type) : Configuration sites ≃ Configuration sites where
  toFun := step
  invFun := step
  left_inv := step_involutive
  right_inv := step_involutive

/-- Total number of balls across finitely many independent sites. -/
def totalBallCount {sites : Type} [Fintype sites]
    (configuration : Configuration sites) : Nat :=
  ∑ site, hammingWeight (configuration site).1

/-- A simultaneous independent-site step preserves total ball count. -/
theorem totalBallCount_step {sites : Type} [Fintype sites]
    (configuration : Configuration sites) :
    totalBallCount (step configuration) = totalBallCount configuration := by
  apply Finset.sum_congr rfl
  intro site _
  exact Collision.allowedEquiv_weight (configuration site)

/-- Advance only one named independent site. -/
def stepAt {sites : Type} [DecidableEq sites] (selected : sites)
    (configuration : Configuration sites) : Configuration sites :=
  fun site => if site = selected then Collision.allowedEquiv (configuration site)
    else configuration site

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

/-- Three occupied channels, outside the selected local collision domain. -/
def illegalThreeBallMask : BitState 4 :=
  Interaction.output true true true false

/-- The legal local-state predicate rejects the named three-ball event. -/
theorem illegalThreeBallMask_not_allowed :
    ¬ Collision.AllowedLocal illegalThreeBallMask := by
  intro allowed
  rcases allowed with few | straight | deflected
  · exact (by decide : ¬ hammingWeight illegalThreeBallMask ≤ 1) few
  · exact (by decide : illegalThreeBallMask ≠ Collision.straightPair) straight
  · exact (by decide : illegalThreeBallMask ≠ Collision.deflectedPair) deflected

/-- Consequently the raw three-ball mask cannot inhabit the legal state subtype. -/
theorem no_illegalThreeBallState :
    ¬ ∃ state : Collision.AllowedState, state.1 = illegalThreeBallMask := by
  rintro ⟨state, equality⟩
  exact illegalThreeBallMask_not_allowed (equality ▸ state.2)

/-- Pairwise-disjoint source support required of simultaneously scheduled events. -/
def PairwiseDisjoint {particle event : Type} [DecidableEq particle]
    (support : event → Finset particle) : Prop :=
  ∀ left right, left ≠ right → Disjoint (support left) (support right)

end ConservativeLogic.Billiard.ScatteringLayer
