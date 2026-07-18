import ConservativeLogic.Billiard

/-!
# Adversarial audit of the constrained billiard abstraction

This non-public leaf checks every interaction and switch row, constrained
inverse use, unequal-width vacancy changes, the selected legal collision masks,
independent simultaneous sites, event-support overlap, sampled routing and
clearance distinctions, and every Figure 14 endpoint case.

The union and wire-permutation obstructions ensure that the selected collision
is not silently implemented as independent structural routing.  None of these
checks upgrades sampled trajectories to continuous hard-ball mechanics.
-/

namespace ConservativeLogic.Audit.Billiard

open ConservativeLogic
open ConservativeLogic.Billiard

/-! ## Exact constrained rail tables -/

example : Interaction.encode (Interaction.input false false) =
    Interaction.output false false false false := rfl

example : Interaction.encode (Interaction.input false true) =
    Interaction.output false true false false := rfl

example : Interaction.encode (Interaction.input true false) =
    Interaction.output false false true false := rfl

example : Interaction.encode (Interaction.input true true) =
    Interaction.output true false false true := rfl

example (input : BitState 2) : Interaction.equiv.symm (Interaction.equiv input) = input :=
  Interaction.equiv.symm_apply_apply input

example : Fintype.card Interaction.ValidOutput = 4 := Interaction.card_validOutput

example : ¬ Nonempty (BitState 2 ≃ BitState 4) := Interaction.no_raw_equiv

example (input : BitState 2) :
    vacancies (Interaction.encode input) = vacancies input + 2 :=
  Interaction.encode_vacancies input

example : Switch.encode (Switch.input false false) = Switch.output false false false := rfl

example : Switch.encode (Switch.input false true) = Switch.output false false true := rfl

example : Switch.encode (Switch.input true false) = Switch.output true false false := rfl

example : Switch.encode (Switch.input true true) = Switch.output true true false := rfl

example (input : BitState 2) : Switch.equiv.symm (Switch.equiv input) = input :=
  Switch.equiv.symm_apply_apply input

example : Fintype.card Switch.ValidOutput = 4 := Switch.card_validOutput

example : ¬ Nonempty (BitState 2 ≃ BitState 3) := Switch.no_raw_equiv

example (input : BitState 2) :
    vacancies (Switch.encode input) = vacancies input + 1 :=
  Switch.encode_vacancies input

/-! ## Local collision and the legal independent layer -/

example : Collision.map Collision.straightPair = Collision.deflectedPair :=
  Collision.map_straightPair

example : Collision.map Collision.deflectedPair = Collision.straightPair :=
  Collision.map_deflectedPair

example : Collision.straightPair = Interaction.invalidBothSingles := rfl

/-- `0110` is legal before scattering but invalid as a post-interaction rail tuple. -/
example : ¬ Interaction.IsValidOutput Collision.straightPair :=
  Interaction.invalidBothSingles_not_valid

example (state : Collision.AllowedState) :
    Collision.allowedEquiv.symm (Collision.allowedEquiv state) = state :=
  Collision.allowedEquiv.symm_apply_apply state

example (input : BitState 2) :
    Collision.map (Collision.embed input) = Interaction.encode input :=
  Collision.map_embed input

example : ¬ Collision.AllowedLocal ScatteringLayer.illegalThreeBallMask :=
  ScatteringLayer.illegalThreeBallMask_not_allowed

private def emptyLayer : ScatteringLayer.Configuration (Fin 0) :=
  fun site => Fin.elim0 site

example : ScatteringLayer.Configuration.totalBallCount emptyLayer = 0 := rfl

example {sites : Type} [Fintype sites]
    (configuration : ScatteringLayer.Configuration sites) :
    ScatteringLayer.Configuration.totalBallCount
        (ScatteringLayer.Configuration.step configuration) =
      ScatteringLayer.Configuration.totalBallCount configuration :=
  ScatteringLayer.Configuration.totalBallCount_step configuration

example {sites : Type} [DecidableEq sites] {left right : sites}
    (distinct : left ≠ right) (configuration : ScatteringLayer.Configuration sites) :
    ScatteringLayer.Configuration.stepAt left
        (ScatteringLayer.Configuration.stepAt right configuration) =
      ScatteringLayer.Configuration.stepAt right
        (ScatteringLayer.Configuration.stepAt left configuration) :=
  ScatteringLayer.Configuration.stepAt_commute distinct configuration

private def tripleCandidateSupports : Bool → Finset (Fin 3)
  | false => {0, 1}
  | true => {1, 2}

/-- Two candidate pair events sharing particle `1` cannot run simultaneously. -/
theorem tripleCandidates_conflict :
    ¬ ScatteringLayer.PairwiseDisjoint tripleCandidateSupports := by
  intro pairwise
  have disjoint := pairwise false true (by decide)
  exact (Finset.disjoint_left.mp disjoint)
    (show (1 : Fin 3) ∈ tripleCandidateSupports false by decide)
    (show (1 : Fin 3) ∈ tripleCandidateSupports true by decide)

/-! ## Collision is not independent structural routing -/

private def stateOr {width : Nat} (left right : BitState width) : BitState width :=
  fun wire => left wire || right wire

private def singletonB : BitState 4 := Interaction.output false true false false
private def singletonC : BitState 4 := Interaction.output false false true false

/-- The selected two-ball interaction is not the union of independent singleton routes. -/
theorem collision_not_unionPreserving :
    ¬ ∀ left right : BitState 4,
      Collision.map (stateOr left right) =
        stateOr (Collision.map left) (Collision.map right) := by
  intro preserves
  have equality := preserves singletonB singletonC
  exact (by decide :
    Collision.map (stateOr singletonB singletonC) ≠
      stateOr (Collision.map singletonB) (Collision.map singletonC)) equality

private theorem wirePerm_unionPreserving (permutation : WirePerm 4)
    (left right : BitState 4) :
    WirePerm.onState permutation (stateOr left right) =
      stateOr (WirePerm.onState permutation left) (WirePerm.onState permutation right) := by
  funext wire
  rfl

/-- No bare structural wire permutation realizes the selected collision map. -/
theorem no_wirePerm_collision :
    ¬ ∃ permutation : WirePerm 4, WirePerm.onState permutation = Collision.equiv := by
  rintro ⟨permutation, equality⟩
  apply collision_not_unionPreserving
  intro left right
  change Collision.equiv (stateOr left right) =
    stateOr (Collision.equiv left) (Collision.equiv right)
  rw [← equality]
  exact wirePerm_unionPreserving permutation left right

/-! ## Sampled mirrors, timing, and clearance -/

example (mirror : Grid.Mirror) (direction : Grid.Direction) :
    mirror.reflect (mirror.reflect direction) = direction :=
  mirror.reflect_involutive direction

example : Grid.Mirror.reflect .horizontal (Grid.mirrorTurn.direction 0) =
    Grid.mirrorTurn.direction 1 := Grid.mirrorTurn_reflects

example : (Grid.fourTickDetour.start, Grid.fourTickDetour.finish) =
    (Grid.shortRoute.start, Grid.shortRoute.finish) :=
  Grid.fourTickDetour_same_endpoints

example : Grid.shortRoute.direction 0 = .northeast ∧
    Grid.shortRoute.direction 1 = .southeast ∧
      Grid.fourTickDetour.direction 0 = .northwest ∧
        Grid.fourTickDetour.direction 5 = .southwest :=
  Grid.fourTickDetour_boundaryDirections

example (turn : Fin 5) :
    (Grid.fourTickDetourMirrors turn).reflect
        (Grid.fourTickDetour.direction turn.castSucc) =
      Grid.fourTickDetour.direction turn.succ :=
  Grid.fourTickDetour_reflects turn

example : Function.Injective
    Grid.fourTickDetourTurnPoint :=
  Grid.fourTickDetour_turnPoints_injective

example : ¬ Grid.TimedUse.ConflictFree
    ⟨Grid.northeastCrossing, 0⟩ ⟨Grid.southeastCrossing, 0⟩ :=
  Grid.simultaneous_crossing_conflict

example : Grid.TimedUse.ConflictFree
    ⟨Grid.northeastCrossing, 0⟩ ⟨Grid.southeastCrossing, 1⟩ :=
  Grid.oneTickStagger_sampleConflictFree

example : ¬ Grid.TimedUse.HasSampleClearance 2
    ⟨Grid.northeastCrossing, 0⟩ ⟨Grid.southeastCrossing, 1⟩ :=
  Grid.oneTickStagger_not_sampleClearance

example : Grid.TimedUse.HasSampleClearance 2
    ⟨Grid.northeastCrossing, 0⟩ ⟨Grid.southeastCrossing, 2⟩ :=
  Grid.twoTickStagger_sampleClearance

example : Grid.TimedUse.ConflictFree
    ⟨Grid.northeastCrossing, 0⟩ ⟨Grid.southeastCrossing, 2⟩ :=
  Grid.twoTickStagger_sampleConflictFree

/-- Distinct sampled centers need not meet the radius-derived squared threshold two. -/
theorem distinct_not_sampleClear :
    let left : Grid.Point := ⟨0, 0⟩
    let right : Grid.Point := ⟨1, 0⟩
    left ≠ right ∧ ¬ 2 ≤ left.squaredDistance right := by
  decide

/-! ## Figure 14 complete sampled refinement -/

example : Figure14.observeOutput (Figure14.frame false false 4) =
    Interaction.output false false false false := by decide

example : Figure14.observeOutput (Figure14.frame false true 4) =
    Interaction.output false true false false := by decide

example : Figure14.observeOutput (Figure14.frame true false 4) =
    Interaction.output false false true false := by decide

example : Figure14.observeOutput (Figure14.frame true true 4) =
    Interaction.output true false false true := by decide

example (p q : Bool) : Figure14.observeOutput (Figure14.frame p q 4) =
    Collision.map (Collision.embed (Interaction.input p q)) :=
  Figure14.output_refines_collision p q

example (p q : Bool) (time : Fin (Figure14.latency + 1)) :
    (Figure14.frame p q time).ballCount =
      hammingWeight (Interaction.input p q) :=
  Figure14.frame_ballCount p q time

example (p q : Bool) (time : Fin (Figure14.latency + 1)) :
    Grid.Frame.HasSampleClearance 2 (Figure14.frame p q time) :=
  Figure14.sampled_clearance p q time

example : Grid.Point.squaredDistance
    (Figure14.pDeflected.position 2) (Figure14.qDeflected.position 2) = 2 :=
  Figure14.contact_sample

example (time : Fin (Figure14.latency + 1)) :
    Grid.Point.squaredDistance
        (Figure14.pDeflected.position time) (Figure14.qDeflected.position time) = 2 ↔
      time = 2 :=
  Figure14.contact_sample_iff time

example (p q : Bool) :
    Figure14.HasRightAngleTurnAtTwo (Figure14.pRoute q) (Figure14.qRoute p) ↔
      p = true ∧ q = true :=
  Figure14.rightAngleTurn_iff p q

#print axioms ConservativeLogic.Billiard.Interaction.equiv
#print axioms ConservativeLogic.Billiard.Interaction.encode_weightPreserving
#print axioms ConservativeLogic.Billiard.Switch.equiv
#print axioms ConservativeLogic.Billiard.Switch.encode_weightPreserving
#print axioms ConservativeLogic.Billiard.Collision.allowedEquiv
#print axioms ConservativeLogic.Billiard.ScatteringLayer.Configuration.totalBallCount_step
#print axioms ConservativeLogic.Billiard.Grid.twoTickStagger_sampleClearance
#print axioms ConservativeLogic.Billiard.Figure14.output_refines_collision
#print axioms ConservativeLogic.Billiard.Figure14.sampled_clearance

end ConservativeLogic.Audit.Billiard
