import ConservativeLogic.Billiard.Geometry
import ConservativeLogic.Billiard.Collision
import Mathlib.Tactic.FinCases

/-!
# Figure 14 sampled interaction layout

This module gives one explicit coordinate reconstruction of Figure 14 in the
rotated integer basis from `Billiard.Geometry`.  Inputs `P,Q` lie on one
left-hand sample line and outputs `A,B,C,D` on one right-hand sample line.
Every active ball takes four directed nearest-neighbor steps.  A lone ball
continues straight; when both are active, their directions change at the
sampled contact configuration.

The main theorem observes the complete final frame after exactly four ticks
and recovers the paper's constrained interaction output.  This is a certified
sampled trajectory, not a continuous elastic-collision or swept-clearance
theorem, and four ticks is specific to this Figure 14 reconstruction.
-/

namespace ConservativeLogic.Billiard.Figure14

open Grid

/-- The numerical latency stated for the particular Figure 14 example. -/
abbrev latency : Nat := 4

/-- Upper input port `P`. -/
def pointP : Point := ⟨0, -2⟩

/-- Lower input port `Q`. -/
def pointQ : Point := ⟨-3, 1⟩

/-- Outer upper output port `A`. -/
def pointA : Point := ⟨2, 0⟩

/-- Inner upper output port `B`. -/
def pointB : Point := ⟨1, 1⟩

/-- Inner lower output port `C`. -/
def pointC : Point := ⟨0, 2⟩

/-- Outer lower output port `D`. -/
def pointD : Point := ⟨-1, 3⟩

/-- The upper ball's straight southeast path from `P` to `C`. -/
def pStraight : Route latency where
  position
    | ⟨0, _⟩ => pointP
    | ⟨1, _⟩ => ⟨0, -1⟩
    | ⟨2, _⟩ => ⟨0, 0⟩
    | ⟨3, _⟩ => ⟨0, 1⟩
    | ⟨4, _⟩ => pointC
  direction _ := .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The lower ball's straight northeast path from `Q` to `B`. -/
def qStraight : Route latency where
  position
    | ⟨0, _⟩ => pointQ
    | ⟨1, _⟩ => ⟨-2, 1⟩
    | ⟨2, _⟩ => ⟨-1, 1⟩
    | ⟨3, _⟩ => ⟨0, 1⟩
    | ⟨4, _⟩ => pointB
  direction _ := .northeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The upper ball's collision-deflected path from `P` to `A`. -/
def pDeflected : Route latency where
  position
    | ⟨0, _⟩ => pointP
    | ⟨1, _⟩ => ⟨0, -1⟩
    | ⟨2, _⟩ => ⟨0, 0⟩
    | ⟨3, _⟩ => ⟨1, 0⟩
    | ⟨4, _⟩ => pointA
  direction
    | ⟨0, _⟩ => .southeast
    | ⟨1, _⟩ => .southeast
    | ⟨2, _⟩ => .northeast
    | ⟨3, _⟩ => .northeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The lower ball's collision-deflected path from `Q` to `D`. -/
def qDeflected : Route latency where
  position
    | ⟨0, _⟩ => pointQ
    | ⟨1, _⟩ => ⟨-2, 1⟩
    | ⟨2, _⟩ => ⟨-1, 1⟩
    | ⟨3, _⟩ => ⟨-1, 2⟩
    | ⟨4, _⟩ => pointD
  direction
    | ⟨0, _⟩ => .northeast
    | ⟨1, _⟩ => .northeast
    | ⟨2, _⟩ => .southeast
    | ⟨3, _⟩ => .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The potential upper trajectory selected by the other input's presence. -/
def pRoute (q : Bool) : Route latency := if q then pDeflected else pStraight

/-- The potential lower trajectory selected by the other input's presence. -/
def qRoute (p : Bool) : Route latency := if p then qDeflected else qStraight

/-- Complete sampled configuration, with one optional slot for each input ball. -/
def frame (p q : Bool) (time : Fin (latency + 1)) : Frame 2
  | ⟨0, _⟩ => if p then some ((pRoute q).position time) else none
  | ⟨1, _⟩ => if q then some ((qRoute p).position time) else none

/-- Complete initial frame before the four sampled moves. -/
def initialFrame (p q : Bool) : Frame 2
  | ⟨0, _⟩ => if p then some pointP else none
  | ⟨1, _⟩ => if q then some pointQ else none

/-- Complete final frame, including both separately tracked optional balls. -/
def finalFrame (p q : Bool) : Frame 2
  | ⟨0, _⟩ => if p then some (if q then pointA else pointC) else none
  | ⟨1, _⟩ => if q then some (if p then pointD else pointB) else none

/-- The sampled trace starts with exactly the two selected input ports. -/
theorem frame_zero (p q : Bool) : frame p q 0 = initialFrame p q := by
  funext slot
  fin_cases slot <;> cases p <;> cases q <;> rfl

/-- The sampled trace ends after four ticks with no unnamed interior ball. -/
theorem frame_four (p q : Bool) : frame p q 4 = finalFrame p q := by
  funext slot
  fin_cases slot <;> cases p <;> cases q <;> rfl

/-- Boolean presence of a point in either labeled particle slot. -/
def present (sample : Frame 2) (point : Point) : Bool :=
  decide (sample 0 = some point) || decide (sample 1 = some point)

/-- Observe the ordered Figure 14 input rails `(P,Q)`. -/
def observeInput (sample : Frame 2) : BitState 2 :=
  Interaction.input (present sample pointP) (present sample pointQ)

/-- Observe the ordered Figure 14 output rails `(A,B,C,D)`. -/
def observeOutput (sample : Frame 2) : BitState 4 :=
  Interaction.output (present sample pointA) (present sample pointB)
    (present sample pointC) (present sample pointD)

/-- The complete initial frame decodes to the supplied interaction input. -/
theorem input_refines (p q : Bool) :
    observeInput (frame p q 0) = Interaction.input p q := by
  cases p <;> cases q <;> decide

/--
After the paper's four ticks, the complete sampled layout refines the exact
constrained interaction table in the stated `A,B,C,D` order.
-/
theorem output_refines (p q : Bool) :
    observeOutput (frame p q 4) = Interaction.encode (Interaction.input p q) := by
  cases p <;> cases q <;> decide

/-- The same endpoint theorem factored through the admitted local collision rule. -/
theorem output_refines_collision (p q : Bool) :
    observeOutput (frame p q 4) =
      Collision.map (Collision.embed (Interaction.input p q)) := by
  rw [Collision.map_embed]
  exact output_refines p q

/-- The Figure 14 observation time is exactly four sampled route steps. -/
theorem exact_latency : latency = 4 := rfl

/-- Every sampled frame has exactly as many active balls as its input. -/
theorem frame_ballCount (p q : Bool) (time : Fin (latency + 1)) :
    (frame p q time).ballCount = hammingWeight (Interaction.input p q) := by
  cases p <;> cases q <;> fin_cases time <;> decide

/--
Every integral frame satisfies the squared-distance threshold `2`.  This is
sampled center clearance only, not a swept-volume or obstacle-clearance fact.
-/
theorem sampled_clearance (p q : Bool) (time : Fin (latency + 1)) :
    Frame.HasSampleClearance 2 (frame p q time) := by
  cases p <;> cases q <;> fin_cases time <;>
    intro left right distinct <;>
    fin_cases left <;> fin_cases right <;>
    simp [frame, pRoute, qRoute, pStraight, qStraight, pDeflected, qDeflected,
      pointP, pointQ, pointA, pointB, pointC, pointD,
      Point.squaredDistance] at distinct ⊢

/-- At the scheduled two-ball turn, the sampled centers have squared distance two. -/
theorem contact_sample :
    Point.squaredDistance (pDeflected.position 2) (qDeflected.position 2) = 2 := rfl

/-- The two-ball trace meets the sampled contact threshold only at tick two. -/
theorem contact_sample_iff (time : Fin (latency + 1)) :
    Point.squaredDistance (pDeflected.position time) (qDeflected.position time) = 2 ↔
      time = 2 := by
  fin_cases time <;> decide

/-- Direction pattern of the selected right-angle scattering event. -/
def HasRightAngleTurnAtTwo (upper lower : Route latency) : Prop :=
  upper.direction 1 = .southeast ∧ lower.direction 1 = .northeast ∧
    upper.direction 2 = .northeast ∧ lower.direction 2 = .southeast ∧
    Point.squaredDistance (upper.position 2) (lower.position 2) = 2

/-- A right-angle direction change is scheduled exactly on the two-ball input row. -/
theorem rightAngleTurn_iff (p q : Bool) :
    HasRightAngleTurnAtTwo (pRoute q) (qRoute p) ↔ p = true ∧ q = true := by
  cases p <;> cases q <;>
    simp [HasRightAngleTurnAtTwo, pRoute, qRoute, pStraight, qStraight,
      pDeflected, qDeflected, Point.squaredDistance]

end ConservativeLogic.Billiard.Figure14
