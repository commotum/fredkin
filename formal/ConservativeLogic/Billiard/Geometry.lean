import ConservativeLogic.State.Core
import Mathlib.Tactic.FinCases

/-!
# Directed sampled geometry for the billiard-ball abstraction

This module uses integer coordinates in the square lattice basis rotated by
45 degrees relative to the page in Figures 12--18.  Moving one coordinate by
one is one sampled unit step along one of the four drawn principal directions.
The coordinates and routes are a discrete reconstruction: they do not define
continuous hard-ball motion, swept-volume clearance, elastic impact, or
specular mechanics.

Routes retain direction as well as occupancy.  Timed uses make the paper's
"trivial crossover" obligation explicit: two spatially crossing routes are
safe only after proving that their balls never occupy the crossing at the same
global sample time.
-/

namespace ConservativeLogic.Billiard.Grid

/-- A point in the integer coordinate basis aligned with the two principal paths. -/
structure Point where
  first : Int
  second : Int
deriving DecidableEq, Repr

/-- The four directed nearest-neighbor moves in the rotated lattice. -/
inductive Direction where
  | northeast
  | southeast
  | southwest
  | northwest
deriving DecidableEq, Repr

/-- Advance one sampled lattice step in a directed principal direction. -/
def Point.advance (point : Point) : Direction → Point
  | .northeast => ⟨point.first + 1, point.second⟩
  | .southeast => ⟨point.first, point.second + 1⟩
  | .southwest => ⟨point.first - 1, point.second⟩
  | .northwest => ⟨point.first, point.second - 1⟩

/-- Squared distance in the orthonormal rotated coordinate basis. -/
def Point.squaredDistance (left right : Point) : Int :=
  (left.first - right.first) ^ 2 + (left.second - right.second) ^ 2

/-- A finite directed route with one principal-direction move per tick. -/
structure Route (latency : Nat) where
  position : Fin (latency + 1) → Point
  direction : Fin latency → Direction
  advances : ∀ tick : Fin latency,
    (position tick.castSucc).advance (direction tick) = position tick.succ

namespace Route

/-- The boundary point occupied before the route's first tick. -/
def start {latency : Nat} (route : Route latency) : Point :=
  route.position ⟨0, Nat.zero_lt_succ latency⟩

/-- The boundary point occupied after all of the route's ticks. -/
def finish {latency : Nat} (route : Route latency) : Point :=
  route.position ⟨latency, Nat.lt_succ_self latency⟩

end Route

/-- Axis orientation for a fixed mirror in the sampled direction abstraction. -/
inductive Mirror where
  | horizontal
  | vertical
deriving DecidableEq, Repr

namespace Mirror

/-- Direction permutation induced by the selected axis-mirror abstraction. -/
def reflect : Mirror → Direction → Direction
  | .horizontal, .northeast => .southeast
  | .horizontal, .southeast => .northeast
  | .horizontal, .southwest => .northwest
  | .horizontal, .northwest => .southwest
  | .vertical, .northeast => .northwest
  | .vertical, .northwest => .northeast
  | .vertical, .southeast => .southwest
  | .vertical, .southwest => .southeast

/-- Each fixed sampled mirror reflection is its own selected inverse. -/
theorem reflect_involutive (mirror : Mirror) : Function.Involutive mirror.reflect := by
  intro direction
  cases mirror <;> cases direction <;> rfl

/-- Bundled direction equivalence for a fixed sampled mirror. -/
def reflectEquiv (mirror : Mirror) : Direction ≃ Direction where
  toFun := mirror.reflect
  invFun := mirror.reflect
  left_inv := mirror.reflect_involutive
  right_inv := mirror.reflect_involutive

end Mirror

/-- A two-tick route with one horizontal-mirror direction change. -/
def mirrorTurn : Route 2 where
  position
    | ⟨0, _⟩ => ⟨0, -1⟩
    | ⟨1, _⟩ => ⟨1, -1⟩
    | ⟨2, _⟩ => ⟨1, 0⟩
  direction
    | ⟨0, _⟩ => .northeast
    | ⟨1, _⟩ => .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The concrete route's direction change agrees with horizontal reflection. -/
theorem mirrorTurn_reflects :
    Mirror.reflect .horizontal (mirrorTurn.direction 0) = mirrorTurn.direction 1 := rfl

/-- A direct two-tick route between the endpoints used by `fourTickDetour`. -/
def shortRoute : Route 2 where
  position
    | ⟨0, _⟩ => ⟨0, 0⟩
    | ⟨1, _⟩ => ⟨1, 0⟩
    | ⟨2, _⟩ => ⟨1, 1⟩
  direction
    | ⟨0, _⟩ => .northeast
    | ⟨1, _⟩ => .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- A fixed mirror detour with the same endpoints and four additional ticks. -/
def fourTickDetour : Route 6 where
  position
    | ⟨0, _⟩ => ⟨0, 0⟩
    | ⟨1, _⟩ => ⟨1, 0⟩
    | ⟨2, _⟩ => ⟨1, -1⟩
    | ⟨3, _⟩ => ⟨0, -1⟩
    | ⟨4, _⟩ => ⟨0, 0⟩
    | ⟨5, _⟩ => ⟨1, 0⟩
    | ⟨6, _⟩ => ⟨1, 1⟩
  direction
    | ⟨0, _⟩ => .northeast
    | ⟨1, _⟩ => .northwest
    | ⟨2, _⟩ => .southwest
    | ⟨3, _⟩ => .southeast
    | ⟨4, _⟩ => .northeast
    | ⟨5, _⟩ => .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- The detour and the short route have the same ordered boundary points. -/
theorem fourTickDetour_same_endpoints :
    (fourTickDetour.start, fourTickDetour.finish) =
      (shortRoute.start, shortRoute.finish) := rfl

/-- The selected detour adds exactly four sampled ticks. -/
theorem fourTickDetour_extra_latency : 6 = 2 + 4 := rfl

/-- A route crossing the origin in the northeast direction. -/
def northeastCrossing : Route 2 where
  position
    | ⟨0, _⟩ => ⟨-1, 0⟩
    | ⟨1, _⟩ => ⟨0, 0⟩
    | ⟨2, _⟩ => ⟨1, 0⟩
  direction _ := .northeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- A route crossing the origin in the southeast direction. -/
def southeastCrossing : Route 2 where
  position
    | ⟨0, _⟩ => ⟨0, -1⟩
    | ⟨1, _⟩ => ⟨0, 0⟩
    | ⟨2, _⟩ => ⟨0, 1⟩
  direction _ := .southeast
  advances := by
    intro tick
    fin_cases tick <;> rfl

/-- A route together with the global sample time at which it begins. -/
structure TimedUse (latency : Nat) where
  route : Route latency
  startTime : Nat

/-- Two timed routes are sample-conflict-free when shared coordinates never occur together. -/
def TimedUse.ConflictFree {leftLatency rightLatency : Nat}
    (left : TimedUse leftLatency) (right : TimedUse rightLatency) : Prop :=
  ∀ leftTick rightTick,
    left.startTime + leftTick.val = right.startTime + rightTick.val →
      left.route.position leftTick ≠ right.route.position rightTick

/-- Simultaneously used naked crossing paths conflict at the origin. -/
theorem simultaneous_crossing_conflict :
    ¬ TimedUse.ConflictFree
      ⟨northeastCrossing, 0⟩ ⟨southeastCrossing, 0⟩ := by
  intro clear
  exact clear 1 1 rfl rfl

/-- A one-tick offset makes these particular sampled crossing uses conflict-free. -/
theorem staggered_crossing_clear :
    TimedUse.ConflictFree
      ⟨northeastCrossing, 0⟩ ⟨southeastCrossing, 1⟩ := by
  intro leftTick rightTick
  fin_cases leftTick <;> fin_cases rightTick <;> decide

/-- A fixed number of optional labeled particles at one integral sample. -/
abbrev Frame (slots : Nat) := Fin slots → Option Point

namespace Frame

/-- Number of particles present in a sampled frame. -/
def ballCount {slots : Nat} (frame : Frame slots) : Nat :=
  (Finset.univ.filter fun slot => (frame slot).isSome).card

/-- Pairwise squared-distance lower bound at one integral sample only. -/
def HasSampleClearance {slots : Nat} (minimumSquared : Int)
    (frame : Frame slots) : Prop :=
  ∀ left right, left ≠ right →
    match frame left, frame right with
    | some leftPoint, some rightPoint =>
        minimumSquared ≤ leftPoint.squaredDistance rightPoint
    | _, _ => True

end Frame

end ConservativeLogic.Billiard.Grid
