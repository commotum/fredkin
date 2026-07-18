import Mathlib.GroupTheory.Perm.ClosureSwap
import ConservativeLogic.Completeness.Semantic

/-!
# Clean Fredkin-basis synthesis

This module proves the fixed-basis half of finite conservative completeness.
The permitted syntax is the paper's zero-controlled Fredkin gate together with
identity, serial/tensor composition, and explicit structural wire
reindexing.  Structural reindexing is an admitted routing convention; it is
not claimed to be a physical Fredkin network.

Ancillas are explicit, may contain both zeroes and ones, and are returned
bit-for-bit.  The construction is finite and classical.  It does not claim an
optimal ancillary width, an all-zero initialization, or a physical cost bound.
-/

namespace ConservativeLogic

namespace Circuit

/-- Syntax certificate for the fixed Fredkin-plus-structural-reindexing basis. -/
def FredkinStructural : {width : Nat} → Circuit width → Prop
  | _, .identity _ => True
  | _, .unitWire => False
  | _, .fredkin => True
  | _, .permute _ => True
  | _, .seq first second => FredkinStructural first ∧ FredkinStructural second
  | _, .tensor left right => FredkinStructural left ∧ FredkinStructural right

@[simp] theorem fredkinStructural_identity (width : Nat) :
    FredkinStructural (.identity width) := trivial

@[simp] theorem fredkinStructural_fredkin :
    FredkinStructural .fredkin := trivial

@[simp] theorem fredkinStructural_permute {width : Nat} (wiring : WirePerm width) :
    FredkinStructural (.permute wiring) := trivial

@[simp] theorem fredkinStructural_seq {width : Nat} (first second : Circuit width) :
    FredkinStructural (.seq first second) ↔
      FredkinStructural first ∧ FredkinStructural second :=
  Iff.rfl

@[simp] theorem fredkinStructural_tensor {m n : Nat}
    (left : Circuit m) (right : Circuit n) :
    FredkinStructural (.tensor left right) ↔
      FredkinStructural left ∧ FredkinStructural right :=
  Iff.rfl

@[simp] theorem fredkinStructural_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth) :
    FredkinStructural (Simulation.castCircuit width circuit) ↔
      FredkinStructural circuit := by
  cases width
  rfl

@[simp] theorem fredkinStructural_inverse {width : Nat} (circuit : Circuit width) :
    FredkinStructural (Circuit.inverse circuit) ↔ FredkinStructural circuit := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => rfl
  | permute wiring => rfl
  | seq first second firstIH secondIH => simp [firstIH, secondIH, and_comm]
  | tensor left right leftIH rightIH => simp [leftIH, rightIH]

end Circuit

/--
A circuit realization with one explicit ancillary prefix returned exactly.
The data block follows the ancillary block at both boundaries.
-/
structure CleanFredkinRealization {width : Nat} (gate : Reversible width) where
  ancillaWidth : Nat
  ancillaInit : BitState ancillaWidth
  circuit : Circuit (ancillaWidth + width)
  structural : Circuit.FredkinStructural circuit
  latencyZero : Circuit.HasLatency circuit 0
  realizes : ∀ state,
    Circuit.eval circuit (BitState.append ancillaInit state) =
      BitState.append ancillaInit (gate state)

/-- Existence of some finite, exactly returned clean ancillary prefix. -/
def CleanFredkinRealizable {width : Nat} (gate : Reversible width) : Prop :=
  Nonempty (CleanFredkinRealization gate)

namespace CleanFredkinRealization

/-- The identity permutation needs no ancillary wires. -/
def identity (width : Nat) :
    CleanFredkinRealization (Reversible.identity width) where
  ancillaWidth := 0
  ancillaInit := fun index => Fin.elim0 index
  circuit := .identity (0 + width)
  structural := trivial
  latencyZero := Circuit.hasLatency_identity _
  realizes _ := rfl

/-- A clean realization remains clean after structural circuit inversion. -/
def inverse {width : Nat} {gate : Reversible width}
    (realization : CleanFredkinRealization gate) :
    CleanFredkinRealization gate.symm where
  ancillaWidth := realization.ancillaWidth
  ancillaInit := realization.ancillaInit
  circuit := Circuit.inverse realization.circuit
  structural := (Circuit.fredkinStructural_inverse realization.circuit).2
    realization.structural
  latencyZero := Circuit.HasLatency.inverse realization.latencyZero
  realizes state := by
    have forward := realization.realizes (gate.symm state)
    have forward' :
        Circuit.eval realization.circuit
            (BitState.append realization.ancillaInit (gate.symm state)) =
          BitState.append realization.ancillaInit state := by
      simpa using forward
    rw [← forward']
    exact Circuit.eval_inverse_eval realization.circuit _

private def emptyState : BitState 0 := fun index => Fin.elim0 index

@[simp] private theorem append_emptyState {width : Nat} (state : BitState width) :
    BitState.append state emptyState = state := by
  funext index
  refine Fin.addCases ?_ (fun impossible => Fin.elim0 impossible) index
  intro inner
  simp

private def firstRoute (firstAncilla secondAncilla width : Nat) :
    Circuit ((firstAncilla + secondAncilla) + (width + 0)) :=
  .permute
    (Simulation.middleSwapWiring firstAncilla secondAncilla width 0)

private theorem firstRoute_spec {firstAncilla secondAncilla width : Nat}
    (firstInit : BitState firstAncilla)
    (secondInit : BitState secondAncilla) (state : BitState width) :
    Circuit.eval (firstRoute firstAncilla secondAncilla width)
        (BitState.append (BitState.append firstInit secondInit)
          (BitState.append state emptyState)) =
      Realization.castState
        (by ac_rfl :
          (firstAncilla + width) + (secondAncilla + 0) =
            (firstAncilla + secondAncilla) + (width + 0))
        (BitState.append (BitState.append firstInit state)
          (BitState.append secondInit emptyState)) := by
  exact Simulation.middleSwapWiring_on_append
    firstInit secondInit state emptyState

private def firstLayer {width : Nat} {firstGate : Reversible width}
    (first : CleanFredkinRealization firstGate) (secondAncilla : Nat) :
    Circuit ((first.ancillaWidth + secondAncilla) + (width + 0)) :=
  Simulation.castCircuit
    (by ac_rfl :
      (first.ancillaWidth + width) + (secondAncilla + 0) =
        (first.ancillaWidth + secondAncilla) + (width + 0))
    (.tensor first.circuit (.identity (secondAncilla + 0)))

private theorem firstLayer_spec {width secondAncilla : Nat}
    {firstGate : Reversible width}
    (first : CleanFredkinRealization firstGate)
    (secondInit : BitState secondAncilla) (state : BitState width) :
    Circuit.eval (firstLayer first secondAncilla)
        (Circuit.eval
          (firstRoute first.ancillaWidth secondAncilla width)
          (BitState.append (BitState.append first.ancillaInit secondInit)
            (BitState.append state emptyState))) =
      Circuit.eval
        (firstRoute first.ancillaWidth secondAncilla width)
        (BitState.append (BitState.append first.ancillaInit secondInit)
          (BitState.append (firstGate state) emptyState)) := by
  rw [firstRoute_spec]
  rw [firstLayer, Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    first.realizes, Circuit.eval_identity]
  exact firstRoute_spec first.ancillaInit secondInit (firstGate state) |>.symm

private def secondLayer {width : Nat} {secondGate : Reversible width}
    (firstAncilla : Nat) (second : CleanFredkinRealization secondGate) :
    Circuit ((firstAncilla + second.ancillaWidth) + (width + 0)) :=
  Simulation.castCircuit
    (by ac_rfl :
      firstAncilla + (second.ancillaWidth + width) =
        (firstAncilla + second.ancillaWidth) + (width + 0))
    (.tensor (.identity firstAncilla) second.circuit)

private theorem secondLayer_spec {width firstAncilla : Nat}
    {secondGate : Reversible width}
    (firstInit : BitState firstAncilla)
    (second : CleanFredkinRealization secondGate) (state : BitState width) :
    Circuit.eval (secondLayer firstAncilla second)
        (BitState.append (BitState.append firstInit second.ancillaInit)
          (BitState.append state emptyState)) =
      BitState.append (BitState.append firstInit second.ancillaInit)
        (BitState.append (secondGate state) emptyState) := by
  unfold secondLayer
  rw [show
      BitState.append (BitState.append firstInit second.ancillaInit)
          (BitState.append state emptyState) =
        Realization.castState
          (by ac_rfl :
            firstAncilla + (second.ancillaWidth + width) =
              (firstAncilla + second.ancillaWidth) + (width + 0))
          (BitState.append firstInit
            (BitState.append second.ancillaInit state)) by
      funext index
      simp [Realization.castState]]
  rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    Circuit.eval_identity, second.realizes]
  funext index
  simp [Realization.castState]

/--
Serially compose two clean realizations.  Their independently initialized
ancillary blocks are both retained, and structural routing brings the data
next to the first block only while its circuit runs.
-/
def comp {width : Nat} {firstGate secondGate : Reversible width}
    (first : CleanFredkinRealization firstGate)
    (second : CleanFredkinRealization secondGate) :
    CleanFredkinRealization (firstGate.trans secondGate) where
  ancillaWidth := first.ancillaWidth + second.ancillaWidth
  ancillaInit := BitState.append first.ancillaInit second.ancillaInit
  circuit := .seq
    (firstRoute first.ancillaWidth second.ancillaWidth width)
    (.seq (firstLayer first second.ancillaWidth)
      (.seq
        (Circuit.inverse
          (firstRoute first.ancillaWidth second.ancillaWidth width))
        (secondLayer first.ancillaWidth second)))
  structural := by
    simp [firstRoute, firstLayer, secondLayer,
      first.structural, second.structural]
  latencyZero := by
    have routeTimed : Circuit.HasLatency
        (firstRoute first.ancillaWidth second.ancillaWidth width) 0 :=
      Circuit.hasLatency_permute _
    have firstTimed : Circuit.HasLatency
        (firstLayer first second.ancillaWidth) 0 := by
      apply Ancilla.hasLatency_castCircuit_zero
      exact Circuit.HasLatency.tensor first.latencyZero
        (Circuit.hasLatency_identity _)
    have secondTimed : Circuit.HasLatency
        (secondLayer first.ancillaWidth second) 0 := by
      apply Ancilla.hasLatency_castCircuit_zero
      exact Circuit.HasLatency.tensor (Circuit.hasLatency_identity _)
        second.latencyZero
    have inverseRouteTimed : Circuit.HasLatency
        (Circuit.inverse
          (firstRoute first.ancillaWidth second.ancillaWidth width)) 0 :=
      Circuit.HasLatency.inverse routeTimed
    have tailTimed := Circuit.HasLatency.seq inverseRouteTimed secondTimed
    have middleTimed := Circuit.HasLatency.seq firstTimed tailTimed
    have allTimed := Circuit.HasLatency.seq routeTimed middleTimed
    simpa using allTimed
  realizes state := by
    change Circuit.eval _
        (BitState.append
          (BitState.append first.ancillaInit second.ancillaInit) state) = _
    have appendEmpty (value : BitState width) :
        BitState.append
            (BitState.append first.ancillaInit second.ancillaInit) value =
          BitState.append
            (BitState.append first.ancillaInit second.ancillaInit)
            (BitState.append value emptyState) := by
      rw [append_emptyState]
    rw [appendEmpty state]
    simp only [Circuit.eval_seq]
    rw [firstLayer_spec]
    rw [← firstRoute_spec first.ancillaInit second.ancillaInit
      (firstGate state)]
    rw [Circuit.eval_inverse_eval]
    rw [secondLayer_spec]
    rw [← appendEmpty (secondGate (firstGate state))]
    rfl

end CleanFredkinRealization

end ConservativeLogic
