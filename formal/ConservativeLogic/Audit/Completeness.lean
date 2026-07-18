import ConservativeLogic.API

/-!
# Adversarial audit of finite completeness

This diagnostic leaf exercises the semantic/fixed-basis separation, the two
Fredkin control conventions, canonical and routed state exchanges, exact clean
restoration, width-zero boundaries, Figure 25 with a noninjective function,
and the width-four no-ancilla obstruction.  It is intentionally outside the
public import graph.
-/

namespace ConservativeLogic.Audit.Completeness

open ConservativeLogic
open ConservativeLogic.Ancilla
open ConservativeLogic.Simulation

private def noBits : BitState 0 := fun index => Fin.elim0 index

private def oneBit (value : Bool) : BitState 1 := fun _ => value

private def constantFalse (_ : BitState 1) : BitState 1 := oneBit false

/-! ## Semantic boundary and Figure 25 -/

example : ∃ gate : Conservative (1 + (1 + 1)), ∀ argument,
    gate (BitState.append argument (resultRegisterInput 1)) =
      BitState.append argument (resultRegisterOutput (constantFalse argument)) :=
  exists_figure25_conservative constantFalse

example : ∃ gate : Conservative (1 + (0 + 0)), ∀ argument,
    gate (BitState.append argument (resultRegisterInput 0)) =
      BitState.append argument (resultRegisterOutput noBits) :=
  exists_figure25_conservative (fun _ : BitState 1 => noBits)

example : DirectlyRealizable (id : BitState 0 → BitState 0) := by
  rw [direct_realization_iff]
  exact ⟨IsReversible.identity 0, WeightPreserving.identity 0⟩

example : hammingWeight (pair false true) =
    hammingWeight (pair true false) := by
  decide

example : hammingWeight (oneBit false) ≠
    hammingWeight (oneBit true) := by
  decide

example : ¬ ∃ gate : Conservative 1,
    gate (oneBit false) = oneBit true := by
  rintro ⟨gate, equality⟩
  have preserved := gate.weight_preserving (oneBit false)
  rw [equality] at preserved
  exact (by decide : hammingWeight (oneBit true) ≠
    hammingWeight (oneBit false)) preserved

/-! ## Control convention and explicit pattern marker -/

example : Circuit.eval oneControlledFredkin
    (PaperFredkin.state false true false) =
      PaperFredkin.state false true false := by
  simp

example : Circuit.eval oneControlledFredkin
    (PaperFredkin.state true true false) =
      PaperFredkin.state true false true := by
  simp

example : SourceCircuit.eval (patternMatch (oneBit false)) (oneBit false) 0 = true :=
  (patternMatch_spec (oneBit false) (oneBit false)).2 rfl

example : SourceCircuit.eval (patternMatch (oneBit false)) (oneBit true) 0 = false := by
  have notTrue :
      SourceCircuit.eval (patternMatch (oneBit false)) (oneBit true) 0 ≠ true := by
    intro isTrue
    have equality := (patternMatch_spec (oneBit false) (oneBit true)).1 isTrue
    exact (by decide : oneBit true ≠ oneBit false) equality
  cases value : SourceCircuit.eval (patternMatch (oneBit false)) (oneBit true) 0
  · rfl
  · exact (notTrue value).elim

example : SourceCircuit.eval (patternMatch (oneBit true)) (oneBit true) 0 = true :=
  (patternMatch_spec (oneBit true) (oneBit true)).2 rfl

example : SourceCircuit.eval (patternMatch (oneBit true)) (oneBit false) 0 = false := by
  have notTrue :
      SourceCircuit.eval (patternMatch (oneBit true)) (oneBit false) 0 ≠ true := by
    intro isTrue
    have equality := (patternMatch_spec (oneBit true) (oneBit false)).1 isTrue
    exact (by decide : oneBit false ≠ oneBit true) equality
  cases value : SourceCircuit.eval (patternMatch (oneBit true)) (oneBit false) 0
  · rfl
  · exact (notTrue value).elim

/-! ## Canonical and routed transpositions -/

example : edgeClean noBits 0 = true := by decide

example : edgeClean noBits 1 = false := by decide

example : Circuit.eval (adjacentTranspositionCircuit noBits)
    (BitState.append (edgeClean noBits) (pair false true)) =
      BitState.append (edgeClean noBits) (pair true false) := by
  rw [adjacentTranspositionCircuit_spec]
  rw [show edgeData noBits false true = pair false true by decide]
  rw [show edgeData noBits true false = pair true false by decide]
  rw [Equiv.swap_apply_left]

example : Circuit.eval (adjacentTranspositionCircuit noBits)
    (BitState.append (edgeClean noBits) (pair false false)) =
      BitState.append (edgeClean noBits) (pair false false) := by
  rw [adjacentTranspositionCircuit_spec]
  rw [show edgeData noBits false true = pair false true by decide]
  rw [show edgeData noBits true false = pair true false by decide]
  rw [Equiv.swap_apply_of_ne_of_ne] <;> decide

example : Circuit.eval (adjacentTranspositionCircuit noBits)
    (BitState.append (edgeClean noBits) (pair true false)) =
      BitState.append (edgeClean noBits) (pair false true) := by
  rw [adjacentTranspositionCircuit_spec]
  rw [show edgeData noBits false true = pair false true by decide]
  rw [show edgeData noBits true false = pair true false by decide]
  rw [Equiv.swap_apply_right]

example : WirePerm.onState (Equiv.swap (0 : Fin 2) 1)
    (pair false true) = pair true false := by
  decide

example : CleanFredkinRealizable
    (Equiv.swap (pair false true) (pair true false)) := by
  simpa only [show edgeData noBits false true = pair false true by decide,
    show edgeData noBits true false = pair true false by decide] using
    adjacentTranspositionClean noBits

example : CleanFredkinRealizable
    (Equiv.swap (pair false true)
      (WirePerm.onState (Equiv.swap (0 : Fin 2) 1) (pair false true))) := by
  apply singleExchangeClean (pair false true) _ 0 1
  · decide
  · decide
  · rfl

/-! ## All-width completeness and Figure 25 fixed-basis synthesis -/

example (gate : Conservative 0) : CleanFredkinRealizable gate.toEquiv :=
  fredkin_complete_conservative gate

example (gate : Conservative 1) : CleanFredkinRealizable gate.toEquiv :=
  fredkin_complete_conservative gate

example (gate : Conservative 2) : CleanFredkinRealizable gate.toEquiv :=
  fredkin_complete_conservative gate

example (gate : Conservative 3) : CleanFredkinRealizable gate.toEquiv :=
  fredkin_complete_conservative gate

example (gate : Conservative 4) : CleanFredkinRealizable gate.toEquiv :=
  fredkin_complete_conservative gate

example : ∃ gate : Conservative (1 + (1 + 1)),
    ∃ _realization : CleanFredkinRealization gate.toEquiv, ∀ argument,
      gate (BitState.append argument (resultRegisterInput 1)) =
        BitState.append argument (resultRegisterOutput (constantFalse argument)) :=
  figure25_fredkin_complete constantFalse

example : ¬ Circuit.FredkinStructural Circuit.unitWire := by
  simp [Circuit.FredkinStructural]

/-! ## False no-ancilla reading -/

example (circuit : Circuit 4) :
    Equiv.Perm.sign (Circuit.eval circuit).toEquiv = 1 :=
  circuit_four_even circuit

example : middleLayerSwapConservative middleLayerStateA = middleLayerStateB := by
  simp [middleLayerSwapConservative, middleLayerSwap]

example : middleLayerSwapConservative middleLayerStateB = middleLayerStateA := by
  simp [middleLayerSwapConservative, middleLayerSwap]

example : ¬ ∃ circuit : Circuit 4,
    (Circuit.eval circuit).toEquiv = middleLayerSwap :=
  middleLayerSwap_not_circuit

/-! ## Public surface and axiom audit -/

#check WeightLayer
#check Conservative.onWeightLayer
#check Conservative.ofWeightLayers
#check exists_conservative_extending_pair
#check exists_figure25_conservative
#check direct_realization_iff
#check Circuit.FredkinStructural
#check CleanFredkinRealization
#check adjacentTranspositionCircuit_spec
#check singleExchangeClean
#check Conservative.weightLayer_hammingTwo_connected
#check fredkin_complete_conservative
#check clean_fredkin_realizable_iff
#check figure25_fredkin_complete
#check circuit_four_even
#check middleLayerSwap_not_circuit

#print axioms Conservative.ofWeightLayers
#print axioms exists_conservative_extending_pair
#print axioms exists_figure25_conservative
#print axioms direct_realization_iff
#print axioms adjacentTranspositionCircuit_spec
#print axioms singleExchangeClean
#print axioms Conservative.weightLayer_hammingTwo_connected
#print axioms fredkin_complete_conservative
#print axioms clean_fredkin_realizable_iff
#print axioms figure25_fredkin_complete
#print axioms circuit_four_even
#print axioms middleLayerSwap_not_circuit

end ConservativeLogic.Audit.Completeness
