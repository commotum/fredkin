import ConservativeLogic.Simulation.Source
import ConservativeLogic.Realization.Primitive
import ConservativeLogic.Circuit.Timed

/-!
# Constructive Fredkin simulation of finite source circuits

Every source-language node is compiled to the fixed target `Circuit` grammar.
The construction exposes its complete initialized source and complete garbage
function.  Serial compilation retains earlier garbage untouched; tensor
compilation uses proved structural permutations to keep its two inputs
disjoint.  No scratch wire, arbitrary target equivalence, semantic gate,
implicit FAN-OUT, or discard is introduced.

The result is a static theorem for the explicitly generated feed-forward
source language.  Target `WirePerm` nodes remain an admitted zero-delay
structural reindexing resource, so this is Fredkin-plus-reindexing simulation,
not pure physical Fredkin synthesis or a sequential-network theorem.
-/

namespace ConservativeLogic.Simulation

open Realization
open Realization.Primitive

namespace SourceCircuit

/-- Fixed source width used by the selected recursive compilation. -/
def sourceWidth : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → Nat
  | _, _, .identity _ => 0
  | _, _, .permute _ => 0
  | _, outputWidth, .constant _ => outputWidth
  | _, _, .discard _ => 0
  | _, _, .andGate => 1
  | _, _, .orGate => 1
  | _, _, .notGate => 2
  | _, _, .fanout => 2
  | _, _, .seq first second => sourceWidth second + sourceWidth first
  | _, _, .tensor left right => sourceWidth left + sourceWidth right

/-- Complete garbage width used by the selected recursive compilation. -/
def garbageWidth : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → Nat
  | _, _, .identity _ => 0
  | _, _, .permute _ => 0
  | _, _, .constant _ => 0
  | _, _, .discard inputWidth => inputWidth
  | _, _, .andGate => 2
  | _, _, .orGate => 2
  | _, _, .notGate => 2
  | _, _, .fanout => 1
  | _, _, .seq first second => garbageWidth second + garbageWidth first
  | _, _, .tensor left right => garbageWidth left + garbageWidth right

/-- Exact boundary-width balance for every source term. -/
theorem source_garbage_balance {inputWidth outputWidth : Nat}
    (circuit : SourceCircuit inputWidth outputWidth) :
    sourceWidth circuit + inputWidth = outputWidth + garbageWidth circuit := by
  induction circuit with
  | identity width => simp [sourceWidth, garbageWidth]
  | permute wiring => simp [sourceWidth, garbageWidth]
  | constant value => simp [sourceWidth, garbageWidth]
  | discard width => simp [sourceWidth, garbageWidth]
  | andGate => rfl
  | orGate => rfl
  | notGate => rfl
  | fanout => rfl
  | seq first second firstIH secondIH =>
      simp only [sourceWidth, garbageWidth]
      calc
        (sourceWidth second + sourceWidth first) + _ =
            sourceWidth second + (sourceWidth first + _) := Nat.add_assoc ..
        _ = sourceWidth second + (_ + garbageWidth first) :=
          congrArg (sourceWidth second + ·) firstIH
        _ = (sourceWidth second + _) + garbageWidth first := (Nat.add_assoc ..).symm
        _ = (_ + garbageWidth second) + garbageWidth first :=
          congrArg (· + garbageWidth first) secondIH
        _ = _ + (garbageWidth second + garbageWidth first) := Nat.add_assoc ..
  | tensor left right leftIH rightIH =>
      simp only [sourceWidth, garbageWidth]
      calc
        (sourceWidth left + sourceWidth right) + (_ + _) =
            (sourceWidth left + _) + (sourceWidth right + _) := by ac_rfl
        _ = (_ + garbageWidth left) + (_ + garbageWidth right) :=
          congrArg₂ Nat.add leftIH rightIH
        _ = (_ + _) + (garbageWidth left + garbageWidth right) := by ac_rfl

/-- Complete fixed source state, independent of the circuit argument. -/
def sourceState : {inputWidth outputWidth : Nat} →
    (circuit : SourceCircuit inputWidth outputWidth) → BitState (sourceWidth circuit)
  | _, _, .identity _ => noBits
  | _, _, .permute _ => noBits
  | _, _, .constant value => value
  | _, _, .discard _ => noBits
  | _, _, .andGate => andSource
  | _, _, .orGate => orSource
  | _, _, .notGate => notFanoutSource
  | _, _, .fanout => notFanoutSource
  | _, _, .seq first second => BitState.append (sourceState second) (sourceState first)
  | _, _, .tensor left right => BitState.append (sourceState left) (sourceState right)

/-- Complete final garbage state as a function of the original argument. -/
def garbage : {inputWidth outputWidth : Nat} →
    (circuit : SourceCircuit inputWidth outputWidth) →
    BitState inputWidth → BitState (garbageWidth circuit)
  | _, _, .identity _, _ => noBits
  | _, _, .permute _, _ => noBits
  | _, _, .constant _, _ => noBits
  | _, _, .discard _, input => input
  | _, _, .andGate, input => andGarbage input
  | _, _, .orGate, input => orGarbage input
  | _, _, .notGate, input => notGarbage input
  | _, _, .fanout, input => fanoutGarbage input
  | _, _, .seq first second, input =>
      BitState.append (garbage second (eval first input)) (garbage first input)
  | _, _, .tensor left right, input =>
      BitState.append
        (garbage left (BitState.split _ _ input).1)
        (garbage right (BitState.split _ _ input).2)

/-- The exhaustive zero-scratch layout selected by the compiler. -/
def simulationLayout {inputWidth outputWidth : Nat}
    (circuit : SourceCircuit inputWidth outputWidth) : Layout where
  sourceWidth := sourceWidth circuit
  scratchWidth := 0
  argumentWidth := inputWidth
  resultWidth := outputWidth
  garbageWidth := garbageWidth circuit
  balanced := source_garbage_balance circuit

end SourceCircuit

/-! ## Width transport and explicit structural block routing -/

/-- Dependent width transport for target syntax; it changes no wire order. -/
def castCircuit {leftWidth rightWidth : Nat} (width : leftWidth = rightWidth)
    (circuit : Circuit leftWidth) : Circuit rightWidth :=
  width ▸ circuit

/-- Circuit evaluation commutes exactly with width transport. -/
theorem eval_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth)
    (input : BitState leftWidth) :
    Circuit.eval (castCircuit width circuit) (castState width input) =
      castState width (Circuit.eval circuit input) := by
  cases width
  rfl

private def fourDecompose (a b c d : Nat) :
    Fin ((a + b) + (c + d)) ≃ (Fin a ⊕ Fin b) ⊕ (Fin c ⊕ Fin d) :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm)

private def fourCompose (a b c d : Nat) :
    (Fin a ⊕ Fin b) ⊕ (Fin c ⊕ Fin d) ≃ Fin ((a + b) + (c + d)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- Actively exchange the middle two of four adjacent ordered wire blocks. -/
def middleSwapWiring (a b c d : Nat) : WirePerm ((a + b) + (c + d)) :=
  (fourDecompose a b c d).trans <|
    (Equiv.sumSumSumComm (Fin a) (Fin b) (Fin c) (Fin d)).trans <|
      (fourCompose a c b d).trans <|
        Equiv.cast (congrArg Fin (by ac_rfl :
          (a + c) + (b + d) = (a + b) + (c + d)))

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

private theorem cast_self {α : Sort _} (proof : α = α) (value : α) :
    cast proof value = value := by
  have proof_eq : proof = rfl := Subsingleton.elim _ _
  rw [proof_eq]
  rfl

private theorem fin_val_cast {leftWidth rightWidth : Nat}
    (proof : Fin leftWidth = Fin rightWidth) (index : Fin leftWidth) :
    (cast proof index).val = index.val := by
  cases proof
  rfl

/-- The active middle-block permutation has the stated four-block action. -/
theorem middleSwapWiring_on_append {a b c d : Nat}
    (as : BitState a) (bs : BitState b) (cs : BitState c) (ds : BitState d) :
    WirePerm.onState (middleSwapWiring a b c d)
        (BitState.append (BitState.append as bs) (BitState.append cs ds)) =
      castState (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d))
        (BitState.append (BitState.append as cs) (BitState.append bs ds)) := by
  funext output
  obtain ⟨input, rfl⟩ := (middleSwapWiring a b c d).surjective output
  rw [WirePerm.onState_apply_image, castState_apply]
  let tagged := fourDecompose a b c d input
  have taggedBack : (fourDecompose a b c d).symm tagged = input := by
    simp [tagged]
  rcases tagged with ((index | index) | (index | index))
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.castAdd b index))) =
          Fin.castAdd (b + d) (Fin.castAdd c index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
      generalize_proofs h
      rw [fin_val_cast h]
      rfl
    rw [route]
    simp
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.natAdd a index))) =
          Fin.natAdd (a + c) (Fin.castAdd d index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
      generalize_proofs h
      rw [fin_val_cast h]
      rfl
    rw [route]
    simp
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.castAdd d index))) =
          Fin.castAdd (b + d) (Fin.natAdd a index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
      generalize_proofs h
      rw [fin_val_cast h]
      rfl
    rw [route]
    simp
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.natAdd c index))) =
          Fin.natAdd (a + c) (Fin.natAdd b index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
      generalize_proofs h
      rw [fin_val_cast h]
      rfl
    rw [route]
    simp

end ConservativeLogic.Simulation
