import ConservativeLogic.API

/-!
# Stage 8 compute-copy-uncompute audit

This non-public consumer checks the initialized spy register, explicit block
order, all-width copying, complete compute-copy-uncompute boundary, restored
scratch/source/argument, and exact static resources.  Fixed `decide` proofs
are confined to concrete Boolean rows.  Generic vector, resource, and final
boundary claims are exercised through the public structural theorems.
-/

namespace ConservativeLogic.Audit.Uncompute

open ConservativeLogic.Ancilla
open ConservativeLogic.Realization
open ConservativeLogic.Realization.Primitive
open ConservativeLogic.Simulation

private def noBits : BitState 0 := fun index => Fin.elim0 index

private def oneBit (value : Bool) : BitState 1 := fun _ => value

private def twoBits (first second : Bool) : BitState 2 :=
  BitState.append (oneBit first) (oneBit second)

private def threeBits (first second third : Bool) : BitState 3 :=
  PaperFredkin.state first second third

private theorem twoBits_eta (input : BitState 2) :
    twoBits (input 0) (input 1) = input := by
  funext index
  refine Fin.cases rfl ?_ index
  intro tail
  refine Fin.cases rfl ?_ tail
  intro impossible
  exact Fin.elim0 impossible

private theorem oneBit_eta (input : BitState 1) : oneBit (input 0) = input := by
  funext index
  exact Fin.eq_zero index ▸ rfl

/-! ## Exact paper ports and the required canonical permutation -/

example : Circuit.eval Circuit.fredkin (threeBits false true false) =
    threeBits false false true := by
  simpa only [threeBits] using copyPair_physical_spec false

example : Circuit.eval Circuit.fredkin (threeBits true true false) =
    threeBits true true false := by
  simpa only [threeBits] using copyPair_physical_spec true

example : Circuit.eval copyPair (threeBits false false true) =
    threeBits false false true := by
  simpa only [threeBits] using copyPair_spec false

example : Circuit.eval copyPair (threeBits true false true) =
    threeBits true true false := by
  simpa only [threeBits] using copyPair_spec true

/-- Static copying on the initialized slice is not a syntactic identity term. -/
theorem copyPair_ne_identity : copyPair ≠ Circuit.identity 3 := by
  intro equality
  cases equality

/- Omitting the canonical-to-physical data swap reverses copy/complement here. -/
example : Circuit.eval Circuit.fredkin (threeBits false false true) =
    threeBits false true false := by
  decide

example : Circuit.eval Circuit.fredkin (threeBits false false true) ≠
    threeBits false false true := by
  decide

example : Circuit.eval Circuit.fredkin (threeBits true false true) ≠
    threeBits true true false := by
  decide

/-! ## Conservation obstruction when the initialized one is missing -/

/-- No conservative circuit can produce the false-bit copy/complement triple
from an all-zero triple: the missing initialized `1` is a real resource. -/
theorem missing_one_weight_obstruction (circuit : Circuit 3) :
    Circuit.eval circuit (threeBits false false false) ≠
      threeBits false false true := by
  intro equality
  have preserved := Circuit.eval_weightPreserving circuit
    (threeBits false false false)
  rw [equality] at preserved
  have outputWeight : hammingWeight (threeBits false false true) = 1 := by
    decide
  have inputWeight : hammingWeight (threeBits false false false) = 0 := by
    decide
  rw [outputWeight, inputWeight] at preserved
  omega

/-! ## Register weights, zero width, and asymmetric vector copying -/

example (width : Nat) : hammingWeight (zeroRegister width) = 0 :=
  hammingWeight_zeroRegister width

example (width : Nat) : hammingWeight (oneRegister width) = width :=
  hammingWeight_oneRegister width

example (width : Nat) : hammingWeight (resultRegisterInput width) = width :=
  hammingWeight_resultRegisterInput width

example {width : Nat} (value : BitState width) :
    hammingWeight (resultRegisterOutput value) = width :=
  hammingWeight_resultRegisterOutput value

example : Circuit.eval (copyRegisterCircuit 0)
      (BitState.append noBits (resultRegisterInput 0)) =
    BitState.append noBits (resultRegisterOutput noBits) :=
  copyRegister_spec noBits

private def asymmetricValue : BitState 2 := twoBits true false

example : Circuit.eval (copyRegisterCircuit 2)
      (BitState.append asymmetricValue (resultRegisterInput 2)) =
    BitState.append asymmetricValue (resultRegisterOutput asymmetricValue) :=
  copyRegister_spec asymmetricValue

/- This expanded row catches block exchange as well as copy/complement exchange. -/
example : Circuit.eval (copyRegisterCircuit 2)
      (BitState.append (twoBits true false)
        (BitState.append (twoBits false false) (twoBits true true))) =
    BitState.append (twoBits true false)
      (BitState.append (twoBits true false) (twoBits false true)) := by
  have inputEquality :
      BitState.append (twoBits true false)
          (BitState.append (twoBits false false) (twoBits true true)) =
        BitState.append asymmetricValue (resultRegisterInput 2) := by
    decide
  have outputEquality :
      BitState.append (twoBits true false)
          (BitState.append (twoBits true false) (twoBits false true)) =
        BitState.append asymmetricValue (resultRegisterOutput asymmetricValue) := by
    decide
  rw [inputEquality, outputEquality]
  exact copyRegister_spec asymmetricValue

/-! ## Explicit realization witnesses used by the final-boundary audit -/

/-- OR extended by one genuinely nonzero returned scratch bit.  Its fixed
source has weight one and its one source wire is deliberately not confused
with its two transient-garbage wires. -/
private def scratchOrLayout : Layout where
  sourceWidth := 1
  scratchWidth := 1
  argumentWidth := 2
  resultWidth := 1
  garbageWidth := 2
  balanced := rfl

private def scratchOrScratch : BitState 1 := oneBit true

private def scratchOrCircuit : Circuit scratchOrLayout.width :=
  Circuit.tensor (Circuit.identity 1) fredkinOrCircuit

private theorem scratchOr_complete (first second : Bool) :
    Circuit.eval scratchOrCircuit
        (scratchOrLayout.packInput scratchOrScratch orSource
          (twoBits first second)) =
      scratchOrLayout.packOutput scratchOrScratch
        (orTarget (twoBits first second)) (orGarbage (twoBits first second)) := by
  cases first <;> cases second <;> decide

private theorem scratchOr_realizes :
    Realizes scratchOrLayout scratchOrCircuit scratchOrScratch orSource
      orTarget orGarbage := by
  intro argument
  change BitState 2 at argument
  rw [← twoBits_eta argument]
  exact scratchOr_complete (argument 0) (argument 1)

example : scratchOrLayout.sourceWidth = 1 := rfl
example : scratchOrLayout.garbageWidth = 2 := rfl
example : hammingWeight scratchOrScratch = 1 := by decide
example : hammingWeight orSource = 1 := by decide

/-- A nonempty main register whose selected result has width zero. -/
private def emptyResultLayout : Layout where
  sourceWidth := 0
  scratchWidth := 0
  argumentWidth := 1
  resultWidth := 0
  garbageWidth := 1
  balanced := rfl

private def emptyResultTarget (_ : BitState 1) : BitState 0 := noBits

private def emptyResultGarbage (argument : BitState 1) : BitState 1 := argument

private theorem emptyResult_complete (value : Bool) :
    Circuit.eval (Circuit.identity 1)
        (emptyResultLayout.packInput noBits noBits (oneBit value)) =
      emptyResultLayout.packOutput noBits (emptyResultTarget (oneBit value))
        (emptyResultGarbage (oneBit value)) := by
  cases value <;> decide

private theorem emptyResult_realizes :
    Realizes emptyResultLayout (Circuit.identity 1) noBits noBits
      emptyResultTarget emptyResultGarbage := by
  intro argument
  change BitState 1 at argument
  rw [← oneBit_eta argument]
  exact emptyResult_complete (argument 0)

/- A static identity realization with one positive-delay unit wire. -/
private def unitWireLayout : Layout where
  sourceWidth := 0
  scratchWidth := 0
  argumentWidth := 1
  resultWidth := 1
  garbageWidth := 0
  balanced := rfl

private def unitWireTarget (argument : BitState 1) : BitState 1 := argument

private def unitWireGarbage (_ : BitState 1) : BitState 0 := noBits

private theorem unitWire_realizes :
    Realizes unitWireLayout Circuit.unitWire noBits noBits unitWireTarget
      unitWireGarbage := by
  intro argument
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro impossible
    exact Fin.elim0 impossible

end ConservativeLogic.Audit.Uncompute
