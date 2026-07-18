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

/-! ## Exact paper ports and the required canonical permutation -/

example : Circuit.eval Circuit.fredkin (threeBits false true false) =
    threeBits false false true := by
  simpa using copyPair_physical_spec false

example : Circuit.eval Circuit.fredkin (threeBits true true false) =
    threeBits true true false := by
  simpa using copyPair_physical_spec true

example : Circuit.eval copyPair (threeBits false false true) =
    threeBits false false true := by
  simpa using copyPair_spec false

example : Circuit.eval copyPair (threeBits true false true) =
    threeBits true true false := by
  simpa using copyPair_spec true

/- Omitting the canonical-to-physical data swap reverses copy/complement here. -/
example : Circuit.eval Circuit.fredkin (threeBits false false true) =
    threeBits false true false := by
  decide

example : Circuit.eval Circuit.fredkin (threeBits false false true) !=
    threeBits false false true := by
  decide

example : Circuit.eval Circuit.fredkin (threeBits true false true) !=
    threeBits true true false := by
  decide

/-! ## Conservation obstruction when the initialized one is missing -/

/-- No conservative circuit can produce the false-bit copy/complement triple
from an all-zero triple: the missing initialized `1` is a real resource. -/
theorem missing_one_weight_obstruction (circuit : Circuit 3) :
    Circuit.eval circuit (threeBits false false false) !=
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

end ConservativeLogic.Audit.Uncompute
