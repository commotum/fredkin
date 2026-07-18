import ConservativeLogic.Circuit.Semantics

/-!
# Structural circuit transport and block routing

This module owns generic structural operations on balanced circuits.  Width
transport changes only the dependent width index, while `middleSwapWiring`
actively exchanges the middle two of four adjacent wire blocks.  Both are
structural operations: they introduce no value-processing gate, copying, or
physical routing claim.
-/

namespace ConservativeLogic.Circuit

open Realization

/-- Circuit evaluation commutes exactly with width transport. -/
theorem eval_cast {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth)
    (input : BitState leftWidth) :
    Circuit.eval (cast width circuit) (castState width input) =
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
        finCongr (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d))

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
  · have input_eq :
        Fin.castAdd (c + d) (Fin.castAdd b index) = input := by
      simpa [fourDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.castAdd b index))) =
          Fin.castAdd (b + d) (Fin.castAdd c index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp
  · have input_eq :
        Fin.castAdd (c + d) (Fin.natAdd a index) = input := by
      simpa [fourDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.natAdd a index))) =
          Fin.natAdd (a + c) (Fin.castAdd d index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp
  · have input_eq :
        Fin.natAdd (a + b) (Fin.castAdd d index) = input := by
      simpa [fourDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.castAdd d index))) =
          Fin.castAdd (b + d) (Fin.natAdd a index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp
  · have input_eq :
        Fin.natAdd (a + b) (Fin.natAdd c index) = input := by
      simpa [fourDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.natAdd c index))) =
          Fin.natAdd (a + c) (Fin.natAdd b index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp

end ConservativeLogic.Circuit
