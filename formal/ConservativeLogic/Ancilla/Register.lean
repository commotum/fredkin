import ConservativeLogic.State.Core

/-!
# Explicit result-register states

The result register consists of two ordered width-`n` halves.  Its prescribed
input is `(0ⁿ,1ⁿ)`, and copying a value into it produces `(value,¬value)`.
These state and Hamming-weight facts are independent of any circuit that
implements the copy operation.
-/

namespace ConservativeLogic.Ancilla

/-- The width-`n` all-zero register. -/
def zeroRegister (n : Nat) : BitState n := fun _ => false

/-- The width-`n` all-one register. -/
def oneRegister (n : Nat) : BitState n := fun _ => true

/-- Pointwise Boolean complement of a fixed-width register. -/
def bitwiseNot {n : Nat} (state : BitState n) : BitState n :=
  fun index => !state index

/-- The prescribed ordered result-register initialization `(0ⁿ,1ⁿ)`. -/
def resultRegisterInput (n : Nat) : BitState (n + n) :=
  BitState.append (zeroRegister n) (oneRegister n)

/-- The ordered result-register output `(value,¬value)`. -/
def resultRegisterOutput {n : Nat} (value : BitState n) : BitState (n + n) :=
  BitState.append value (bitwiseNot value)

/-- An all-zero register has Hamming weight zero. -/
@[simp]
theorem hammingWeight_zeroRegister (n : Nat) :
    hammingWeight (zeroRegister n) = 0 := by
  simp [hammingWeight, zeroRegister]

/-- An all-one width-`n` register has Hamming weight `n`. -/
@[simp]
theorem hammingWeight_oneRegister (n : Nat) :
    hammingWeight (oneRegister n) = n := by
  simp [hammingWeight, oneRegister]

/-- The prescribed result-register initialization contains exactly `n` true bits. -/
@[simp]
theorem hammingWeight_resultRegisterInput (n : Nat) :
    hammingWeight (resultRegisterInput n) = n := by
  simp [resultRegisterInput]

/-- A register and its pointwise complement contain exactly `n` true bits. -/
theorem hammingWeight_add_bitwiseNot {n : Nat} (state : BitState n) :
    hammingWeight state + hammingWeight (bitwiseNot state) = n := by
  unfold hammingWeight bitwiseNot
  simpa using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun index : Fin n => state index = true))

/-- Every ordered output pair `(value,¬value)` has exactly `n` true bits. -/
@[simp]
theorem hammingWeight_resultRegisterOutput {n : Nat} (value : BitState n) :
    hammingWeight (resultRegisterOutput value) = n := by
  rw [resultRegisterOutput, hammingWeight_append,
    hammingWeight_add_bitwiseNot]

end ConservativeLogic.Ancilla
