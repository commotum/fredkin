import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite Boolean states

This module defines fixed-width Boolean states, their Hamming weight, and an
explicit ordered decomposition into adjacent wire blocks. The definitions work
uniformly at width zero and expose the block order through named projection and
round-trip theorems.
-/

namespace ConservativeLogic

/-- A width-`n` Boolean state, indexed by its wire positions. -/
abbrev BitState (n : Nat) := Fin n → Bool

/-- The number of wires carrying `true` in a finite Boolean state. -/
def hammingWeight {n : Nat} (x : BitState n) : Nat :=
  (Finset.univ.filter fun i => x i = true).card

/--
The number of false-valued wires in a fixed-width Boolean state.  This is the
paper's derived `N₀ = N - N₁`, not a second independent conserved quantity.
-/
def zeroCount {n : Nat} (x : BitState n) : Nat :=
  n - hammingWeight x

/-- Every width-zero Boolean state has Hamming weight zero. -/
@[simp]
theorem hammingWeight_zero (x : BitState 0) : hammingWeight x = 0 := by
  simp [hammingWeight]

/-- A width-zero state also has no false-valued wires. -/
@[simp]
theorem zeroCount_zero (x : BitState 0) : zeroCount x = 0 := by
  simp [zeroCount]

namespace BitState

/-- Concatenate two ordered Boolean states, with `left` before `right`. -/
def append {m n : Nat} (left : BitState m) (right : BitState n) : BitState (m + n) :=
  Fin.addCases left right

/-- Split a Boolean state at the explicit boundary between widths `m` and `n`. -/
def split (m n : Nat) (x : BitState (m + n)) : BitState m × BitState n :=
  (fun i => x (Fin.castAdd n i), fun i => x (Fin.natAdd m i))

/-- Reading an appended state through the left inclusion recovers the left block. -/
@[simp]
theorem append_castAdd {m n : Nat} (left : BitState m) (right : BitState n) (i : Fin m) :
    append left right (Fin.castAdd n i) = left i := by
  simp [append]

/-- Reading an appended state through the right inclusion recovers the right block. -/
@[simp]
theorem append_natAdd {m n : Nat} (left : BitState m) (right : BitState n) (i : Fin n) :
    append left right (Fin.natAdd m i) = right i := by
  simp [append]

/-- Splitting an appended pair of blocks recovers both original blocks. -/
@[simp]
theorem split_append {m n : Nat} (left : BitState m) (right : BitState n) :
    split m n (append left right) = (left, right) := by
  apply Prod.ext <;> funext i <;> simp [split]

/-- Re-appending the two blocks of a split state recovers the original state. -/
@[simp]
theorem append_split {m n : Nat} (x : BitState (m + n)) :
    append (split m n x).1 (split m n x).2 = x := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [split]
  · intro j
    simp [split]

/-- Concatenation is an equivalence between a pair of blocks and their joined state. -/
def appendEquiv (m n : Nat) : BitState m × BitState n ≃ BitState (m + n) where
  toFun pair := append pair.1 pair.2
  invFun := split m n
  left_inv pair := split_append pair.1 pair.2
  right_inv := append_split

private def truePositionsAppendEquiv {m n : Nat} (left : BitState m) (right : BitState n) :
    {i : Fin (m + n) // append left right i = true} ≃
      {i : Fin m // left i = true} ⊕ {i : Fin n // right i = true} := by
  let e :
      {s : Fin m ⊕ Fin n // Sum.elim (fun i => left i = true) (fun i => right i = true) s} ≃
        {i : Fin (m + n) // append left right i = true} :=
    finSumFinEquiv.subtypeEquiv (by
      intro s
      cases s <;> simp [append])
  exact e.symm.trans Equiv.subtypeSum

end BitState

/-- Hamming weight is additive across the explicit ordered block decomposition. -/
@[simp]
theorem hammingWeight_append {m n : Nat} (left : BitState m) (right : BitState n) :
    hammingWeight (BitState.append left right) =
      hammingWeight left + hammingWeight right := by
  calc
    hammingWeight (BitState.append left right) =
        Fintype.card {i : Fin (m + n) // BitState.append left right i = true} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card ({i : Fin m // left i = true} ⊕ {i : Fin n // right i = true}) :=
      Fintype.card_congr (BitState.truePositionsAppendEquiv left right)
    _ = Fintype.card {i : Fin m // left i = true} +
        Fintype.card {i : Fin n // right i = true} := Fintype.card_sum
    _ = hammingWeight left + hammingWeight right := by
      simp only [Fintype.card_subtype, hammingWeight]

namespace Realization

/-!
Width transport is defined at the state layer because circuit structure and
realization layouts both need it.  The historical `Realization` namespace is
retained as the stable public name; no realization-specific data is involved.
-/

/-- Transport a Boolean state along an equality of widths, without changing any value. -/
def castState {m n : Nat} (width : m = n) (state : BitState m) : BitState n :=
  width ▸ state

/-- Pointwise form of width transport, with the index transported in the reverse direction. -/
theorem castState_apply {m n : Nat} (width : m = n) (state : BitState m)
    (index : Fin n) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

/-- Width transport does not alter Hamming weight. -/
@[simp]
theorem hammingWeight_castState {m n : Nat} (width : m = n) (state : BitState m) :
    hammingWeight (castState width state) = hammingWeight state := by
  cases width
  rfl

/-- Width transport is injective. -/
theorem castState_injective {m n : Nat} (width : m = n) :
    Function.Injective (castState width) := by
  cases width
  exact Function.injective_id

end Realization

end ConservativeLogic
