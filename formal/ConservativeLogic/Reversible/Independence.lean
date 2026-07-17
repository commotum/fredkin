import ConservativeLogic.Reversible.Core

/-!
# Independence of reversibility and Hamming-weight preservation

This module supplies the small semantic witnesses missing from §2.5 of
Fredkin and Toffoli's paper. These are ordinary Boolean endomaps, not circuit
realizations: in particular, `sortTwo` is not evidence for legal fan-out in a
one-to-one circuit model.
-/

namespace ConservativeLogic.Independence

/-- Bitwise negation on a one-wire state, bundled with its inverse. -/
def flipOne : Reversible 1 where
  toFun x i := !x i
  invFun x i := !x i
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

private def zeroOne : BitState 1 := fun _ => false

private def oneOne : BitState 1 := fun _ => true

private theorem flipOne_zeroOne : flipOne zeroOne = oneOne := by
  decide

private theorem hammingWeight_zeroOne : hammingWeight zeroOne = 0 := by
  decide

private theorem hammingWeight_oneOne : hammingWeight oneOne = 1 := by
  decide

/-- One-wire negation is reversible. -/
theorem flipOne_isReversible : IsReversible flipOne :=
  Reversible.isReversible flipOne

/-- One-wire negation is not Hamming-weight-preserving: it sends `false` to `true`. -/
theorem flipOne_not_weightPreserving : ¬ WeightPreserving flipOne := by
  intro h
  have hzero := h zeroOne
  rw [flipOne_zeroOne, hammingWeight_oneOne, hammingWeight_zeroOne] at hzero
  exact Nat.one_ne_zero hzero

/-- There is a reversible Boolean endomap that is not Hamming-weight-preserving. -/
theorem reversible_not_weightPreserving :
    ∃ f : BitState 1 → BitState 1, IsReversible f ∧ ¬ WeightPreserving f :=
  ⟨flipOne, flipOne_isReversible, flipOne_not_weightPreserving⟩

/--
Sort two Boolean values with the larger value first.

Semantically this is `(a, b) ↦ (a || b, a && b)`. It is an ordinary endomap,
not a circuit term and not a claim that either input wire may be consumed twice.
-/
def sortTwo (x : BitState 2) : BitState 2 := fun i =>
  match i with
  | ⟨0, _⟩ => x 0 || x 1
  | ⟨1, _⟩ => x 0 && x 1

/-- The state `(true, false)`. -/
def leftHot : BitState 2 := fun i => decide (i = 0)

/-- The state `(false, true)`. -/
def rightHot : BitState 2 := fun i => decide (i = 1)

/-- The two single-`true` inputs used below are distinct. -/
theorem leftHot_ne_rightHot : leftHot ≠ rightHot := by
  decide

/-- Boolean sorting maps both single-`true` inputs to the same ordered state. -/
theorem sortTwo_collision : sortTwo leftHot = sortTwo rightHot := by
  decide

/-- Boolean sorting preserves Hamming weight on all four two-wire states. -/
theorem sortTwo_weightPreserving : WeightPreserving sortTwo := by
  change ∀ x, hammingWeight (sortTwo x) = hammingWeight x
  decide

/-- Boolean sorting is not injective, witnessed by `leftHot` and `rightHot`. -/
theorem sortTwo_not_injective : ¬ Function.Injective sortTwo := by
  intro hinjective
  exact leftHot_ne_rightHot (hinjective sortTwo_collision)

/-- Boolean sorting is not reversible because it is not injective. -/
theorem sortTwo_not_reversible : ¬ IsReversible sortTwo := by
  intro hreversible
  exact sortTwo_not_injective hreversible.1

/-- There is a Hamming-weight-preserving Boolean endomap that is not reversible. -/
theorem weightPreserving_not_reversible :
    ∃ f : BitState 2 → BitState 2, WeightPreserving f ∧ ¬ IsReversible f :=
  ⟨sortTwo, sortTwo_weightPreserving, sortTwo_not_reversible⟩

end ConservativeLogic.Independence
