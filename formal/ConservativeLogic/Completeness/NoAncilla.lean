import Mathlib.GroupTheory.Perm.Sign
import ConservativeLogic.Completeness.Semantic

/-!
# The minimal no-ancilla obstruction

Fredkin completeness is false if it is read as a same-width theorem with no
ancillary wires.  This module proves the first obstruction for the repository's
actual circuit grammar, including its arbitrary structural wire
reindexings.  Every four-wire circuit induces an even permutation of all
sixteen states, while one transposition inside the weight-two layer is an odd
conservative permutation.

The circuit theorem is structural and covers infinitely many syntax trees.
Only the finite base fact that all 24 `WirePerm 4` values act evenly on
four-wire states is discharged by kernel reduction.
-/

namespace ConservativeLogic

open Equiv

private theorem sign_prodCongr {α β : Type*}
    [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]
    (left : Equiv.Perm α) (right : Equiv.Perm β) :
    Equiv.Perm.sign (Equiv.prodCongr left right) =
      Equiv.Perm.sign left ^ Fintype.card β *
        Equiv.Perm.sign right ^ Fintype.card α := by
  have factorization :
      Equiv.prodCongr left right =
        (Equiv.prodCongrLeft (fun _ : β => left)).trans
          (Equiv.prodCongrRight (fun _ : α => right)) := by
    ext input <;> rfl
  rw [factorization, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_prodCongrRight, Equiv.Perm.sign_prodCongrLeft]
  simp [Finset.prod_const, mul_comm]

private theorem sign_tensor {m n : Nat}
    (left : Reversible m) (right : Reversible n) :
    Equiv.Perm.sign (Reversible.tensor left right) =
      Equiv.Perm.sign left ^ (2 ^ n) *
        Equiv.Perm.sign right ^ (2 ^ m) := by
  unfold Reversible.tensor
  rw [← Equiv.trans_assoc, Equiv.Perm.sign_symm_trans_trans, sign_prodCongr]
  simp only [Realization.card_bitState]

private theorem intUnit_even_pow (unit : ℤˣ) (exponent : Nat) :
    unit ^ (2 * exponent) = 1 := by
  rcases Int.units_eq_one_or unit with rfl | rfl <;> simp [pow_mul]

set_option maxRecDepth 100000 in
private theorem wirePerm_four_even : ∀ wiring : WirePerm 4,
    Equiv.Perm.sign (WirePerm.onState wiring) = 1 := by
  decide

private theorem circuit_even_aux {width : Nat} (circuit : Circuit width)
    (widthEquality : width = 4) :
    Equiv.Perm.sign (Circuit.eval circuit).toEquiv = 1 := by
  induction circuit with
  | identity width => simp [Circuit.eval, Conservative.identity, Reversible.identity]
  | unitWire => omega
  | fredkin => omega
  | permute wiring =>
      cases widthEquality
      exact wirePerm_four_even wiring
  | seq first second firstIH secondIH =>
      simp only [Circuit.eval, Conservative.comp, Reversible.comp]
      rw [Equiv.Perm.sign_trans, firstIH widthEquality, secondIH widthEquality]
      simp
  | @tensor m n left right leftIH rightIH =>
      have widths :
          (m = 0 ∧ n = 4) ∨ (m = 1 ∧ n = 3) ∨
          (m = 2 ∧ n = 2) ∨ (m = 3 ∧ n = 1) ∨
          (m = 4 ∧ n = 0) := by omega
      simp only [Circuit.eval]
      change Equiv.Perm.sign
        (Reversible.tensor (Circuit.eval left).toEquiv
          (Circuit.eval right).toEquiv) = 1
      rw [sign_tensor]
      rcases widths with h | h | h | h | h
      · rcases h with ⟨rfl, rfl⟩
        rw [rightIH (by omega)]
        have leftEven : Equiv.Perm.sign (Circuit.eval left).toEquiv ^ 16 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval left).toEquiv) 8
        simpa using leftEven
      · rcases h with ⟨rfl, rfl⟩
        have leftEven : Equiv.Perm.sign (Circuit.eval left).toEquiv ^ 8 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval left).toEquiv) 4
        have rightEven : Equiv.Perm.sign (Circuit.eval right).toEquiv ^ 2 = 1 := by
          exact intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval right).toEquiv) 1
        simp [leftEven, rightEven]
      · rcases h with ⟨rfl, rfl⟩
        have leftEven : Equiv.Perm.sign (Circuit.eval left).toEquiv ^ 4 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval left).toEquiv) 2
        have rightEven : Equiv.Perm.sign (Circuit.eval right).toEquiv ^ 4 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval right).toEquiv) 2
        simp [leftEven, rightEven]
      · rcases h with ⟨rfl, rfl⟩
        have leftEven : Equiv.Perm.sign (Circuit.eval left).toEquiv ^ 2 = 1 := by
          exact intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval left).toEquiv) 1
        have rightEven : Equiv.Perm.sign (Circuit.eval right).toEquiv ^ 8 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval right).toEquiv) 4
        simp [leftEven, rightEven]
      · rcases h with ⟨rfl, rfl⟩
        rw [leftIH (by omega)]
        have rightEven : Equiv.Perm.sign (Circuit.eval right).toEquiv ^ 16 = 1 := by
          simpa using intUnit_even_pow
            (Equiv.Perm.sign (Circuit.eval right).toEquiv) 8
        simpa using rightEven

/-- Every complete four-wire circuit semantics is an even state permutation. -/
theorem circuit_four_even (circuit : Circuit 4) :
    Equiv.Perm.sign (Circuit.eval circuit).toEquiv = 1 :=
  circuit_even_aux circuit rfl

private def pair (first second : Bool) : BitState 2 :=
  fun index => Fin.cases first (fun tail => Fin.cases second Fin.elim0 tail) index

/-- The weight-two state `1100`. -/
def middleLayerStateA : BitState 4 :=
  BitState.append (pair true true) (pair false false)

/-- The weight-two state `1010`. -/
def middleLayerStateB : BitState 4 :=
  BitState.append (pair true false) (pair true false)

/-- Swap only `1100` and `1010`, fixing the other fourteen states. -/
def middleLayerSwap : Reversible 4 :=
  Equiv.swap middleLayerStateA middleLayerStateB

@[simp]
theorem middleLayerStateA_weight : hammingWeight middleLayerStateA = 2 := by
  decide

@[simp]
theorem middleLayerStateB_weight : hammingWeight middleLayerStateB = 2 := by
  decide

/-- The isolated middle-layer swap preserves Hamming weight. -/
theorem middleLayerSwap_weightPreserving : WeightPreserving middleLayerSwap := by
  intro state
  by_cases ha : state = middleLayerStateA
  · subst state
    simp [middleLayerSwap]
  · by_cases hb : state = middleLayerStateB
    · subst state
      simp [middleLayerSwap]
    · rw [show middleLayerSwap state = state by
          exact Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The minimal counterexample bundled as a total conservative permutation. -/
def middleLayerSwapConservative : Conservative 4 where
  toEquiv := middleLayerSwap
  weight_preserving := middleLayerSwap_weightPreserving

/-- A single nontrivial state transposition is odd. -/
theorem middleLayerSwap_odd :
    Equiv.Perm.sign middleLayerSwap = -1 := by
  exact Equiv.Perm.sign_swap (by decide : middleLayerStateA ≠ middleLayerStateB)

/-- No ancillary-free four-wire circuit realizes the isolated weight-two swap. -/
theorem middleLayerSwap_not_circuit :
    ¬ ∃ circuit : Circuit 4,
      (Circuit.eval circuit).toEquiv = middleLayerSwap := by
  rintro ⟨circuit, equality⟩
  have even := circuit_four_even circuit
  rw [equality, middleLayerSwap_odd] at even
  exact (by decide : (-1 : ℤˣ) ≠ 1) even

end ConservativeLogic
