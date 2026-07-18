import Mathlib.Logic.Equiv.Prod
import ConservativeLogic.Circuit.Syntax
import ConservativeLogic.Gate.UnitWire
import ConservativeLogic.Gate.Fredkin

/-!
# Static semantics of balanced feed-forward circuits

Evaluation forgets timing and maps every balanced grammar term to its exact
finite conservative boundary-value map. The value-processing basis is fixed,
while explicit arbitrary bijective port reindexing remains a structural
allowance rather than a synthesized gate. Tensor evaluation splits the input
into ordered, disjoint blocks and rejoins the separately evaluated outputs; it
does not copy either block.

These theorems establish only static bijectivity and Hamming-weight
preservation. They do not supply feedback, traces, closed trajectories,
physical routing, or a correspondence with the paper's general graph model.
-/

namespace ConservativeLogic

namespace Reversible

/-- Parallel product of reversible maps on adjacent, disjoint wire blocks. -/
def tensor {m n : Nat} (left : Reversible m) (right : Reversible n) :
    Reversible (m + n) :=
  (BitState.appendEquiv m n).symm |>.trans
    ((Equiv.prodCongr left right).trans (BitState.appendEquiv m n))

/-- General split/apply/rejoin form of the reversible tensor product. -/
@[simp]
theorem tensor_apply {m n : Nat} (left : Reversible m) (right : Reversible n)
    (input : BitState (m + n)) :
    tensor left right input =
      BitState.append (left (BitState.split m n input).1)
        (right (BitState.split m n input).2) :=
  rfl

/-- Tensor evaluation on an explicitly appended pair preserves block order. -/
@[simp]
theorem tensor_apply_append {m n : Nat} (left : Reversible m) (right : Reversible n)
    (leftInput : BitState m) (rightInput : BitState n) :
    tensor left right (BitState.append leftInput rightInput) =
      BitState.append (left leftInput) (right rightInput) := by
  simp [tensor_apply]

end Reversible

namespace Conservative

/-- Parallel product of conservative maps on adjacent, disjoint wire blocks. -/
def tensor {m n : Nat} (left : Conservative m) (right : Conservative n) :
    Conservative (m + n) where
  toEquiv := Reversible.tensor left.toEquiv right.toEquiv
  weight_preserving := by
    intro input
    let leftInput := (BitState.split m n input).1
    let rightInput := (BitState.split m n input).2
    calc
      hammingWeight (Reversible.tensor left.toEquiv right.toEquiv input) =
          hammingWeight (left leftInput) + hammingWeight (right rightInput) := by
        rw [Reversible.tensor_apply, hammingWeight_append]
      _ = hammingWeight leftInput + hammingWeight rightInput :=
        congrArg₂ Nat.add (left.weight_preserving leftInput)
          (right.weight_preserving rightInput)
      _ = hammingWeight (BitState.append leftInput rightInput) :=
        (hammingWeight_append leftInput rightInput).symm
      _ = hammingWeight input := by
        simp [leftInput, rightInput]

/-- General split/apply/rejoin form of the conservative tensor product. -/
@[simp]
theorem tensor_apply {m n : Nat} (left : Conservative m) (right : Conservative n)
    (input : BitState (m + n)) :
    tensor left right input =
      BitState.append (left (BitState.split m n input).1)
        (right (BitState.split m n input).2) :=
  rfl

/-- Conservative tensor evaluation on appended inputs preserves block order. -/
@[simp]
theorem tensor_apply_append {m n : Nat} (left : Conservative m)
    (right : Conservative n) (leftInput : BitState m) (rightInput : BitState n) :
    tensor left right (BitState.append leftInput rightInput) =
      BitState.append (left leftInput) (right rightInput) := by
  simp [tensor_apply]

end Conservative

namespace Circuit

/-- Static conservative boundary-value semantics of a feed-forward circuit. -/
def eval : {n : Nat} → Circuit n → Conservative n
  | _, .identity n => Conservative.identity n
  | _, .unitWire => UnitWire.value
  | _, .fredkin => PaperFredkin.conservative
  | _, .permute wiring => WirePerm.conservative wiring
  | _, .seq first second => Conservative.comp (eval first) (eval second)
  | _, .tensor left right => Conservative.tensor (eval left) (eval right)

/-- Structural identity evaluates to the identity value map. -/
@[simp]
theorem eval_identity {n : Nat} (input : BitState n) :
    eval (.identity n) input = input :=
  rfl

/-- The circuit unit-wire primitive reuses the primitive unit-wire value map. -/
@[simp]
theorem eval_unitWire (input : BitState 1) :
    eval .unitWire input = UnitWire.value input :=
  rfl

/-- The circuit Fredkin primitive reuses the exact paper-convention map. -/
@[simp]
theorem eval_fredkin (input : BitState 3) :
    eval .fredkin input = PaperFredkin.map input :=
  rfl

/-- Structural permutation evaluation uses the established active wire action. -/
@[simp]
theorem eval_permute {n : Nat} (wiring : WirePerm n) (input : BitState n) :
    eval (.permute wiring) input = WirePerm.onState wiring input :=
  rfl

/-- Serial evaluation applies `first` before `second`. -/
@[simp]
theorem eval_seq {n : Nat} (first second : Circuit n) (input : BitState n) :
    eval (.seq first second) input = eval second (eval first input) :=
  rfl

/-- General split/apply/rejoin semantics of disjoint circuit tensor. -/
@[simp]
theorem eval_tensor {m n : Nat} (left : Circuit m) (right : Circuit n)
    (input : BitState (m + n)) :
    eval (.tensor left right) input =
      BitState.append (eval left (BitState.split m n input).1)
        (eval right (BitState.split m n input).2) :=
  rfl

/-- Tensor evaluation on explicit blocks is ordered and disjoint. -/
@[simp]
theorem eval_tensor_append {m n : Nat} (left : Circuit m) (right : Circuit n)
    (leftInput : BitState m) (rightInput : BitState n) :
    eval (.tensor left right) (BitState.append leftInput rightInput) =
      BitState.append (eval left leftInput) (eval right rightInput) := by
  simp [eval_tensor]

/-- Every composed wire length carries the same Boolean value. -/
@[simp]
theorem eval_wireOfLength (length : Nat) (input : BitState 1) :
    eval (wireOfLength length) input = input := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      simpa [wireOfLength, eval_seq, eval_unitWire] using inductionHypothesis

/-- Every circuit term evaluates to a bijection. -/
theorem eval_isReversible {n : Nat} (circuit : Circuit n) :
    IsReversible (eval circuit) :=
  (eval circuit).isReversible

/-- Every circuit term's static boundary-value map preserves Hamming weight. -/
theorem eval_weightPreserving {n : Nat} (circuit : Circuit n) :
    WeightPreserving (eval circuit) :=
  (eval circuit).weight_preserving

end Circuit

end ConservativeLogic
