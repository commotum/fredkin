import ConservativeLogic.Gate.Fredkin

/-!
# A precise XOR-nonlinearity witness for the paper Fredkin gate

The paper calls the Fredkin gate "nonlinear" without specifying an algebraic
structure. This module selects the standard identification of Boolean states
with vectors over `F₂`: vector addition is coordinatewise XOR and the zero
vector is the all-`false` state. The result below is only a theorem about that
explicit algebraic interpretation. It is not a definition quoted from the
paper and makes no claim about physical nonlinearity.
-/

namespace ConservativeLogic

namespace BitState

/-- Coordinatewise XOR, used here as addition of finite Boolean states. -/
def xor {n : Nat} (left right : BitState n) : BitState n :=
  fun i => Bool.xor (left i) (right i)

/-- Coordinatewise XOR is computed independently at each wire position. -/
@[simp]
theorem xor_apply {n : Nat} (left right : BitState n) (i : Fin n) :
    xor left right i = Bool.xor (left i) (right i) :=
  rfl

/-- The all-`false` Boolean state, selected as the zero vector. -/
def falseState (n : Nat) : BitState n :=
  fun _ => false

/-- Every coordinate of the selected zero state is `false`. -/
@[simp]
theorem falseState_apply (n : Nat) (i : Fin n) : falseState n i = false :=
  rfl

end BitState

/--
An explicitly selected lightweight notion of `F₂`-linearity: a map preserves
the all-false state and coordinatewise XOR.

This predicate deliberately states both obligations rather than installing a
Boolean-ring or module structure on `BitState`.
-/
def XorLinear {m n : Nat} (f : BitState m → BitState n) : Prop :=
  f (BitState.falseState m) = BitState.falseState n ∧
    ∀ left right, f (BitState.xor left right) = BitState.xor (f left) (f right)

namespace PaperFredkin

/--
For the concrete inputs `100` and `010`, mapping their XOR produces `110`.
This is one side of the selected `F₂`-additivity equation.
-/
theorem map_xor_counterexample_left :
    map (BitState.xor (state true false false) (state false true false)) =
      state true true false := by
  decide

/--
For the concrete inputs `100` and `010`, XORing their separate images produces
`101`. This is the other side of the selected `F₂`-additivity equation.
-/
theorem map_xor_counterexample_right :
    BitState.xor (map (state true false false)) (map (state false true false)) =
      state true false true := by
  decide

/-- The two explicit output states in the XOR counterexample are unequal. -/
theorem map_xor_counterexample_outputs_ne :
    state true true false ≠ state true false true := by
  decide

/-- The two concrete inputs directly witness failure of XOR additivity. -/
theorem map_xor_counterexample :
    map (BitState.xor (state true false false) (state false true false)) ≠
      BitState.xor (map (state true false false)) (map (state false true false)) := by
  rw [map_xor_counterexample_left, map_xor_counterexample_right]
  exact map_xor_counterexample_outputs_ne

/--
The paper-convention Fredkin map is not linear for the explicitly selected
coordinatewise-XOR interpretation of Boolean states as vectors over `F₂`.
-/
theorem map_not_xorLinear : ¬ XorLinear map := by
  intro hlinear
  exact map_xor_counterexample
    (hlinear.2 (state true false false) (state false true false))

end PaperFredkin

end ConservativeLogic
