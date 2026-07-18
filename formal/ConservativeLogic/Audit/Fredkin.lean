import ConservativeLogic.API

/-!
# Stage 3 unit-wire and Fredkin audit

This diagnostic module checks the two unit-wire value rows, Table (2)'s eight
rows in printed order, bundle agreement, the selected coordinatewise-XOR
counterexample, and the axiom footprints of the stable Stage 3 results. It is
intentionally not re-exported by the public API.
-/

namespace ConservativeLogic.Audit.Fredkin

private def bit (value : Bool) : BitState 1 := fun _ => value

example : UnitWire.value (bit false) = bit false := by
  decide

example : UnitWire.value (bit true) = bit true := by
  decide

example : UnitWire.delay = 1 := by
  rfl

example : PaperFredkin.state true false true 0 = true := rfl
example : PaperFredkin.state true false true 1 = false := rfl
example : PaperFredkin.state true false true 2 = true := rfl

example : PaperFredkin.dataSwap (0 : Fin 3) = 0 := by
  decide

example : PaperFredkin.dataSwap (1 : Fin 3) = 2 := by
  decide

example : PaperFredkin.dataSwap (2 : Fin 3) = 1 := by
  decide

-- Table (2), in the paper's printed row order.
example : PaperFredkin.map (PaperFredkin.state false false false) =
    PaperFredkin.state false false false := by
  decide

example : PaperFredkin.map (PaperFredkin.state false false true) =
    PaperFredkin.state false true false := by
  decide

example : PaperFredkin.map (PaperFredkin.state false true false) =
    PaperFredkin.state false false true := by
  decide

example : PaperFredkin.map (PaperFredkin.state false true true) =
    PaperFredkin.state false true true := by
  decide

example : PaperFredkin.map (PaperFredkin.state true false false) =
    PaperFredkin.state true false false := by
  decide

example : PaperFredkin.map (PaperFredkin.state true false true) =
    PaperFredkin.state true false true := by
  decide

example : PaperFredkin.map (PaperFredkin.state true true false) =
    PaperFredkin.state true true false := by
  decide

example : PaperFredkin.map (PaperFredkin.state true true true) =
    PaperFredkin.state true true true := by
  decide

example (input : BitState 3) : PaperFredkin.equiv input = PaperFredkin.map input := by
  simp

example (input : BitState 3) :
    PaperFredkin.conservative input = PaperFredkin.map input := by
  simp

example :
    PaperFredkin.map
        (BitState.xor (PaperFredkin.state true false false)
          (PaperFredkin.state false true false)) =
      PaperFredkin.state true true false :=
  PaperFredkin.map_xor_counterexample_left

example :
    BitState.xor
        (PaperFredkin.map (PaperFredkin.state true false false))
        (PaperFredkin.map (PaperFredkin.state false true false)) =
      PaperFredkin.state true false true :=
  PaperFredkin.map_xor_counterexample_right

example : ¬ XorLinear PaperFredkin.map :=
  PaperFredkin.map_not_xorLinear

#check UnitWire.value
#check UnitWire.delay
#check PaperFredkin.state
#check PaperFredkin.dataSwap
#check PaperFredkin.map
#check PaperFredkin.map_control
#check PaperFredkin.map_data₁
#check PaperFredkin.map_data₂
#check PaperFredkin.map_of_control_false
#check PaperFredkin.map_of_control_true
#check PaperFredkin.map_state_false
#check PaperFredkin.map_state_true
#check PaperFredkin.table
#check PaperFredkin.equiv
#check PaperFredkin.conservative
#check BitState.xor
#check BitState.falseState
#check XorLinear

#print axioms UnitWire.value_apply
#print axioms UnitWire.delay_eq_one
#print axioms UnitWire.value_isReversible
#print axioms UnitWire.value_weightPreserving
#print axioms PaperFredkin.state_ext
#print axioms PaperFredkin.map_control
#print axioms PaperFredkin.map_data₁
#print axioms PaperFredkin.map_data₂
#print axioms PaperFredkin.map_of_control_false
#print axioms PaperFredkin.map_of_control_true
#print axioms PaperFredkin.map_state_false
#print axioms PaperFredkin.map_state_true
#print axioms PaperFredkin.table
#print axioms PaperFredkin.map_involutive
#print axioms PaperFredkin.equiv_apply
#print axioms PaperFredkin.map_isReversible
#print axioms PaperFredkin.map_weightPreserving
#print axioms PaperFredkin.conservative_apply
#print axioms PaperFredkin.map_xor_counterexample_left
#print axioms PaperFredkin.map_xor_counterexample_right
#print axioms PaperFredkin.map_xor_counterexample_outputs_ne
#print axioms PaperFredkin.map_xor_counterexample
#print axioms PaperFredkin.map_not_xorLinear

end ConservativeLogic.Audit.Fredkin
