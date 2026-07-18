import ConservativeLogic.Circuit.Structural

/-!
# Static circuit syntax resources

This module contains resource measures defined directly on balanced circuit
syntax.  Counts are independent of evaluation, routing geometry, and the
source-language compiler.
-/

namespace ConservativeLogic.Circuit

/-- Exact number of paper-Fredkin constructors in a circuit term. -/
def fredkinCount : {width : Nat} → Circuit width → Nat
  | _, .identity _ => 0
  | _, .unitWire => 0
  | _, .fredkin => 1
  | _, .permute _ => 0
  | _, .seq first second => fredkinCount first + fredkinCount second
  | _, .tensor left right => fredkinCount left + fredkinCount right

/-- Width transport does not change the number of Fredkin constructors. -/
@[simp]
theorem fredkinCount_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth) :
    fredkinCount (Circuit.cast width circuit) = fredkinCount circuit := by
  cases width
  rfl

end ConservativeLogic.Circuit
