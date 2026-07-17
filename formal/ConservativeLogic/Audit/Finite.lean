import ConservativeLogic.API

/-!
# Stage 2 finite-state audit

This diagnostic module checks boundary widths, all rows of the two small
independence witnesses, the active wire-action convention, and the axiom
footprints of the main closure theorems. It is intentionally not re-exported by
the public API.
-/

namespace ConservativeLogic.Audit.Finite

private def singleton (b : Bool) : BitState 1 := fun _ => b

private def pair (a b : Bool) : BitState 2 :=
  BitState.append (singleton a) (singleton b)

example (x : BitState 0) : hammingWeight x = 0 := by simp

example : BitState.split 0 0 (fun i => Fin.elim0 i) =
    ((fun i => Fin.elim0 i), (fun i => Fin.elim0 i)) := by
  apply Prod.ext <;> funext i <;> exact Fin.elim0 i

example : (Conservative.identity 0 : Conservative 0) (fun i => Fin.elim0 i) =
    (fun i => Fin.elim0 i) := by
  simp

example : hammingWeight (BitState.append (singleton true) (singleton false)) = 1 := by
  decide

example : BitState.split 1 1 (pair true false) =
    (singleton true, singleton false) := by
  decide

example : BitState.append (BitState.split 1 1 (pair false true)).1
    (BitState.split 1 1 (pair false true)).2 = pair false true := by
  simp

example : Independence.flipOne (singleton false) = singleton true := by
  decide

example : Independence.flipOne (singleton true) = singleton false := by
  decide

example : Independence.sortTwo (pair false false) = pair false false := by
  decide

example : Independence.sortTwo (pair false true) = pair true false := by
  decide

example : Independence.sortTwo (pair true false) = pair true false := by
  decide

example : Independence.sortTwo (pair true true) = pair true true := by
  decide

private def swapTwo : WirePerm 2 := Equiv.swap 0 1

example : WirePerm.onState swapTwo (pair true false) = pair false true := by
  decide

example : WirePerm.onState swapTwo (pair false true) = pair true false := by
  decide

example : WeightPreserving (WirePerm.onState swapTwo) :=
  WirePerm.onState_weightPreserving swapTwo

#check IsReversible
#check WeightPreserving
#check Reversible
#check Conservative
#check WirePerm.onState_apply_image

#print axioms hammingWeight_append
#print axioms WeightPreserving.comp
#print axioms WeightPreserving.inverse
#print axioms Conservative.comp
#print axioms Conservative.inverse
#print axioms WirePerm.onState_weightPreserving
#print axioms Independence.flipOne_not_weightPreserving
#print axioms Independence.sortTwo_weightPreserving
#print axioms Independence.sortTwo_not_injective
#print axioms Independence.reversible_not_weightPreserving
#print axioms Independence.weightPreserving_not_reversible

end ConservativeLogic.Audit.Finite
