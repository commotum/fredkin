import ConservativeLogic.API

/-!
# Stage 2 finite-state audit

This diagnostic module checks boundary widths, all rows of the two small
independence witnesses, the active wire-action convention, and the axiom
footprints of the main closure theorems. It is intentionally not re-exported by
the public API.
-/

namespace ConservativeLogic.Audit.Finite

private def emptyState : BitState 0 := fun i => Fin.elim0 i

private def singleton (b : Bool) : BitState 1 := fun _ => b

private def pair (a b : Bool) : BitState 2 :=
  BitState.append (singleton a) (singleton b)

private def triple (a b c : Bool) : BitState 3 :=
  BitState.append (singleton a) (pair b c)

example (x : BitState 0) : hammingWeight x = 0 := by simp

example : BitState.split 0 0 emptyState = (emptyState, emptyState) := by
  apply Prod.ext <;> funext i <;> exact Fin.elim0 i

example : BitState.append emptyState emptyState = emptyState := by
  funext i
  exact Fin.elim0 i

example : BitState.appendEquiv 0 0 (emptyState, emptyState) = emptyState := by
  funext i
  exact Fin.elim0 i

example : (Conservative.identity 0 : Conservative 0) emptyState = emptyState := by
  simp

example : hammingWeight (BitState.append (singleton true) (singleton false)) = 1 := by
  decide

example : zeroCount (pair true false) = 1 := by
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

example : zeroCount (WirePerm.onState swapTwo (pair true false)) =
    zeroCount (pair true false) :=
  WeightPreserving.zeroCount (WirePerm.onState_weightPreserving swapTwo) _

private def cycleThree : WirePerm 3 :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

/-- A non-self-inverse row that distinguishes the active action from its inverse. -/
example : WirePerm.onState cycleThree (triple true false false) =
    triple false false true := by
  decide

private def emptyWirePerm : WirePerm 0 := Equiv.refl _

example : WirePerm.onState emptyWirePerm emptyState = emptyState := by
  funext i
  exact Fin.elim0 i

example : (WirePerm.conservative emptyWirePerm) emptyState = emptyState := by
  funext i
  exact Fin.elim0 i

#check IsReversible
#check WeightPreserving
#check Reversible
#check Conservative
#check BitState.appendEquiv
#check Reversible.identity
#check Reversible.comp
#check Reversible.inverse
#check Reversible.injective
#check Reversible.surjective
#check Reversible.isReversible
#check WirePerm.onState_apply_image
#check WirePerm.conservative

#print axioms BitState.split_append
#print axioms BitState.append_split
#print axioms hammingWeight_append
#print axioms WeightPreserving.zeroCount
#print axioms IsReversible.comp
#print axioms WeightPreserving.comp
#print axioms WeightPreserving.inverse
#print axioms Conservative.comp
#print axioms Conservative.inverse
#print axioms WirePerm.onState_comp
#print axioms WirePerm.onState_inverse
#print axioms WirePerm.onState_weightPreserving
#print axioms Independence.flipOne_not_weightPreserving
#print axioms Independence.sortTwo_weightPreserving
#print axioms Independence.sortTwo_not_injective
#print axioms Independence.reversible_not_weightPreserving
#print axioms Independence.weightPreserving_not_reversible

end ConservativeLogic.Audit.Finite
