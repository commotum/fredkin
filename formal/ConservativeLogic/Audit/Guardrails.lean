import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Stage 1 representation probes

This diagnostic leaf checks that the candidate finite-word and reversible-map
surfaces needed by stage 2 are available from a narrow mathlib import. All
candidate declarations are private so this file creates no public API.
-/

namespace ConservativeLogic.Audit.Guardrails

private abbrev FunctionWord (n : Nat) := Fin n → Bool

private abbrev VectorWord (n : Nat) := Vector Bool n

private abbrev PackedWord (n : Nat) := BitVec n

private abbrev Reversible (n : Nat) := Equiv.Perm (FunctionWord n)

private abbrev WirePerm (n : Nat) := Equiv.Perm (Fin n)

private def functionWeight {n : Nat} (x : FunctionWord n) : Nat :=
  (Finset.univ.filter fun i => x i = true).card

example (n : Nat) : Fintype (FunctionWord n) := inferInstance

example (n : Nat) : DecidableEq (FunctionWord n) := inferInstance

example (n : Nat) : Reversible n := Equiv.refl _

example (n : Nat) : Equiv.Perm (FunctionWord n) := Equiv.refl _

example (n : Nat) (e : Reversible n) : Reversible n := e.symm

example (n : Nat) (e f : Reversible n) : Reversible n := e.trans f

example (n : Nat) (e f : Reversible n) (x : FunctionWord n) :
    e.trans f x = f (e x) := rfl

example (n : Nat) : WirePerm n := Equiv.refl _

example (m n : Nat) : (Fin m ⊕ Fin n) ≃ Fin (m + n) := finSumFinEquiv

example (m n : Nat) (left : FunctionWord m) (right : FunctionWord n) :
    FunctionWord (m + n) :=
  Fin.addCases left right

example (n : Nat) (x : FunctionWord n) : Nat := functionWeight x

example (n : Nat) (x : VectorWord n) : VectorWord n := x

example (n : Nat) : DecidableEq (VectorWord n) := inferInstance

#guard_msgs (drop info) in
#check_failure (inferInstance : Fintype (VectorWord 3))

example (n : Nat) (x : PackedWord n) : PackedWord n := x

example (n : Nat) : DecidableEq (PackedWord n) := inferInstance

#guard_msgs (drop info) in
#check_failure (inferInstance : Fintype (PackedWord 3))

end ConservativeLogic.Audit.Guardrails
