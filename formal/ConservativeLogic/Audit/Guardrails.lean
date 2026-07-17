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

example (n : Nat) : WirePerm n := Equiv.refl _

example (m n : Nat) : (Fin m ⊕ Fin n) ≃ Fin (m + n) := finSumFinEquiv

example (n : Nat) (x : FunctionWord n) : Nat := functionWeight x

example (n : Nat) (x : VectorWord n) : VectorWord n := x

example (n : Nat) (x : PackedWord n) : PackedWord n := x

end ConservativeLogic.Audit.Guardrails
