import Mathlib.Logic.Equiv.Fintype
import ConservativeLogic.Ancilla.Uncompute

/-!
# Finite Hamming layers and semantic conservative completion

This module separates two semantic facts from fixed-basis synthesis.  First,
a conservative permutation is exactly a family of independent permutations of
the finite Hamming-weight layers.  Second, two finite injective families paired
at equal weight extend noncanonically to a total conservative permutation.

The latter repairs the suppressed total-extension step in Figure 25 of
Fredkin and Toffoli: the drawing specifies only
`(x,0^n,1^n) -> (x,f x,not (f x))`.  The extension chosen here is classical and
is not itself a circuit.  The final same-register characterization likewise
concerns one arbitrary monolithic conservative gate, not the fixed Fredkin
basis.
-/

namespace ConservativeLogic

open Ancilla

/-- Boolean states of width `n` having exactly `weight` true wires. -/
abbrev WeightLayer (n weight : Nat) :=
  {state : BitState n // hammingWeight state = weight}

namespace Conservative

/-- A conservative permutation restricts to a permutation of every weight layer. -/
def onWeightLayer {n : Nat} (gate : Conservative n) (weight : Nat) :
    Equiv.Perm (WeightLayer n weight) where
  toFun state :=
    ⟨gate state.1, (gate.weight_preserving state.1).trans state.2⟩
  invFun state :=
    ⟨gate.toEquiv.symm state.1,
      ((WeightPreserving.inverse gate.toEquiv gate.weight_preserving) state.1).trans state.2⟩
  left_inv state := by
    apply Subtype.ext
    exact gate.toEquiv.symm_apply_apply state.1
  right_inv state := by
    apply Subtype.ext
    exact gate.toEquiv.apply_symm_apply state.1

end Conservative

/-- Every state is equivalently its weight together with a state in that exact layer. -/
def stateWeightEquiv (n : Nat) :
    BitState n ≃ (Σ weight, WeightLayer n weight) where
  toFun state := ⟨hammingWeight state, ⟨state, rfl⟩⟩
  invFun state := state.2.1
  left_inv _ := rfl
  right_inv state := by
    rcases state with ⟨weight, state, stateWeight⟩
    subst weight
    rfl

namespace Conservative

/-- Independent permutations of all Hamming layers assemble into a conservative map. -/
def ofWeightLayers {n : Nat}
    (layers : ∀ weight, Equiv.Perm (WeightLayer n weight)) : Conservative n where
  toEquiv :=
    (stateWeightEquiv n).trans
      ((Equiv.sigmaCongrRight layers).trans (stateWeightEquiv n).symm)
  weight_preserving := by
    intro state
    exact (layers (hammingWeight state) ⟨state, rfl⟩).2

@[simp]
theorem ofWeightLayers_apply {n : Nat}
    (layers : ∀ weight, Equiv.Perm (WeightLayer n weight)) (state : BitState n) :
    ofWeightLayers layers state =
      (layers (hammingWeight state) ⟨state, rfl⟩).1 :=
  rfl

/-- Restricting an assembled layer family recovers the selected permutation. -/
theorem onWeightLayer_ofWeightLayers {n : Nat}
    (layers : ∀ weight, Equiv.Perm (WeightLayer n weight)) (weight : Nat) :
    (ofWeightLayers layers).onWeightLayer weight = layers weight := by
  ext state
  rcases state with ⟨state, stateWeight⟩
  subst weight
  rfl

/-- Reassembling all restrictions of a conservative map recovers that map. -/
theorem ofWeightLayers_onWeightLayer {n : Nat} (gate : Conservative n) :
    ofWeightLayers (gate.onWeightLayer) = gate := by
  apply Conservative.ext
  ext state
  rfl

end Conservative

/--
Two finite injective families of states, paired pointwise at equal Hamming
weight, extend to a total conservative permutation.

The choice outside the displayed pairs is made independently in each layer
and is intentionally noncanonical.
-/
theorem exists_conservative_extending_pair {n : Nat} {index : Type*} [Finite index]
    (source target : index → BitState n)
    (source_injective : Function.Injective source)
    (target_injective : Function.Injective target)
    (sameWeight : ∀ i, hammingWeight (target i) = hammingWeight (source i)) :
    ∃ gate : Conservative n, ∀ i, gate (source i) = target i := by
  classical
  have layerExtension : ∀ weight, ∃ permutation : Equiv.Perm (WeightLayer n weight),
      ∀ i : {i : index // hammingWeight (source i) = weight},
        permutation ⟨source i.1, i.2⟩ =
          ⟨target i.1, (sameWeight i.1).trans i.2⟩ := by
    intro weight
    apply Equiv.Perm.exists_extending_pair
    · intro left right equality
      apply Subtype.ext
      apply source_injective
      exact congrArg Subtype.val equality
    · intro left right equality
      apply Subtype.ext
      apply target_injective
      exact congrArg Subtype.val equality
  choose layers extension_spec using layerExtension
  refine ⟨Conservative.ofWeightLayers layers, ?_⟩
  intro i
  have extension := extension_spec (hammingWeight (source i)) ⟨i, rfl⟩
  exact congrArg Subtype.val extension

/-- Figure 25's initialized slice extends to a total conservative permutation. -/
theorem exists_figure25_conservative {argumentWidth resultWidth : Nat}
    (function : BitState argumentWidth → BitState resultWidth) :
    ∃ gate : Conservative (argumentWidth + (resultWidth + resultWidth)), ∀ argument,
      gate (BitState.append argument (resultRegisterInput resultWidth)) =
        BitState.append argument (resultRegisterOutput (function argument)) := by
  apply exists_conservative_extending_pair
  · intro left right equality
    have splitEquality := congrArg
      (BitState.split argumentWidth (resultWidth + resultWidth)) equality
    simpa using congrArg Prod.fst splitEquality
  · intro left right equality
    have splitEquality := congrArg
      (BitState.split argumentWidth (resultWidth + resultWidth)) equality
    simpa using congrArg Prod.fst splitEquality
  · intro argument
    simp only [hammingWeight_append, hammingWeight_resultRegisterInput,
      hammingWeight_resultRegisterOutput]

/-- Semantic same-register realization by one arbitrary conservative gate. -/
def DirectlyRealizable {n : Nat} (function : BitState n → BitState n) : Prop :=
  ∃ gate : Conservative n, ∀ state, gate state = function state

/--
Direct semantic realizability is exactly bijectivity plus conservation.
This theorem permits the complete endomap itself as a monolithic primitive;
it is not a `Circuit` or Fredkin-basis theorem.
-/
theorem direct_realization_iff {n : Nat} (function : BitState n → BitState n) :
    DirectlyRealizable function ↔
      IsReversible function ∧ WeightPreserving function := by
  constructor
  · rintro ⟨gate, realizes⟩
    have functionEquality : (fun state => gate state) = function := funext realizes
    constructor
    · rw [← functionEquality]
      exact gate.isReversible
    · rw [← functionEquality]
      exact gate.weight_preserving
  · rintro ⟨reversible, conservative⟩
    let gate : Conservative n :=
      { toEquiv := Equiv.ofBijective function reversible
        weight_preserving := conservative }
    exact ⟨gate, fun _ => rfl⟩

end ConservativeLogic
