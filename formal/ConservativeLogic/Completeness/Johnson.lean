import Mathlib.GroupTheory.Perm.Sign
import ConservativeLogic.Completeness.Semantic

/-!
# Connectivity of finite Hamming layers

Members of one fixed Hamming layer form a connected Johnson graph: an edge
exchanges one true and one false coordinate.  The proof is uniform in the
width.  It maps the true support of one state to the other by a wire
permutation and decomposes that permutation into coordinate swaps.
-/

namespace ConservativeLogic

namespace Conservative

/-- The finite set of true coordinates of a Boolean state. -/
def trueSupport {n : Nat} (state : BitState n) : Finset (Fin n) :=
  Finset.univ.filter fun index => state index = true

@[simp]
theorem mem_trueSupport {n : Nat} (state : BitState n) (index : Fin n) :
    index ∈ trueSupport state ↔ state index = true := by
  simp [trueSupport]

theorem card_trueSupport {n : Nat} (state : BitState n) :
    (trueSupport state).card = hammingWeight state :=
  rfl

theorem trueSupport_onState {n : Nat} (wiring : WirePerm n)
    (state : BitState n) :
    trueSupport (WirePerm.onState wiring state) =
      (trueSupport state).map wiring.toEmbedding := by
  ext index
  simp [trueSupport, WirePerm.onState_apply]

theorem eq_of_trueSupport_eq {n : Nat} {left right : BitState n}
    (equality : trueSupport left = trueSupport right) : left = right := by
  funext index
  have pointwise : left index = true ↔ right index = true := by
    simpa only [mem_trueSupport] using Finset.ext_iff.mp equality index
  cases leftValue : left index <;> cases rightValue : right index <;> simp_all

/-- Reindex a member of one Hamming layer by a permutation of its wires. -/
def reindexLayer {n weight : Nat} (wiring : WirePerm n)
    (state : WeightLayer n weight) : WeightLayer n weight :=
  ⟨WirePerm.onState wiring state.1,
    (WirePerm.onState_weightPreserving wiring state.1).trans state.2⟩

@[simp]
theorem reindexLayer_one {n weight : Nat} (state : WeightLayer n weight) :
    reindexLayer (1 : WirePerm n) state = state := by
  apply Subtype.ext
  rfl

theorem reindexLayer_mul {n weight : Nat} (first second : WirePerm n)
    (state : WeightLayer n weight) :
    reindexLayer (first * second) state =
      reindexLayer first (reindexLayer second state) := by
  apply Subtype.ext
  funext index
  rfl

theorem reindexLayer_swap_eq_self_of_eq {n weight : Nat}
    (state : WeightLayer n weight) (first second : Fin n)
    (sameValue : state.1 first = state.1 second) :
    reindexLayer (Equiv.swap first second) state = state := by
  apply Subtype.ext
  funext index
  by_cases firstIndex : index = first
  · subst index
    simpa [reindexLayer, WirePerm.onState_apply] using sameValue.symm
  by_cases secondIndex : index = second
  · subst index
    simpa [reindexLayer, WirePerm.onState_apply] using sameValue
  simp [reindexLayer, WirePerm.onState_apply,
    Equiv.swap_apply_of_ne_of_ne firstIndex secondIndex]

/-- One Johnson-graph step exchanges a true and a false coordinate. -/
def SingleExchange {n weight : Nat}
    (left right : WeightLayer n weight) : Prop :=
  ∃ first second : Fin n, first ≠ second ∧
    left.1 first ≠ left.1 second ∧
    right = reindexLayer (Equiv.swap first second) left

theorem reindexLayer_reachable {n weight : Nat} (wiring : WirePerm n)
    (state : WeightLayer n weight) :
    Relation.ReflTransGen SingleExchange state (reindexLayer wiring state) := by
  induction wiring using Equiv.Perm.swap_induction_on with
  | one =>
      simpa using (Relation.ReflTransGen.refl :
        Relation.ReflTransGen SingleExchange state state)
  | swap_mul previous first second distinct inductionHypothesis =>
      rw [reindexLayer_mul]
      let middle := reindexLayer previous state
      by_cases sameValue : middle.1 first = middle.1 second
      · rw [reindexLayer_swap_eq_self_of_eq middle first second sameValue]
        exact inductionHypothesis
      · exact inductionHypothesis.tail
          ⟨first, second, distinct, sameValue, rfl⟩

/-- Every two states in one Hamming layer are joined by single exchanges. -/
theorem weightLayer_exchange_connected {n weight : Nat}
    (left right : WeightLayer n weight) :
    Relation.ReflTransGen SingleExchange left right := by
  have sameCardinality :
      (trueSupport left.1).card = (trueSupport right.1).card := by
    rw [card_trueSupport, card_trueSupport, left.2, right.2]
  obtain ⟨wiring, wiringSpec⟩ := Equiv.Perm.exists_map_finset_eq
    (trueSupport left.1) (trueSupport right.1) sameCardinality
  have mapsState : reindexLayer wiring left = right := by
    apply Subtype.ext
    apply eq_of_trueSupport_eq
    exact (trueSupport_onState wiring left.1).trans wiringSpec
  rw [← mapsState]
  exact reindexLayer_reachable wiring left

/-- Number of coordinates on which two Boolean states differ. -/
def hammingDistance {n : Nat} (left right : BitState n) : Nat :=
  (Finset.univ.filter fun index => left index ≠ right index).card

/-- Distance-two adjacency within a fixed Hamming layer. -/
def HammingTwo {n weight : Nat}
    (left right : WeightLayer n weight) : Prop :=
  hammingDistance left.1 right.1 = 2

theorem hammingTwo_ne {n weight : Nat}
    (left right : WeightLayer n weight) (edge : HammingTwo left right) :
    left ≠ right := by
  intro equality
  subst right
  simp [HammingTwo, hammingDistance] at edge

theorem singleExchange_hammingTwo {n weight : Nat}
    {left right : WeightLayer n weight} (exchange : SingleExchange left right) :
    HammingTwo left right := by
  rcases exchange with ⟨first, second, distinct, differentValues, rfl⟩
  unfold HammingTwo hammingDistance
  rw [show (Finset.univ.filter fun index =>
      left.1 index ≠ (reindexLayer (Equiv.swap first second) left).1 index) =
        {first, second} by
    ext index
    by_cases isFirst : index = first
    · subst index
      simp [reindexLayer, WirePerm.onState_apply, differentValues]
    by_cases isSecond : index = second
    · subst index
      simp [reindexLayer, WirePerm.onState_apply, differentValues.symm]
    simp [reindexLayer, WirePerm.onState_apply, isFirst, isSecond,
      Equiv.swap_apply_of_ne_of_ne isFirst isSecond]]
  simp [distinct]

/-- The distance-two Johnson graph on every finite Hamming layer is connected. -/
theorem weightLayer_hammingTwo_connected {n weight : Nat}
    (left right : WeightLayer n weight) :
    Relation.ReflTransGen HammingTwo left right := by
  exact @Relation.ReflTransGen.mono (WeightLayer n weight)
    SingleExchange HammingTwo (fun _ _ => singleExchange_hammingTwo)
    left right (weightLayer_exchange_connected left right)

end Conservative

end ConservativeLogic
