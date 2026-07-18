import Mathlib.GroupTheory.Perm.ClosureSwap
import ConservativeLogic.Completeness.Adjacent
import ConservativeLogic.Completeness.Johnson

/-!
# Finite clean synthesis from local state exchanges

The distance-two exchanges in each Hamming layer generate exactly the finite
conservative permutations.  This module connects that group-theoretic fact to
the explicit clean Fredkin realization of one exchange.
-/

namespace ConservativeLogic

open Equiv MulAction Set Subgroup

/-- Full-state transpositions arising from one true/false coordinate exchange. -/
private def conservativeEdgeSwaps (width : Nat) :
    Set (Equiv.Perm (BitState width)) :=
  {permutation | ∃ weight, ∃ left right : WeightLayer width weight,
    Conservative.SingleExchange left right ∧
      permutation = Equiv.swap left.1 right.1}

private theorem conservativeEdgeSwaps_isSwap (width : Nat) :
    ∀ permutation ∈ conservativeEdgeSwaps width, permutation.IsSwap := by
  rintro permutation ⟨weight, left, right, exchange, rfl⟩
  have distinct : left.1 ≠ right.1 := by
    intro equality
    apply Conservative.hammingTwo_ne left right
      (Conservative.singleExchange_hammingTwo exchange)
    exact Subtype.ext equality
  exact ⟨left.1, right.1, distinct, rfl⟩

private theorem layerSwap_mem_edgeClosure {width weight : Nat}
    {left right : WeightLayer width weight}
    (path : Relation.ReflTransGen Conservative.SingleExchange left right) :
    Equiv.swap left.1 right.1 ∈
      Subgroup.closure (conservativeEdgeSwaps width) := by
  induction path with
  | refl =>
      rw [Equiv.swap_self]
      exact (Subgroup.closure (conservativeEdgeSwaps width)).one_mem
  | @tail middle right path exchange inductionHypothesis =>
      exact SubmonoidClass.swap_mem_trans
        (Subgroup.closure (conservativeEdgeSwaps width)) inductionHypothesis
        (Subgroup.subset_closure
          ⟨weight, middle, right, exchange, rfl⟩)

/--
If each single-coordinate exchange has a clean realization, every finite
conservative permutation has one.  The proof is not an enumeration of circuit
syntax: it uses Hamming-layer connectivity and the finite permutation-group
closure theorem.
-/
private theorem conservative_clean_of_exchange_clean {width : Nat}
    (edgeClean : ∀ weight (left right : WeightLayer width weight),
      Conservative.SingleExchange left right →
        CleanFredkinRealizable (Equiv.swap left.1 right.1))
    (gate : Conservative width) :
    CleanFredkinRealizable gate.toEquiv := by
  have generated : gate.toEquiv ∈
      Subgroup.closure (conservativeEdgeSwaps width) := by
    rw [mem_closure_isSwap (conservativeEdgeSwaps_isSwap width)]
    constructor
    · exact Set.toFinite _
    · intro state
      let source : WeightLayer width (hammingWeight state) := ⟨state, rfl⟩
      let target : WeightLayer width (hammingWeight state) :=
        ⟨gate state, gate.weight_preserving state⟩
      have path : Relation.ReflTransGen Conservative.SingleExchange
          source target :=
        Conservative.weightLayer_exchange_connected source target
      have swapMem : Equiv.swap state (gate state) ∈
          Subgroup.closure (conservativeEdgeSwaps width) := by
        simpa [source, target] using layerSwap_mem_edgeClosure path
      exact ⟨⟨Equiv.swap state (gate state), swapMem⟩,
        Equiv.swap_apply_left state (gate state)⟩
  have closure_le_clean :
      Subgroup.closure (conservativeEdgeSwaps width) ≤
        cleanFredkinSubgroup width := by
    rw [Subgroup.closure_le]
    rintro permutation ⟨weight, left, right, exchange, rfl⟩
    exact edgeClean weight left right exchange
  exact closure_le_clean generated

/--
Every finite conservative permutation has a clean realization using paper
Fredkin gates and explicit structural wire reindexing.

The witness exposes its finite ancillary width, exact Boolean initialization
(not constrained to all zero), complete circuit, exact restoration equation,
no-`unitWire` syntax certificate, and zero-latency certificate through the
fields of `CleanFredkinRealization`.
-/
theorem fredkin_complete_conservative {width : Nat}
    (gate : Conservative width) :
    CleanFredkinRealizable gate.toEquiv := by
  apply conservative_clean_of_exchange_clean
  · intro weight left right exchange
    rcases exchange with ⟨first, second, distinct, different, rfl⟩
    simpa [Conservative.reindexLayer] using
      (singleExchangeClean left.1
        (WirePerm.onState (Equiv.swap first second) left.1)
        first second distinct different rfl)

/-- Pointwise functions admitting some reversible clean Fredkin realization. -/
def CleanFredkinRealizableFunction {width : Nat}
    (function : BitState width → BitState width) : Prop :=
  ∃ gate : Reversible width,
    (∀ state, gate state = function state) ∧ CleanFredkinRealizable gate

/--
Fixed-basis clean realizability has the same finite semantic boundary as a
monolithic conservative gate, but supplies a circuit and returned workspace.
-/
theorem clean_fredkin_realizable_iff {width : Nat}
    (function : BitState width → BitState width) :
    CleanFredkinRealizableFunction function ↔
      IsReversible function ∧ WeightPreserving function := by
  constructor
  · rintro ⟨gate, realizes, clean⟩
    have functionEquality : (fun state => gate state) = function :=
      funext realizes
    constructor
    · rw [← functionEquality]
      exact gate.isReversible
    · rw [← functionEquality]
      exact clean.weightPreserving
  · rintro ⟨reversible, conservative⟩
    let gateEquiv : Reversible width := Equiv.ofBijective function reversible
    let gate : Conservative width := {
      toEquiv := gateEquiv
      weight_preserving := conservative
    }
    exact ⟨gateEquiv, fun _ => rfl, fredkin_complete_conservative gate⟩

/--
Figure 25's noncanonical total completion also has a fixed-basis clean
realization.  The visible `argument ++ (0^n,1^n)` block is separate from the
returned completeness workspace stored in `realization.ancillaInit`.
-/
theorem figure25_fredkin_complete {argumentWidth resultWidth : Nat}
    (function : BitState argumentWidth → BitState resultWidth) :
    ∃ gate : Conservative (argumentWidth + (resultWidth + resultWidth)),
      ∃ _realization : CleanFredkinRealization gate.toEquiv,
        ∀ argument,
          gate (BitState.append argument
              (Ancilla.resultRegisterInput resultWidth)) =
            BitState.append argument
              (Ancilla.resultRegisterOutput (function argument)) := by
  obtain ⟨gate, gateSpec⟩ := exists_figure25_conservative function
  obtain ⟨realization⟩ := fredkin_complete_conservative gate
  exact ⟨gate, realization, gateSpec⟩

end ConservativeLogic
