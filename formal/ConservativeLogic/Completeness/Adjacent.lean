import ConservativeLogic.Completeness.Fredkin
import ConservativeLogic.Simulation.Fredkin
import ConservativeLogic.Ancilla.Uncompute

/-!
# Clean realization of one Hamming-layer exchange

An explicit equality predicate is compiled to the paper Fredkin basis, copied
into a returned dual-rail marker, used to exchange one data pair, and
uncomputed.  The canonical circuit swaps exactly `(pattern,0,1)` with
`(pattern,1,0)`.  Structural wire conjugation then realizes the transposition
associated with any exchange of oppositely valued coordinates.

All constants, compiler garbage, and marker wires belong to the named clean
ancillary prefix and are restored exactly.  The construction uses no
`unitWire`; its routing nodes are the library's explicit zero-delay structural
reindexings, not synthesized physical permutation networks.
-/

namespace ConservativeLogic
namespace Completeness.Adjacent

open ConservativeLogic.Ancilla
open ConservativeLogic.Realization
open ConservativeLogic.Realization.Primitive
open ConservativeLogic.Simulation

abbrev markerLayout {m : Nat} (source : SourceCircuit m 1) : Layout :=
  SourceCircuit.simulationLayout source

abbrev markerCoreWidth {m : Nat} (source : SourceCircuit m 1) : Nat :=
  Ancilla.computeCopyUncomputeWidth (markerLayout source)

abbrev controlledWidth {m : Nat} (source : SourceCircuit m 1) : Nat :=
  (markerLayout source).width + 4

private theorem core_plus_targets_width {m : Nat} (source : SourceCircuit m 1) :
    markerCoreWidth source + 2 = controlledWidth source := by
  simp [markerCoreWidth, controlledWidth, markerLayout,
    Ancilla.computeCopyUncomputeWidth]

private theorem gate_layer_width {m : Nat} (source : SourceCircuit m 1) :
    ((markerLayout source).width + 1) + 3 = controlledWidth source := by
  simp [controlledWidth]

private def gateLayer (width : Nat) : Circuit (width + 4) :=
  Circuit.cast (by omega : (width + 1) + 3 = width + 4)
    (.tensor (.identity (width + 1)) .fredkin)

def markerComputation {m : Nat} (source : SourceCircuit m 1) :
    Circuit (markerCoreWidth source) :=
  Ancilla.computeCopyUncompute (markerLayout source)
    (SourceCircuit.compile source)

def controlledSwap {m : Nat} (source : SourceCircuit m 1) :
    Circuit (controlledWidth source) :=
  .seq
    (Circuit.cast (core_plus_targets_width source)
      (.tensor (markerComputation source) (.identity 2)))
    (.seq
      (gateLayer (markerLayout source).width)
      (Circuit.cast (core_plus_targets_width source)
        (.tensor (Circuit.inverse (markerComputation source)) (.identity 2))))

def pair (first second : Bool) : BitState 2 :=
  BitState.append (fun _ : Fin 1 => first) (fun _ : Fin 1 => second)

def bit (value : Bool) : BitState 1 := fun _ => value

@[simp] theorem pair_zero (first second : Bool) : pair first second 0 = first := rfl
@[simp] theorem pair_one (first second : Bool) : pair first second 1 = second := rfl

private theorem castState_self {n : Nat} (width : n = n)
    (state : BitState n) : Realization.castState width state = state := by
  have width_eq : width = rfl := Subsingleton.elim _ _
  cases width_eq
  rfl

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    Realization.castState width state index =
      state (Fin.cast width.symm index) := by
  cases width
  rfl

@[simp] private theorem castState_trans {left middle right : Nat}
    (first : left = middle) (second : middle = right)
    (state : BitState left) :
    Realization.castState second (Realization.castState first state) =
      Realization.castState (first.trans second) state := by
  cases first
  cases second
  rfl

private theorem castState_proof_irrel {left right : Nat}
    (first second : left = right) (state : BitState left) :
    Realization.castState first state = Realization.castState second state := by
  have equality : first = second := Subsingleton.elim _ _
  cases equality
  rfl

private theorem append_noBits_left {width : Nat} (state : BitState width) :
    BitState.append noBits state =
      Realization.castState (Nat.zero_add width).symm state := by
  funext index
  refine Fin.addCases (fun impossible => Fin.elim0 impossible) ?_ index
  intro inner
  rw [BitState.append_natAdd, castState_apply]
  congr 1
  apply Fin.ext
  simp

private theorem castState_append_left {a b c : Nat} (width : a = b)
    (left : BitState a) (right : BitState c) :
    Realization.castState (congrArg (fun n => n + c) width)
        (BitState.append left right) =
      BitState.append (Realization.castState width left) right := by
  cases width
  rfl

private theorem castState_append_assoc {a b c : Nat}
    (first : BitState a) (second : BitState b) (third : BitState c) :
    Realization.castState (Nat.add_assoc a b c)
        (BitState.append (BitState.append first second) third) =
      BitState.append first (BitState.append second third) := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro firstIndex
    rw [castState_apply]
    rw [show Fin.cast (Nat.add_assoc a b c).symm
          (Fin.castAdd (b + c) firstIndex) =
        Fin.castAdd c (Fin.castAdd b firstIndex) by
      apply Fin.ext
      rfl]
    simp
  · intro remaining
    refine Fin.addCases ?_ ?_ remaining
    · intro secondIndex
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c).symm
            (Fin.natAdd a (Fin.castAdd c secondIndex)) =
          Fin.castAdd c (Fin.natAdd a secondIndex) by
        apply Fin.ext
        rfl]
      simp
    · intro thirdIndex
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c).symm
            (Fin.natAdd a (Fin.natAdd b thirdIndex)) =
          Fin.natAdd (a + b) thirdIndex by
        apply Fin.ext
        simp [Nat.add_assoc]]
      simp

private theorem castState_flatten_four {a b c d total : Nat}
    (as : BitState a) (bs : BitState b) (cs : BitState c) (ds : BitState d)
    (leftWidth : (a + b) + (c + d) = total)
    (rightWidth : (((a + b) + c) + d) = total) :
    Realization.castState leftWidth
        (BitState.append (BitState.append as bs) (BitState.append cs ds)) =
      Realization.castState rightWidth
        (BitState.append
          (BitState.append (BitState.append as bs) cs) ds) := by
  have assoc := castState_append_assoc (BitState.append as bs) cs ds
  calc
    Realization.castState leftWidth
        (BitState.append (BitState.append as bs) (BitState.append cs ds)) =
      Realization.castState leftWidth
        (Realization.castState (Nat.add_assoc (a + b) c d)
          (BitState.append
            (BitState.append (BitState.append as bs) cs) ds)) := by
        exact congrArg (Realization.castState leftWidth) assoc.symm
    _ = Realization.castState
        ((Nat.add_assoc (a + b) c d).trans leftWidth)
        (BitState.append
          (BitState.append (BitState.append as bs) cs) ds) :=
      castState_trans _ _ _
    _ = Realization.castState rightWidth
        (BitState.append
          (BitState.append (BitState.append as bs) cs) ds) :=
      castState_proof_irrel _ _ _

private theorem regroup_gate_input {w : Nat} (main : BitState w)
    (predicate complement first second : Bool) :
    Realization.castState
        (by omega : (w + (1 + 1)) + 2 = w + 4)
        (BitState.append
          (BitState.append main
            (BitState.append (bit predicate) (bit complement)))
          (pair first second)) =
      Realization.castState
        (by omega : (w + 1) + 3 = w + 4)
        (BitState.append (BitState.append main (bit predicate))
          (PaperFredkin.state complement first second)) := by
  let predicateBit := bit predicate
  let complementBit := bit complement
  let targets := pair first second
  have outerLeft :=
    castState_append_assoc main
      (BitState.append predicateBit complementBit) targets
  have inner := castState_append_assoc predicateBit complementBit targets
  have outerRight :=
    castState_append_assoc main predicateBit
      (BitState.append complementBit targets)
  have normalized := outerLeft.trans
    ((congrArg (BitState.append main) inner).trans outerRight.symm)
  have state_eq : BitState.append complementBit targets =
      PaperFredkin.state complement first second := by
    rfl
  rw [← state_eq]
  simpa [predicateBit, complementBit, targets, castState_self,
    Realization.castState] using normalized

private theorem gateLayer_spec {w : Nat} (main : BitState w)
    (predicate first second : Bool) :
    Circuit.eval (gateLayer w)
        (Realization.castState
          (by omega : (w + (1 + 1)) + 2 = w + 4)
          (BitState.append
            (BitState.append main
              (BitState.append (bit predicate) (bit (!predicate))))
            (pair first second))) =
      Realization.castState
        (by omega : (w + (1 + 1)) + 2 = w + 4)
        (BitState.append
          (BitState.append main
            (BitState.append (bit predicate) (bit (!predicate))))
          (pair
            (if predicate = true then second else first)
            (if predicate = true then first else second))) := by
  unfold gateLayer
  rw [regroup_gate_input main predicate (!predicate) first second]
  rw [Circuit.eval_cast, Circuit.eval_tensor_append,
    Circuit.eval_identity, Circuit.eval_fredkin, PaperFredkin.table]
  cases predicate <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Nat.reduceAdd]
  · rw [regroup_gate_input main false true first second]
  · rw [regroup_gate_input main true false second first]

def controlledInput {m : Nat} (source : SourceCircuit m 1)
    (argument : BitState m) (first second : Bool) :
    BitState (controlledWidth source) :=
  Realization.castState (core_plus_targets_width source)
    (BitState.append
      (BitState.append
        ((markerLayout source).packInput noBits
          (SourceCircuit.sourceState source) argument)
        (resultRegisterInput 1))
      (pair first second))

def literal (expected : Bool) : SourceCircuit 1 1 :=
  if expected = true then .identity 1 else .notGate

@[simp] theorem literal_spec (expected actual : Bool) :
    SourceCircuit.eval (literal expected) (bit actual) 0 = true ↔
      actual = expected := by
  cases expected <;> cases actual <;> decide

def patternMatch : {m : Nat} → BitState m → SourceCircuit m 1
  | 0, _ => .constant (bit true)
  | m + 1, pattern =>
      .seq
        (.tensor
          (patternMatch (fun index : Fin m => pattern index.castSucc))
          (literal (pattern (Fin.last m))))
        .andGate

private theorem oneState_eq_bit (state : BitState 1) :
    state = bit (state 0) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro impossible
  exact Fin.elim0 impossible

theorem patternMatch_spec {m : Nat} (pattern argument : BitState m) :
    SourceCircuit.eval (patternMatch pattern) argument 0 = true ↔
      argument = pattern := by
  induction m with
  | zero =>
      constructor
      · intro _
        funext index
        exact Fin.elim0 index
      · intro _
        rfl
  | succ m inductionHypothesis =>
      simp only [patternMatch, SourceCircuit.eval]
      simp only [BitState.append]
      rw [Bool.and_eq_true]
      change
        (SourceCircuit.eval
              (patternMatch (fun index : Fin m => pattern index.castSucc))
              (BitState.split m 1 argument).1 0 = true ∧
            SourceCircuit.eval (literal (pattern (Fin.last m)))
              (BitState.split m 1 argument).2 0 = true) ↔
          argument = pattern
      rw [inductionHypothesis]
      rw [oneState_eq_bit (BitState.split m 1 argument).2]
      rw [literal_spec]
      constructor
      · rintro ⟨hprefix, hlast⟩
        funext index
        refine Fin.lastCases ?_ (fun inner => ?_) index
        · have last_index : Fin.natAdd m (0 : Fin 1) = Fin.last m := by
            apply Fin.ext
            simp
          calc
            argument (Fin.last m) = argument (Fin.natAdd m 0) :=
              congrArg argument last_index.symm
            _ = pattern (Fin.last m) := by
              simpa [BitState.split] using hlast
        · have prefix_index : Fin.castAdd 1 inner = inner.castSucc := by
            apply Fin.ext
            rfl
          calc
            argument inner.castSucc = argument (Fin.castAdd 1 inner) :=
              congrArg argument prefix_index.symm
            _ = pattern inner.castSucc := by
              simpa [BitState.split] using congrFun hprefix inner
      · intro equality
        subst argument
        constructor
        · funext index
          have prefix_index : Fin.castAdd 1 index = index.castSucc := by
            apply Fin.ext
            rfl
          simpa [BitState.split] using congrArg pattern prefix_index
        · have last_index : Fin.natAdd m (0 : Fin 1) = Fin.last m := by
            apply Fin.ext
            simp
          simpa [BitState.split] using congrArg pattern last_index

theorem patternMatch_sourceWidth_le {m : Nat} (pattern : BitState m) :
    SourceCircuit.sourceWidth (patternMatch pattern) ≤ 3 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m inductionHypothesis =>
      simp only [patternMatch, SourceCircuit.sourceWidth]
      by_cases expected : pattern (Fin.last m) = true
      · simp [literal, expected, SourceCircuit.sourceWidth]
        have bound := inductionHypothesis
          (fun index : Fin m => pattern index.castSucc)
        omega
      · simp [literal, expected, SourceCircuit.sourceWidth]
        have bound := inductionHypothesis
          (fun index : Fin m => pattern index.castSucc)
        omega

theorem controlledSwap_spec {m : Nat} (source : SourceCircuit m 1)
    (argument : BitState m) (first second : Bool) :
    Circuit.eval (controlledSwap source)
        (controlledInput source argument first second) =
      controlledInput source argument
        (if SourceCircuit.eval source argument 0 = true then second else first)
        (if SourceCircuit.eval source argument 0 = true then first else second) := by
  have marker_spec :
      Circuit.eval (markerComputation source)
          (BitState.append
            ((markerLayout source).packInput noBits
              (SourceCircuit.sourceState source) argument)
            (resultRegisterInput 1)) =
        BitState.append
          ((markerLayout source).packInput noBits
            (SourceCircuit.sourceState source) argument)
          (resultRegisterOutput (SourceCircuit.eval source argument)) := by
    simpa [markerComputation, markerLayout] using
      (Ancilla.compute_copy_uncompute_spec
        (SourceCircuit.compile_realizes source) argument)
  unfold controlledSwap controlledInput
  simp only [Circuit.eval_seq]
  rw [Circuit.eval_cast]
  rw [Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [marker_spec]
  generalize value_eq : SourceCircuit.eval source argument 0 = value
  have source_eval_eq : SourceCircuit.eval source argument = (fun _ => value) := by
    funext index
    refine Fin.cases value_eq ?_ index
    intro impossible
    exact Fin.elim0 impossible
  have result_output_eq :
      resultRegisterOutput (fun _ : Fin 1 => value) =
        BitState.append (bit value) (bit (!value)) := by
    rfl
  have marker_spec_value :
      Circuit.eval (markerComputation source)
          (BitState.append
            ((markerLayout source).packInput noBits
              (SourceCircuit.sourceState source) argument)
            (resultRegisterInput 1)) =
        BitState.append
          ((markerLayout source).packInput noBits
            (SourceCircuit.sourceState source) argument)
          (BitState.append (bit value) (bit (!value))) := by
    rw [marker_spec, source_eval_eq, result_output_eq]
  rw [source_eval_eq]
  rw [result_output_eq, gateLayer_spec]
  rw [Circuit.eval_cast, Circuit.eval_tensor_append,
    Circuit.eval_identity]
  rw [← marker_spec_value, Circuit.eval_inverse_eval]

theorem patternControlledSwap_spec {m : Nat}
    (pattern argument : BitState m) (first second : Bool) :
    Circuit.eval (controlledSwap (patternMatch pattern))
        (controlledInput (patternMatch pattern) argument first second) =
      controlledInput (patternMatch pattern) argument
        (if argument = pattern then second else first)
        (if argument = pattern then first else second) := by
  rw [controlledSwap_spec]
  have equality_test :
      SourceCircuit.eval (patternMatch pattern) argument 0 = true ↔
        argument = pattern := patternMatch_spec pattern argument
  by_cases equality : argument = pattern
  · have is_true :
        SourceCircuit.eval (patternMatch pattern) argument 0 = true :=
      equality_test.mpr equality
    rw [if_pos is_true, if_pos equality]
    simp only [if_pos is_true, if_pos equality]
  · have not_true :
        SourceCircuit.eval (patternMatch pattern) argument 0 ≠ true := by
      exact fun is_true => equality (equality_test.mp is_true)
    simp [equality, not_true]

/-! A clean canonical adjacent-state transposition. -/

abbrev edgeSource {m : Nat} (pattern : BitState m) : SourceCircuit m 1 :=
  patternMatch pattern

abbrev edgeWidth {m : Nat} (pattern : BitState m) : Nat :=
  (SourceCircuit.sourceWidth (edgeSource pattern) + 2) + (m + 2)

private theorem controlled_to_edge_width {m : Nat} (pattern : BitState m) :
    controlledWidth (edgeSource pattern) = edgeWidth pattern := by
  simp [controlledWidth, edgeSource, edgeWidth, Realization.Layout.width]
  omega

def edgeClean {m : Nat} (pattern : BitState m) :
    BitState (SourceCircuit.sourceWidth (edgeSource pattern) + 2) :=
  BitState.append (SourceCircuit.sourceState (edgeSource pattern))
    (resultRegisterInput 1)

theorem edgeClean_width_le {m : Nat} (pattern : BitState m) :
    SourceCircuit.sourceWidth (edgeSource pattern) + 2 ≤ 3 * m + 3 := by
  change SourceCircuit.sourceWidth (patternMatch pattern) + 2 ≤ 3 * m + 3
  have bound := patternMatch_sourceWidth_le pattern
  omega

theorem edgeWidth_le {m : Nat} (pattern : BitState m) :
    edgeWidth pattern ≤ 4 * m + 5 := by
  have bound := patternMatch_sourceWidth_le pattern
  simp only [edgeWidth, edgeSource]
  omega

def edgeData {m : Nat} (head : BitState m) (first second : Bool) :
    BitState (m + 2) :=
  BitState.append head (pair first second)

def edgeState {m : Nat} (pattern : BitState m) (head : BitState m)
    (first second : Bool) : BitState (edgeWidth pattern) :=
  BitState.append (edgeClean pattern) (edgeData head first second)

def edgeRouteWiring {m : Nat} (pattern : BitState m) :
    WirePerm (edgeWidth pattern) :=
  Circuit.middleSwapWiring
    (SourceCircuit.sourceWidth (edgeSource pattern)) 2 m 2

def edgeRoute {m : Nat} (pattern : BitState m) : Circuit (edgeWidth pattern) :=
  .permute (edgeRouteWiring pattern)

def edgeControlled {m : Nat} (pattern : BitState m) :
    Circuit (edgeWidth pattern) :=
  Circuit.cast (controlled_to_edge_width pattern)
    (controlledSwap (edgeSource pattern))

def edgeControlledState {m : Nat} (pattern : BitState m)
    (head : BitState m) (first second : Bool) : BitState (edgeWidth pattern) :=
  Realization.castState (controlled_to_edge_width pattern)
    (controlledInput (edgeSource pattern) head first second)

theorem edgeRoute_spec {m : Nat} (pattern head : BitState m)
    (first second : Bool) :
    Circuit.eval (edgeRoute pattern) (edgeState pattern head first second) =
      edgeControlledState pattern head first second := by
  unfold edgeRoute edgeRouteWiring edgeState edgeClean edgeData
  rw [Circuit.eval_permute]
  rw [Circuit.middleSwapWiring_on_append]
  unfold edgeControlledState controlledInput
  simp only [markerLayout, Realization.Layout.packInput]
  rw [append_noBits_left]
  rw [← castState_append_left]
  rw [← castState_append_left]
  simp only [castState_trans]
  apply castState_flatten_four

theorem edgeControlled_spec {m : Nat} (pattern head : BitState m)
    (first second : Bool) :
    Circuit.eval (edgeControlled pattern)
        (edgeControlledState pattern head first second) =
      edgeControlledState pattern head
        (if head = pattern then second else first)
        (if head = pattern then first else second) := by
  unfold edgeControlled edgeControlledState
  rw [Circuit.eval_cast]
  rw [patternControlledSwap_spec]

def adjacentTranspositionCircuit {m : Nat} (pattern : BitState m) :
    Circuit (edgeWidth pattern) :=
  .seq (edgeRoute pattern)
    (.seq (edgeControlled pattern) (Circuit.inverse (edgeRoute pattern)))

theorem adjacentTranspositionCircuit_structured_spec {m : Nat}
    (pattern head : BitState m) (first second : Bool) :
    Circuit.eval (adjacentTranspositionCircuit pattern)
        (edgeState pattern head first second) =
      edgeState pattern head
        (if head = pattern then second else first)
        (if head = pattern then first else second) := by
  unfold adjacentTranspositionCircuit
  simp only [Circuit.eval_seq]
  rw [edgeRoute_spec, edgeControlled_spec]
  rw [← edgeRoute_spec]
  exact Circuit.eval_inverse_eval (edgeRoute pattern) _

private theorem edgeData_head_injective {m : Nat}
    {leftHead rightHead : BitState m} {leftFirst leftSecond rightFirst rightSecond : Bool}
    (equality : edgeData leftHead leftFirst leftSecond =
      edgeData rightHead rightFirst rightSecond) :
    leftHead = rightHead := by
  have splitEquality := congrArg (BitState.split m 2) equality
  simpa [edgeData] using congrArg Prod.fst splitEquality

private theorem edgeData_first_eq {m : Nat} (head : BitState m)
    (first second : Bool) :
    edgeData head first second (Fin.natAdd m 0) = first := by
  rw [edgeData, BitState.append_natAdd]
  exact pair_zero first second

private theorem edgeData_second_eq {m : Nat} (head : BitState m)
    (first second : Bool) :
    edgeData head first second (Fin.natAdd m 1) = second := by
  rw [edgeData, BitState.append_natAdd]
  exact pair_one first second

private theorem adjacentData_ne {m : Nat} (pattern : BitState m) :
    edgeData pattern false true ≠ edgeData pattern true false := by
  intro equality
  have coordinate := congrFun equality (Fin.natAdd m 0)
  simp [edgeData_first_eq] at coordinate

private theorem edgeData_conditional_swap {m : Nat}
    (pattern head : BitState m) (first second : Bool) :
    edgeData head
        (if head = pattern then second else first)
        (if head = pattern then first else second) =
      Equiv.swap (edgeData pattern false true) (edgeData pattern true false)
        (edgeData head first second) := by
  by_cases head_eq : head = pattern
  · subst head
    cases first <;> cases second
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · simp
      · intro equality
        have coordinate := congrFun equality (Fin.natAdd m 1)
        simp [edgeData_second_eq] at coordinate
      · intro equality
        have coordinate := congrFun equality (Fin.natAdd m 0)
        simp [edgeData_first_eq] at coordinate
    · rw [Equiv.swap_apply_left]
      simp
    · rw [Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · simp
      · intro equality
        have coordinate := congrFun equality (Fin.natAdd m 0)
        simp [edgeData_first_eq] at coordinate
      · intro equality
        have coordinate := congrFun equality (Fin.natAdd m 1)
        simp [edgeData_second_eq] at coordinate
  · simp only [if_neg head_eq]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro equality
      exact head_eq (edgeData_head_injective equality)
    · intro equality
      exact head_eq (edgeData_head_injective equality)

private theorem twoState_eq_pair (state : BitState 2) :
    state = pair (state 0) (state 1) := by
  funext index
  refine Fin.cases rfl ?_ index
  intro tail
  refine Fin.cases rfl ?_ tail
  intro impossible
  exact Fin.elim0 impossible

/-- Exact clean realization of the adjacent equal-prefix state transposition. -/
theorem adjacentTranspositionCircuit_spec {m : Nat}
    (pattern : BitState m) (data : BitState (m + 2)) :
    Circuit.eval (adjacentTranspositionCircuit pattern)
        (BitState.append (edgeClean pattern) data) =
      BitState.append (edgeClean pattern)
        (Equiv.swap (edgeData pattern false true)
          (edgeData pattern true false) data) := by
  let head := (BitState.split m 2 data).1
  let targets := (BitState.split m 2 data).2
  let first := targets 0
  let second := targets 1
  have targets_eq : targets = pair first second := by
    exact twoState_eq_pair targets
  have data_eq : data = edgeData head first second := by
    unfold edgeData
    rw [← targets_eq]
    exact (BitState.append_split data).symm
  rw [data_eq]
  change Circuit.eval (adjacentTranspositionCircuit pattern)
      (edgeState pattern head first second) = _
  rw [adjacentTranspositionCircuit_structured_spec]
  unfold edgeState
  apply congrArg (BitState.append (edgeClean pattern))
  exact edgeData_conditional_swap pattern head first second

private theorem hasLatency_castCircuit {leftWidth rightWidth latency : Nat}
    (width : leftWidth = rightWidth) {circuit : Circuit leftWidth}
    (timed : Circuit.HasLatency circuit latency) :
    Circuit.HasLatency (Circuit.cast width circuit) latency := by
  cases width
  exact timed

private theorem hasLatency_seq_zero {width : Nat}
    {first second : Circuit width}
    (firstTimed : Circuit.HasLatency first 0)
    (secondTimed : Circuit.HasLatency second 0) :
    Circuit.HasLatency (.seq first second) 0 := by
  intro input output actual path
  simpa using Circuit.HasLatency.seq firstTimed secondTimed path

private theorem hasLatency_tensor_zero {leftWidth rightWidth : Nat}
    {left : Circuit leftWidth} {right : Circuit rightWidth}
    (leftTimed : Circuit.HasLatency left 0)
    (rightTimed : Circuit.HasLatency right 0) :
    Circuit.HasLatency (.tensor left right) 0 := by
  intro input output actual path
  exact Circuit.HasLatency.tensor leftTimed rightTimed path

private theorem markerComputation_hasLatency_zero {m : Nat}
    (source : SourceCircuit m 1) :
    Circuit.HasLatency (markerComputation source) 0 := by
  unfold markerComputation
  exact Ancilla.computeCopyUncompute_hasLatency_zero _
    (SourceCircuit.compile_hasLatency_zero source)

private theorem gateLayer_hasLatency_zero (width : Nat) :
    Circuit.HasLatency (gateLayer width) 0 := by
  unfold gateLayer
  apply hasLatency_castCircuit
  exact hasLatency_tensor_zero (Circuit.hasLatency_identity (width + 1))
    Circuit.hasLatency_fredkin

private theorem controlledSwap_hasLatency_zero {m : Nat}
    (source : SourceCircuit m 1) :
    Circuit.HasLatency (controlledSwap source) 0 := by
  unfold controlledSwap
  apply hasLatency_seq_zero
  · apply hasLatency_castCircuit
    exact hasLatency_tensor_zero (markerComputation_hasLatency_zero source)
      (Circuit.hasLatency_identity 2)
  · apply hasLatency_seq_zero
    · exact gateLayer_hasLatency_zero _
    · apply hasLatency_castCircuit
      exact hasLatency_tensor_zero
        (Circuit.HasLatency.inverse (markerComputation_hasLatency_zero source))
        (Circuit.hasLatency_identity 2)

/-- The adjacent-transposition construction has zero unit-wire latency. -/
theorem adjacentTranspositionCircuit_hasLatency_zero {m : Nat}
    (pattern : BitState m) :
    Circuit.HasLatency (adjacentTranspositionCircuit pattern) 0 := by
  unfold adjacentTranspositionCircuit edgeControlled edgeRoute
  apply hasLatency_seq_zero
  · exact Circuit.hasLatency_permute _
  · apply hasLatency_seq_zero
    · apply hasLatency_castCircuit
      exact controlledSwap_hasLatency_zero _
    · exact Circuit.HasLatency.inverse (Circuit.hasLatency_permute _)

private theorem fredkinCount_inverse {width : Nat} (circuit : Circuit width) :
    Circuit.fredkinCount (Circuit.inverse circuit) =
      Circuit.fredkinCount circuit := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => rfl
  | permute wiring => rfl
  | seq first second firstIH secondIH =>
      simp [Circuit.inverse_seq, Circuit.fredkinCount, firstIH, secondIH,
        Nat.add_comm]
  | tensor left right leftIH rightIH =>
      simp [Circuit.inverse_tensor, Circuit.fredkinCount, leftIH, rightIH]

private theorem gateLayer_fredkinCount (width : Nat) :
    Circuit.fredkinCount (gateLayer width) = 1 := by
  simp [gateLayer, Circuit.fredkinCount]

private theorem markerComputation_fredkinCount {m : Nat}
    (source : SourceCircuit m 1) :
    Circuit.fredkinCount (markerComputation source) =
      2 * SourceCircuit.logicGateCount source + 1 := by
  unfold markerComputation
  rw [Ancilla.computeCopyUncompute_fredkinCount,
    SourceCircuit.compile_fredkinCount]
  change SourceCircuit.logicGateCount source +
      (1 + SourceCircuit.logicGateCount source) =
    2 * SourceCircuit.logicGateCount source + 1
  omega

private theorem controlledSwap_fredkinCount {m : Nat}
    (source : SourceCircuit m 1) :
    Circuit.fredkinCount (controlledSwap source) =
      4 * SourceCircuit.logicGateCount source + 3 := by
  unfold controlledSwap
  simp only [Circuit.fredkinCount, Circuit.fredkinCount_castCircuit,
    markerComputation_fredkinCount, gateLayer_fredkinCount,
    fredkinCount_inverse]
  omega

/-- Exact paper-Fredkin syntax count for the clean adjacent transposition. -/
theorem adjacentTranspositionCircuit_fredkinCount {m : Nat}
    (pattern : BitState m) :
    Circuit.fredkinCount (adjacentTranspositionCircuit pattern) =
      4 * SourceCircuit.logicGateCount (patternMatch pattern) + 3 := by
  unfold adjacentTranspositionCircuit edgeRoute edgeControlled
  simp [Circuit.fredkinCount, controlledSwap_fredkinCount]

/--
The adjacent equal-prefix state swap has a finite paper-Fredkin realization
with one explicit ancillary prefix returned exactly.
-/
theorem adjacentTranspositionClean {m : Nat} (pattern : BitState m) :
    CleanFredkinRealizable
      (Equiv.swap (edgeData pattern false true)
        (edgeData pattern true false)) := by
  refine ⟨{
    ancillaWidth := SourceCircuit.sourceWidth (edgeSource pattern) + 2
    ancillaInit := edgeClean pattern
    circuit := adjacentTranspositionCircuit pattern
    structural := Circuit.fredkinStructural_of_hasLatency_zero _
      (adjacentTranspositionCircuit_hasLatency_zero pattern)
    latencyZero := adjacentTranspositionCircuit_hasLatency_zero pattern
    realizes := adjacentTranspositionCircuit_spec pattern
  }⟩

namespace CleanFredkinRealization

/-- Conjugate a clean realization by an explicit structural data-wire route. -/
def wireConjugate {width : Nat} {gate : Reversible width}
    (realization : CleanFredkinRealization gate) (wiring : WirePerm width) :
    CleanFredkinRealization
      ((WirePerm.onState wiring).trans gate |>.trans
        (WirePerm.onState wiring).symm) where
  ancillaWidth := realization.ancillaWidth
  ancillaInit := realization.ancillaInit
  circuit := .seq
    (.tensor (.identity realization.ancillaWidth) (.permute wiring))
    (.seq realization.circuit
      (.tensor (.identity realization.ancillaWidth) (.permute wiring.symm)))
  structural := by simp [realization.structural]
  latencyZero := by
    apply hasLatency_seq_zero
    · exact hasLatency_tensor_zero (Circuit.hasLatency_identity _)
        (Circuit.hasLatency_permute wiring)
    · apply hasLatency_seq_zero
      · exact realization.latencyZero
      · exact hasLatency_tensor_zero (Circuit.hasLatency_identity _)
          (Circuit.hasLatency_permute wiring.symm)
  realizes state := by
    simp only [Circuit.eval_seq, Circuit.eval_tensor_append,
      Circuit.eval_identity, Circuit.eval_permute]
    rw [realization.realizes]
    rw [Circuit.eval_tensor_append, Circuit.eval_identity,
      Circuit.eval_permute]
    rw [WirePerm.onState_inverse]
    rfl

end CleanFredkinRealization

private def finalDataSwap (m : Nat) : WirePerm (m + 2) :=
  Equiv.swap (Fin.natAdd m (0 : Fin 2)) (Fin.natAdd m (1 : Fin 2))

private theorem finalDataSwap_edgeData {m : Nat} (head : BitState m)
    (first second : Bool) :
    WirePerm.onState (finalDataSwap m) (edgeData head first second) =
      edgeData head second first := by
  funext output
  refine Fin.addCases ?_ ?_ output
  · intro index
    rw [WirePerm.onState_apply]
    have neFirst : Fin.castAdd 2 index ≠ Fin.natAdd m (0 : Fin 2) := by
      intro equality
      have values := congrArg Fin.val equality
      simp at values
      omega
    have neSecond : Fin.castAdd 2 index ≠ Fin.natAdd m (1 : Fin 2) := by
      intro equality
      have values := congrArg Fin.val equality
      simp at values
      omega
    rw [show (finalDataSwap m).symm = finalDataSwap m by rfl]
    unfold finalDataSwap
    rw [Equiv.swap_apply_of_ne_of_ne neFirst neSecond]
    simp [edgeData]
  · intro index
    refine Fin.cases ?_ ?_ index
    · rw [WirePerm.onState_apply]
      rw [show (finalDataSwap m).symm = finalDataSwap m by rfl]
      rw [show finalDataSwap m (Fin.natAdd m (0 : Fin 2)) =
          Fin.natAdd m (1 : Fin 2) by
        exact Equiv.swap_apply_left _ _]
      rw [edgeData_second_eq, edgeData_first_eq]
    · intro tail
      refine Fin.cases ?_ ?_ tail
      · rw [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 by rfl]
        rw [WirePerm.onState_apply]
        rw [show (finalDataSwap m).symm = finalDataSwap m by rfl]
        rw [show finalDataSwap m (Fin.natAdd m (1 : Fin 2)) =
            Fin.natAdd m (0 : Fin 2) by
          exact Equiv.swap_apply_right _ _]
        rw [edgeData_first_eq, edgeData_second_eq]
      · intro impossible
        exact Fin.elim0 impossible

private theorem exists_wiring_to_final {m : Nat} (first second : Fin (m + 2))
    (distinct : first ≠ second) :
    ∃ wiring : WirePerm (m + 2),
      wiring first = Fin.natAdd m (0 : Fin 2) ∧
        wiring second = Fin.natAdd m (1 : Fin 2) := by
  classical
  let source : Bool → Fin (m + 2) := fun bit => if bit then second else first
  let target : Bool → Fin (m + 2) := fun bit =>
    if bit then Fin.natAdd m (1 : Fin 2) else Fin.natAdd m (0 : Fin 2)
  have sourceInjective : Function.Injective source := by
    intro left right equality
    cases left <;> cases right
    · rfl
    · dsimp only [source, Bool.false_eq_true, ↓reduceIte] at equality
      exact (distinct equality).elim
    · dsimp only [source, Bool.true_eq_false, ↓reduceIte] at equality
      exact (distinct equality.symm).elim
    · rfl
  have targetDistinct :
      Fin.natAdd m (0 : Fin 2) ≠ Fin.natAdd m (1 : Fin 2) := by
    intro equality
    have values := congrArg Fin.val equality
    simp at values
  have targetInjective : Function.Injective target := by
    intro left right equality
    cases left <;> cases right <;> simp [target] at equality ⊢
  obtain ⟨wiring, wiringSpec⟩ := Equiv.Perm.exists_extending_pair
    source target sourceInjective targetInjective
  refine ⟨wiring, ?_, ?_⟩
  · simpa [source, target] using wiringSpec false
  · simpa [source, target] using wiringSpec true

private theorem normalized_edgeData {m : Nat} (state : BitState (m + 2))
    (first second : Fin (m + 2)) (wiring : WirePerm (m + 2))
    (firstValue : state first = false) (secondValue : state second = true)
    (routeFirst : wiring first = Fin.natAdd m (0 : Fin 2))
    (routeSecond : wiring second = Fin.natAdd m (1 : Fin 2)) :
    WirePerm.onState wiring state =
      edgeData (BitState.split m 2 (WirePerm.onState wiring state)).1
        false true := by
  let normalized := WirePerm.onState wiring state
  let head := (BitState.split m 2 normalized).1
  let targets := (BitState.split m 2 normalized).2
  have targets_eq : targets = pair false true := by
    funext index
    refine Fin.cases ?_ ?_ index
    · change normalized (Fin.natAdd m (0 : Fin 2)) = false
      rw [← routeFirst]
      exact (WirePerm.onState_apply_image wiring state first).trans firstValue
    · intro tail
      refine Fin.cases ?_ ?_ tail
      · change normalized (Fin.natAdd m (Fin.succ (0 : Fin 1))) = true
        rw [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 by rfl]
        rw [← routeSecond]
        exact (WirePerm.onState_apply_image wiring state second).trans secondValue
      · intro impossible
        exact Fin.elim0 impossible
  change normalized = edgeData head false true
  unfold edgeData
  rw [← targets_eq]
  exact (BitState.append_split normalized).symm

private theorem swap_trans_wiring {m : Nat} (first second : Fin (m + 2))
    (wiring : WirePerm (m + 2))
    (routeFirst : wiring first = Fin.natAdd m (0 : Fin 2))
    (routeSecond : wiring second = Fin.natAdd m (1 : Fin 2)) :
    (Equiv.swap first second).trans wiring =
      wiring.trans (finalDataSwap m) := by
  have conjugated := Equiv.symm_trans_swap_trans first second wiring
  rw [routeFirst, routeSecond] at conjugated
  apply Equiv.ext
  intro index
  have pointwise := congrArg
    (fun permutation : WirePerm (m + 2) => permutation (wiring index))
    conjugated
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, finalDataSwap]
    using pointwise

private theorem normalized_swapped_edgeData {m : Nat}
    (state : BitState (m + 2)) (first second : Fin (m + 2))
    (wiring : WirePerm (m + 2))
    (firstValue : state first = false) (secondValue : state second = true)
    (routeFirst : wiring first = Fin.natAdd m (0 : Fin 2))
    (routeSecond : wiring second = Fin.natAdd m (1 : Fin 2)) :
    WirePerm.onState wiring
        (WirePerm.onState (Equiv.swap first second) state) =
      edgeData (BitState.split m 2 (WirePerm.onState wiring state)).1
        true false := by
  have normalized := normalized_edgeData state first second wiring
    firstValue secondValue routeFirst routeSecond
  calc
    WirePerm.onState wiring
        (WirePerm.onState (Equiv.swap first second) state) =
      WirePerm.onState ((Equiv.swap first second).trans wiring) state := by
        rw [WirePerm.onState_comp]
        rfl
    _ = WirePerm.onState (wiring.trans (finalDataSwap m)) state := by
      rw [swap_trans_wiring first second wiring routeFirst routeSecond]
    _ = WirePerm.onState (finalDataSwap m)
        (WirePerm.onState wiring state) := by
      rw [WirePerm.onState_comp]
      rfl
    _ = WirePerm.onState (finalDataSwap m)
        (edgeData (BitState.split m 2
          (WirePerm.onState wiring state)).1 false true) := by
      exact congrArg (WirePerm.onState (finalDataSwap m)) normalized
    _ = edgeData (BitState.split m 2
          (WirePerm.onState wiring state)).1 true false :=
      finalDataSwap_edgeData _ false true

private theorem singleExchangeClean_ordered {m : Nat}
    (state : BitState (m + 2)) (first second : Fin (m + 2))
    (distinct : first ≠ second)
    (firstValue : state first = false) (secondValue : state second = true) :
    CleanFredkinRealizable
      (Equiv.swap state
        (WirePerm.onState (Equiv.swap first second) state)) := by
  classical
  obtain ⟨wiring, routeFirst, routeSecond⟩ :=
    exists_wiring_to_final first second distinct
  let normalized := WirePerm.onState wiring state
  let pattern := (BitState.split m 2 normalized).1
  have normalizedState :
      WirePerm.onState wiring state = edgeData pattern false true := by
    simpa only [pattern, normalized] using
      normalized_edgeData state first second wiring firstValue secondValue
        routeFirst routeSecond
  have normalizedSwap :
      WirePerm.onState wiring
          (WirePerm.onState (Equiv.swap first second) state) =
        edgeData pattern true false := by
    simpa only [pattern, normalized] using
      normalized_swapped_edgeData state first second wiring firstValue secondValue
        routeFirst routeSecond
  have endpointFirst :
      (WirePerm.onState wiring).symm (edgeData pattern false true) = state := by
    rw [← normalizedState]
    exact Equiv.symm_apply_apply _ _
  have endpointSecond :
      (WirePerm.onState wiring).symm (edgeData pattern true false) =
        WirePerm.onState (Equiv.swap first second) state := by
    rw [← normalizedSwap]
    exact Equiv.symm_apply_apply _ _
  have gateEq :
      ((WirePerm.onState wiring).trans
          (Equiv.swap (edgeData pattern false true)
            (edgeData pattern true false))).trans
          (WirePerm.onState wiring).symm =
        Equiv.swap state
          (WirePerm.onState (Equiv.swap first second) state) := by
    rw [Equiv.trans_swap_trans_symm, endpointFirst, endpointSecond]
  rw [← gateEq]
  obtain ⟨canonical⟩ := adjacentTranspositionClean pattern
  exact ⟨canonical.wireConjugate wiring⟩

/--
Swapping two oppositely valued coordinates of one word produces a cleanly
realizable transposition of that word with the resulting word.
-/
theorem singleExchangeClean {n : Nat} (x y : BitState n) (i j : Fin n)
    (distinct : i ≠ j) (different : x i ≠ x j)
    (exchange : y = WirePerm.onState (Equiv.swap i j) x) :
    CleanFredkinRealizable (Equiv.swap x y) := by
  classical
  subst y
  have valueDistinct : i.val ≠ j.val := by
    intro equality
    exact distinct (Fin.ext equality)
  have widthAtLeastTwo : 2 ≤ n := by
    rcases lt_or_gt_of_ne valueDistinct with order | order
    · omega
    · omega
  obtain ⟨m, widthEq⟩ := Nat.exists_eq_add_of_le widthAtLeastTwo
  have widthEq' : n = m + 2 := by omega
  clear widthEq
  subst n
  cases firstValue : x i <;> cases secondValue : x j
  · exact (different (firstValue.trans secondValue.symm)).elim
  · exact singleExchangeClean_ordered x i j distinct firstValue secondValue
  · have realization := singleExchangeClean_ordered x j i distinct.symm
      secondValue firstValue
    rw [Equiv.swap_comm j i] at realization
    exact realization
  · exact (different (firstValue.trans secondValue.symm)).elim

end Completeness.Adjacent
end ConservativeLogic
