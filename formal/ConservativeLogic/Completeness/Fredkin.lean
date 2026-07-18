import Mathlib.GroupTheory.Perm.ClosureSwap
import ConservativeLogic.Completeness.Semantic

/-!
# Clean Fredkin-basis synthesis

This module proves the fixed-basis half of finite conservative completeness.
The permitted syntax is the paper's zero-controlled Fredkin gate together with
identity, serial/tensor composition, and explicit structural wire
reindexing.  Structural reindexing is an admitted routing convention; it is
not claimed to be a physical Fredkin network.

Ancillas are explicit, may contain both zeroes and ones, and are returned
bit-for-bit.  The construction is finite and classical.  It does not claim an
optimal ancillary width, an all-zero initialization, or a physical cost bound.
-/

namespace ConservativeLogic

namespace Circuit

/-- Syntax certificate for the fixed Fredkin-plus-structural-reindexing basis. -/
def FredkinStructural : {width : Nat} → Circuit width → Prop
  | _, .identity _ => True
  | _, .unitWire => False
  | _, .fredkin => True
  | _, .permute _ => True
  | _, .seq first second => FredkinStructural first ∧ FredkinStructural second
  | _, .tensor left right => FredkinStructural left ∧ FredkinStructural right

@[simp] theorem fredkinStructural_identity (width : Nat) :
    FredkinStructural (.identity width) := trivial

@[simp] theorem fredkinStructural_fredkin :
    FredkinStructural .fredkin := trivial

@[simp] theorem fredkinStructural_permute {width : Nat} (wiring : WirePerm width) :
    FredkinStructural (.permute wiring) := trivial

@[simp] theorem fredkinStructural_seq {width : Nat} (first second : Circuit width) :
    FredkinStructural (.seq first second) ↔
      FredkinStructural first ∧ FredkinStructural second :=
  Iff.rfl

@[simp] theorem fredkinStructural_tensor {m n : Nat}
    (left : Circuit m) (right : Circuit n) :
    FredkinStructural (.tensor left right) ↔
      FredkinStructural left ∧ FredkinStructural right :=
  Iff.rfl

@[simp] theorem fredkinStructural_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth) :
    FredkinStructural (Simulation.castCircuit width circuit) ↔
      FredkinStructural circuit := by
  cases width
  rfl

@[simp] theorem fredkinStructural_inverse {width : Nat} (circuit : Circuit width) :
    FredkinStructural (Circuit.inverse circuit) ↔ FredkinStructural circuit := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => rfl
  | permute wiring => rfl
  | seq first second firstIH secondIH => simp [firstIH, secondIH, and_comm]
  | tensor left right leftIH rightIH => simp [leftIH, rightIH]

private theorem exists_path_from {width : Nat} (circuit : Circuit width)
    (input : Fin width) :
    ∃ output delay, PathDelay circuit input output delay := by
  induction circuit with
  | identity width => exact ⟨input, 0, PathDelay.identity input⟩
  | unitWire => exact ⟨0, 1, PathDelay.unitWire_one⟩
  | fredkin => exact ⟨0, 0, PathDelay.fredkin input 0⟩
  | permute wiring => exact ⟨wiring input, 0, PathDelay.permute wiring input⟩
  | seq first second firstIH secondIH =>
      obtain ⟨middle, firstDelay, firstPath⟩ := firstIH input
      obtain ⟨output, secondDelay, secondPath⟩ := secondIH middle
      exact ⟨output, firstDelay + secondDelay,
        PathDelay.seq firstPath secondPath⟩
  | @tensor leftWidth rightWidth left right leftIH rightIH =>
      refine Fin.addCases ?_ ?_ input
      · intro leftInput
        obtain ⟨leftOutput, delay, path⟩ := leftIH leftInput
        exact ⟨Fin.castAdd rightWidth leftOutput, delay,
          PathDelay.tensorLeft path⟩
      · intro rightInput
        obtain ⟨rightOutput, delay, path⟩ := rightIH rightInput
        exact ⟨Fin.natAdd leftWidth rightOutput, delay,
          PathDelay.tensorRight path⟩

private theorem exists_path_to {width : Nat} (circuit : Circuit width)
    (output : Fin width) :
    ∃ input delay, PathDelay circuit input output delay := by
  induction circuit with
  | identity width => exact ⟨output, 0, PathDelay.identity output⟩
  | unitWire => exact ⟨0, 1, PathDelay.unitWire_one⟩
  | fredkin => exact ⟨0, 0, PathDelay.fredkin 0 output⟩
  | permute wiring =>
      refine ⟨wiring.symm output, 0, ?_⟩
      simpa using PathDelay.permute wiring (wiring.symm output)
  | seq first second firstIH secondIH =>
      obtain ⟨middle, secondDelay, secondPath⟩ := secondIH output
      obtain ⟨input, firstDelay, firstPath⟩ := firstIH middle
      exact ⟨input, firstDelay + secondDelay,
        PathDelay.seq firstPath secondPath⟩
  | @tensor leftWidth rightWidth left right leftIH rightIH =>
      refine Fin.addCases ?_ ?_ output
      · intro leftOutput
        obtain ⟨leftInput, delay, path⟩ := leftIH leftOutput
        exact ⟨Fin.castAdd rightWidth leftInput, delay,
          PathDelay.tensorLeft path⟩
      · intro rightOutput
        obtain ⟨rightInput, delay, path⟩ := rightIH rightOutput
        exact ⟨Fin.natAdd leftWidth rightInput, delay,
          PathDelay.tensorRight path⟩

/-- Zero path latency certifies that no `unitWire` occurs anywhere in the term. -/
theorem fredkinStructural_of_hasLatency_zero {width : Nat}
    (circuit : Circuit width) (timed : HasLatency circuit 0) :
    FredkinStructural circuit := by
  induction circuit with
  | identity width => trivial
  | unitWire =>
      have impossible := timed PathDelay.unitWire_one
      omega
  | fredkin => trivial
  | permute wiring => trivial
  | seq first second firstIH secondIH =>
      constructor
      · apply firstIH
        intro input output actual path
        obtain ⟨final, tailDelay, tailPath⟩ := exists_path_from second output
        have total := timed (PathDelay.seq path tailPath)
        omega
      · apply secondIH
        intro input output actual path
        obtain ⟨initial, headDelay, headPath⟩ := exists_path_to first input
        have total := timed (PathDelay.seq headPath path)
        omega
  | tensor left right leftIH rightIH =>
      constructor
      · apply leftIH
        intro input output actual path
        exact timed (PathDelay.tensorLeft path)
      · apply rightIH
        intro input output actual path
        exact timed (PathDelay.tensorRight path)

end Circuit

/-! ## Derived common-convention Fredkin gate -/

/--
The usual one-controlled Fredkin gate, expressed globally as the paper's
zero-controlled gate followed by an explicit structural data-wire swap.
-/
def oneControlledFredkin : Circuit 3 :=
  .seq .fredkin (.permute PaperFredkin.dataSwap)

/-- Exact common-convention truth table: true swaps and false passes through. -/
@[simp]
theorem oneControlledFredkin_spec (control first second : Bool) :
    Circuit.eval oneControlledFredkin (PaperFredkin.state control first second) =
      PaperFredkin.state control
        (if control = true then second else first)
        (if control = true then first else second) := by
  cases control <;> cases first <;> cases second <;> decide

theorem oneControlledFredkin_structural :
    Circuit.FredkinStructural oneControlledFredkin := by
  simp [oneControlledFredkin]

theorem oneControlledFredkin_hasLatency_zero :
    Circuit.HasLatency oneControlledFredkin 0 := by
  intro input output actual path
  have timed := Circuit.HasLatency.seq Circuit.hasLatency_fredkin
    (Circuit.hasLatency_permute PaperFredkin.dataSwap) path
  simpa using timed

/--
A circuit realization with one explicit ancillary prefix returned exactly.
The data block follows the ancillary block at both boundaries.
-/
structure CleanFredkinRealization {width : Nat} (gate : Reversible width) where
  ancillaWidth : Nat
  ancillaInit : BitState ancillaWidth
  circuit : Circuit (ancillaWidth + width)
  structural : Circuit.FredkinStructural circuit
  latencyZero : Circuit.HasLatency circuit 0
  realizes : ∀ state,
    Circuit.eval circuit (BitState.append ancillaInit state) =
      BitState.append ancillaInit (gate state)

/-- Existence of some finite, exactly returned clean ancillary prefix. -/
def CleanFredkinRealizable {width : Nat} (gate : Reversible width) : Prop :=
  Nonempty (CleanFredkinRealization gate)

/-- Exact restoration lets total circuit conservation cancel the clean prefix. -/
theorem CleanFredkinRealizable.weightPreserving {width : Nat}
    {gate : Reversible width} (clean : CleanFredkinRealizable gate) :
    WeightPreserving gate := by
  rcases clean with ⟨realization⟩
  intro state
  have conservation := Circuit.eval_weightPreserving realization.circuit
    (BitState.append realization.ancillaInit state)
  rw [realization.realizes] at conservation
  simp only [hammingWeight_append] at conservation
  omega

namespace CleanFredkinRealization

/-- The identity permutation needs no ancillary wires. -/
def identity (width : Nat) :
    CleanFredkinRealization (Reversible.identity width) where
  ancillaWidth := 0
  ancillaInit := fun index => Fin.elim0 index
  circuit := .identity (0 + width)
  structural := trivial
  latencyZero := Circuit.hasLatency_identity _
  realizes _ := rfl

/-- A clean realization remains clean after structural circuit inversion. -/
def inverse {width : Nat} {gate : Reversible width}
    (realization : CleanFredkinRealization gate) :
    CleanFredkinRealization gate.symm where
  ancillaWidth := realization.ancillaWidth
  ancillaInit := realization.ancillaInit
  circuit := Circuit.inverse realization.circuit
  structural := (Circuit.fredkinStructural_inverse realization.circuit).2
    realization.structural
  latencyZero := Circuit.HasLatency.inverse realization.latencyZero
  realizes state := by
    have forward := realization.realizes (gate.symm state)
    have forward' :
        Circuit.eval realization.circuit
            (BitState.append realization.ancillaInit (gate.symm state)) =
          BitState.append realization.ancillaInit state := by
      simpa using forward
    rw [← forward']
    exact Circuit.eval_inverse_eval realization.circuit _

private def emptyState : BitState 0 := fun index => Fin.elim0 index

@[simp] private theorem append_emptyState {width : Nat} (state : BitState width) :
    BitState.append state emptyState = state := by
  funext index
  refine Fin.addCases ?_ (fun impossible => Fin.elim0 impossible) index
  intro inner
  exact BitState.append_castAdd state emptyState inner

private theorem hasLatency_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) {circuit : Circuit leftWidth}
    (timed : Circuit.HasLatency circuit 0) :
    Circuit.HasLatency (Simulation.castCircuit width circuit) 0 := by
  cases width
  exact timed

private theorem hasLatency_seq_zero {width : Nat} {first second : Circuit width}
    (firstTimed : Circuit.HasLatency first 0)
    (secondTimed : Circuit.HasLatency second 0) :
    Circuit.HasLatency (.seq first second) 0 := by
  intro input output actual path
  have equality := Circuit.HasLatency.seq firstTimed secondTimed path
  simpa using equality

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    Realization.castState width state index =
      state (Fin.cast width.symm index) := by
  cases width
  rfl

private theorem castState_append_assoc_symm {a b c : Nat}
    (first : BitState a) (second : BitState b) (third : BitState c) :
    Realization.castState (Nat.add_assoc a b c).symm
        (BitState.append first (BitState.append second third)) =
      BitState.append (BitState.append first second) third := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro firstSecond
    refine Fin.addCases ?_ ?_ firstSecond
    · intro firstIndex
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c)
            (Fin.castAdd c (Fin.castAdd b firstIndex)) =
          Fin.castAdd (b + c) firstIndex by
        apply Fin.ext
        rfl]
      simp
    · intro secondIndex
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c)
            (Fin.castAdd c (Fin.natAdd a secondIndex)) =
          Fin.natAdd a (Fin.castAdd c secondIndex) by
        apply Fin.ext
        rfl]
      simp
  · intro thirdIndex
    rw [castState_apply]
    rw [show Fin.cast (Nat.add_assoc a b c)
          (Fin.natAdd (a + b) thirdIndex) =
        Fin.natAdd a (Fin.natAdd b thirdIndex) by
      apply Fin.ext
      simp [Nat.add_assoc]]
    simp

private def threeDecompose (a b c : Nat) :
    Fin ((a + b) + c) ≃ (Fin a ⊕ Fin b) ⊕ Fin c :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))

private def threeCompose (a b c : Nat) :
    (Fin a ⊕ Fin b) ⊕ Fin c ≃ Fin ((a + b) + c) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- Actively exchange the last two of three adjacent wire blocks. -/
private def middleThreeWiring (a b c : Nat) : WirePerm ((a + b) + c) :=
  (threeDecompose a b c).trans <|
    (Equiv.sumAssoc (Fin a) (Fin b) (Fin c)).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin a))
      (Equiv.sumComm (Fin b) (Fin c))).trans <|
    (Equiv.sumAssoc (Fin a) (Fin c) (Fin b)).symm.trans <|
    (threeCompose a c b).trans <|
    finCongr (by ac_rfl : (a + c) + b = (a + b) + c)

private theorem middleThreeWiring_on_append {a b c : Nat}
    (as : BitState a) (bs : BitState b) (cs : BitState c) :
    WirePerm.onState (middleThreeWiring a b c)
        (BitState.append (BitState.append as bs) cs) =
      Realization.castState (by ac_rfl : (a + c) + b = (a + b) + c)
        (BitState.append (BitState.append as cs) bs) := by
  funext output
  obtain ⟨input, rfl⟩ := (middleThreeWiring a b c).surjective output
  rw [WirePerm.onState_apply_image, castState_apply]
  let tagged := threeDecompose a b c input
  have taggedBack : (threeDecompose a b c).symm tagged = input := by
    simp [tagged]
  rcases tagged with ((index | index) | index)
  · have input_eq :
        Fin.castAdd c (Fin.castAdd b index) = input := by
      simpa [threeDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + b = (a + b) + c).symm
            (middleThreeWiring a b c
              (Fin.castAdd c (Fin.castAdd b index))) =
          Fin.castAdd b (Fin.castAdd c index) := by
      apply Fin.ext
      simp [middleThreeWiring, threeDecompose, threeCompose]
    rw [route]
    simp
  · have input_eq :
        Fin.castAdd c (Fin.natAdd a index) = input := by
      simpa [threeDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + b = (a + b) + c).symm
            (middleThreeWiring a b c
              (Fin.castAdd c (Fin.natAdd a index))) =
          Fin.natAdd (a + c) index := by
      apply Fin.ext
      simp [middleThreeWiring, threeDecompose, threeCompose]
    rw [route]
    simp
  · have input_eq : Fin.natAdd (a + b) index = input := by
      simpa [threeDecompose] using taggedBack
    clear taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + b = (a + b) + c).symm
            (middleThreeWiring a b c (Fin.natAdd (a + b) index)) =
          Fin.castAdd b (Fin.natAdd a index) := by
      apply Fin.ext
      simp [middleThreeWiring, threeDecompose, threeCompose]
    rw [route]
    simp

private def firstRoute (firstAncilla secondAncilla width : Nat) :
    Circuit ((firstAncilla + secondAncilla) + width) :=
  .permute (middleThreeWiring firstAncilla secondAncilla width)

private theorem firstRoute_spec {firstAncilla secondAncilla width : Nat}
    (firstInit : BitState firstAncilla)
    (secondInit : BitState secondAncilla) (state : BitState width) :
    Circuit.eval (firstRoute firstAncilla secondAncilla width)
        (BitState.append (BitState.append firstInit secondInit) state) =
      Realization.castState
        (by ac_rfl :
          (firstAncilla + width) + secondAncilla =
            (firstAncilla + secondAncilla) + width)
        (BitState.append (BitState.append firstInit state) secondInit) := by
  exact middleThreeWiring_on_append firstInit secondInit state

private def firstLayer {width : Nat} {firstGate : Reversible width}
    (first : CleanFredkinRealization firstGate) (secondAncilla : Nat) :
    Circuit ((first.ancillaWidth + secondAncilla) + width) :=
  Simulation.castCircuit
    (by ac_rfl :
      (first.ancillaWidth + width) + secondAncilla =
        (first.ancillaWidth + secondAncilla) + width)
    (.tensor first.circuit (.identity secondAncilla))

private theorem firstLayer_spec {width secondAncilla : Nat}
    {firstGate : Reversible width}
    (first : CleanFredkinRealization firstGate)
    (secondInit : BitState secondAncilla) (state : BitState width) :
    Circuit.eval (firstLayer first secondAncilla)
        (Circuit.eval
          (firstRoute first.ancillaWidth secondAncilla width)
          (BitState.append (BitState.append first.ancillaInit secondInit)
            state)) =
      Circuit.eval
        (firstRoute first.ancillaWidth secondAncilla width)
        (BitState.append (BitState.append first.ancillaInit secondInit)
          (firstGate state)) := by
  rw [firstRoute_spec]
  rw [firstLayer, Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    first.realizes, Circuit.eval_identity]
  exact firstRoute_spec first.ancillaInit secondInit (firstGate state) |>.symm

private def secondLayer {width : Nat} {secondGate : Reversible width}
    (firstAncilla : Nat) (second : CleanFredkinRealization secondGate) :
    Circuit ((firstAncilla + second.ancillaWidth) + width) :=
  Simulation.castCircuit
    (by ac_rfl :
      firstAncilla + (second.ancillaWidth + width) =
        (firstAncilla + second.ancillaWidth) + width)
    (.tensor (.identity firstAncilla) second.circuit)

private theorem secondLayer_spec {width firstAncilla : Nat}
    {secondGate : Reversible width}
    (firstInit : BitState firstAncilla)
    (second : CleanFredkinRealization secondGate) (state : BitState width) :
    Circuit.eval (secondLayer firstAncilla second)
        (BitState.append (BitState.append firstInit second.ancillaInit) state) =
      BitState.append (BitState.append firstInit second.ancillaInit)
        (secondGate state) := by
  unfold secondLayer
  rw [← castState_append_assoc_symm firstInit second.ancillaInit state]
  rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    Circuit.eval_identity, second.realizes]
  exact castState_append_assoc_symm firstInit second.ancillaInit
    (secondGate state)

/--
Serially compose two clean realizations.  Their independently initialized
ancillary blocks are both retained, and structural routing brings the data
next to the first block only while its circuit runs.
-/
def comp {width : Nat} {firstGate secondGate : Reversible width}
    (first : CleanFredkinRealization firstGate)
    (second : CleanFredkinRealization secondGate) :
    CleanFredkinRealization (firstGate.trans secondGate) where
  ancillaWidth := first.ancillaWidth + second.ancillaWidth
  ancillaInit := BitState.append first.ancillaInit second.ancillaInit
  circuit := .seq
    (firstRoute first.ancillaWidth second.ancillaWidth width)
    (.seq (firstLayer first second.ancillaWidth)
      (.seq
        (Circuit.inverse
          (firstRoute first.ancillaWidth second.ancillaWidth width))
        (secondLayer first.ancillaWidth second)))
  structural := by
    simp [firstRoute, firstLayer, secondLayer,
      first.structural, second.structural]
  latencyZero := by
    have routeTimed : Circuit.HasLatency
        (firstRoute first.ancillaWidth second.ancillaWidth width) 0 :=
      Circuit.hasLatency_permute _
    have firstTimed : Circuit.HasLatency
        (firstLayer first second.ancillaWidth) 0 := by
      apply hasLatency_castCircuit
      exact Circuit.HasLatency.tensor first.latencyZero
        (Circuit.hasLatency_identity _)
    have secondTimed : Circuit.HasLatency
        (secondLayer first.ancillaWidth second) 0 := by
      apply hasLatency_castCircuit
      exact Circuit.HasLatency.tensor (Circuit.hasLatency_identity _)
        second.latencyZero
    have inverseRouteTimed : Circuit.HasLatency
        (Circuit.inverse
          (firstRoute first.ancillaWidth second.ancillaWidth width)) 0 :=
      Circuit.HasLatency.inverse routeTimed
    intro input output actual path
    exact (hasLatency_seq_zero routeTimed
      (hasLatency_seq_zero firstTimed
        (hasLatency_seq_zero inverseRouteTimed secondTimed))) path
  realizes state := by
    simp only [Circuit.eval_seq]
    rw [firstLayer_spec]
    rw [Circuit.eval_inverse_eval]
    rw [secondLayer_spec]
    rfl

end CleanFredkinRealization

/--
Clean Fredkin realizability is a subgroup of the full finite state-permutation
group.  Composition concatenates independently returned ancillary blocks.
-/
def cleanFredkinSubgroup (width : Nat) :
    Subgroup (Equiv.Perm (BitState width)) where
  carrier := CleanFredkinRealizable
  one_mem' := ⟨CleanFredkinRealization.identity width⟩
  mul_mem' := by
    intro first second firstClean secondClean
    rcases firstClean with ⟨firstRealization⟩
    rcases secondClean with ⟨secondRealization⟩
    refine ⟨?_⟩
    simpa only [Equiv.Perm.mul_def] using
      CleanFredkinRealization.comp secondRealization firstRealization
  inv_mem' := by
    intro gate clean
    rcases clean with ⟨realization⟩
    exact ⟨CleanFredkinRealization.inverse realization⟩

end ConservativeLogic
