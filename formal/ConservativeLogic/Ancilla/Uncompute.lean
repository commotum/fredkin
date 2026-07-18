import ConservativeLogic.Circuit.Inverse
import ConservativeLogic.Simulation.Fredkin

/-!
# Explicit spy registers and compute-copy-uncompute

This module implements the finite static construction from Section 7.1 of
Fredkin and Toffoli.  A result register has two separately named halves,
initialized as `(0ⁿ,1ⁿ)`.  Each result bit controls one real paper Fredkin
gate whose canonical inputs `(a,0,1)` are explicitly routed to the paper's
physical port order `(a,1,0)`.  The complete copy layer consequently maps
`(x,0ⁿ,1ⁿ)` to `(x,x,¬x)` without an unrestricted copy primitive.

Given a full `Realization.Realizes` witness, the final circuit runs the
realization, copies its complete result block, and runs the structural inverse.
Its exact initialized-slice equation restores scratch, source, and argument and
removes the transient garbage.  All declarations here are static finite-state
facts.  They do not provide arbitrary-function synthesis, delay padding,
feedback, physical routing, or a positive-latency time-reversal theorem.
-/

namespace ConservativeLogic.Ancilla

open Realization

/-! ## Explicit result-register states -/

/-- The width-`n` all-zero register. -/
def zeroRegister (n : Nat) : BitState n := fun _ => false

/-- The width-`n` all-one register. -/
def oneRegister (n : Nat) : BitState n := fun _ => true

/-- Pointwise Boolean complement of a fixed-width register. -/
def bitwiseNot {n : Nat} (state : BitState n) : BitState n :=
  fun index => !state index

/-- The prescribed ordered result-register initialization `(0ⁿ,1ⁿ)`. -/
def resultRegisterInput (n : Nat) : BitState (n + n) :=
  BitState.append (zeroRegister n) (oneRegister n)

/-- The ordered result-register output `(value,¬value)`. -/
def resultRegisterOutput {n : Nat} (value : BitState n) : BitState (n + n) :=
  BitState.append value (bitwiseNot value)

@[simp]
theorem hammingWeight_zeroRegister (n : Nat) :
    hammingWeight (zeroRegister n) = 0 := by
  simp [hammingWeight, zeroRegister]

@[simp]
theorem hammingWeight_oneRegister (n : Nat) :
    hammingWeight (oneRegister n) = n := by
  simp [hammingWeight, oneRegister]

@[simp]
theorem hammingWeight_resultRegisterInput (n : Nat) :
    hammingWeight (resultRegisterInput n) = n := by
  simp [resultRegisterInput]

/-! ## One physical paper-Fredkin spy -/

/--
Actively route canonical `(a,0,1)` to the paper gate's physical `(a,1,0)`.
The through/control port remains first and only the two data ports are swapped.
-/
def copyPairInputWiring : WirePerm 3 := PaperFredkin.dataSwap

/-- One real paper Fredkin spy with its canonical-to-physical input routing. -/
def copyPair : Circuit 3 :=
  .seq (.permute copyPairInputWiring) .fredkin

/-- Exact physical-port equation `(a,1,0) ↦ (a,a,¬a)`. -/
@[simp]
theorem copyPair_physical_spec (value : Bool) :
    Circuit.eval Circuit.fredkin (PaperFredkin.state value true false) =
      PaperFredkin.state value value (!value) := by
  cases value <;> decide

/-- Exact canonical equation `(a,0,1) ↦ (a,a,¬a)` for `copyPair`. -/
@[simp]
theorem copyPair_spec (value : Bool) :
    Circuit.eval copyPair (PaperFredkin.state value false true) =
      PaperFredkin.state value value (!value) := by
  cases value <;> decide

/-! ## Grouped registers and an interleaved bank of disjoint spies -/

/-- Width of the complete `(through,zero/first,one/second)` copy-layer state. -/
abbrev copyRegisterWidth (n : Nat) : Nat := n + (n + n)

private def groupedCoordinates (n : Nat) :
    Fin (copyRegisterWidth n) ≃ Fin 3 × Fin n :=
  (finCongr (by
    change n + (n + n) = 3 * n
    omega)).trans
    finProdFinEquiv.symm

private def interleavedCoordinates (n : Nat) :
    Fin (copyRegisterWidth n) ≃ Fin n × Fin 3 :=
  (finCongr (by
    change n + (n + n) = n * 3
    omega)).trans
    finProdFinEquiv.symm

/--
Actively route three width-`n` grouped blocks to `n` adjacent ordered triples.
This is a bijective structural reindexing, not a value-dependent operation.
-/
def copyRegisterInputWiring (n : Nat) : WirePerm (copyRegisterWidth n) :=
  (groupedCoordinates n).trans <|
    (Equiv.prodComm (Fin 3) (Fin n)).trans (interleavedCoordinates n).symm

/-- Regroup adjacent ordered triples into three width-`n` output blocks. -/
def copyRegisterOutputWiring (n : Nat) : WirePerm (copyRegisterWidth n) :=
  (copyRegisterInputWiring n).symm

/-- Interleave three grouped width-`n` states using the exact public wiring. -/
private def interleaveThree {n : Nat}
    (first second third : BitState n) : BitState (copyRegisterWidth n) :=
  WirePerm.onState (copyRegisterInputWiring n)
    (BitState.append first (BitState.append second third))

private theorem interleaveThree_apply {n : Nat}
    (first second third : BitState n) (index : Fin n) (port : Fin 3) :
    interleaveThree first second third
        ((interleavedCoordinates n).symm (index, port)) =
      PaperFredkin.state (first index) (second index) (third index) port := by
  unfold interleaveThree
  rw [WirePerm.onState_apply]
  simp [copyRegisterInputWiring, groupedCoordinates,
    interleavedCoordinates]
  refine Fin.cases ?_ ?_ port
  · rw [show
        Fin.cast _ (finProdFinEquiv ((0 : Fin 3), index)) =
          Fin.castAdd (n + n) index by
        apply Fin.ext
        simp [finProdFinEquiv]]
    simp
  · intro tail
    refine Fin.cases ?_ ?_ tail
    · rw [show
          Fin.cast _
              (finProdFinEquiv ((Fin.succ 0 : Fin 3), index)) =
            Fin.natAdd n (Fin.castAdd n index) by
          apply Fin.ext
          simp [finProdFinEquiv]
          omega]
      simp
    · intro last
      refine Fin.cases ?_ ?_ last
      · rw [show
            Fin.cast _
                (finProdFinEquiv
                  ((Fin.succ (Fin.succ 0) : Fin 3), index)) =
              Fin.natAdd n (Fin.natAdd n index) by
            apply Fin.ext
            simp [finProdFinEquiv]
            omega]
        rw [BitState.append_natAdd, BitState.append_natAdd]
        rfl
      · intro impossible
        exact Fin.elim0 impossible

private theorem copyRegisterWidth_succ (n : Nat) :
    3 + copyRegisterWidth n = copyRegisterWidth (n + 1) := by
  change 3 + (n + (n + n)) = (n + 1) + ((n + 1) + (n + 1))
  omega

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

@[simp]
private theorem castState_trans {left middle right : Nat}
    (first : left = middle) (second : middle = right)
    (state : BitState left) :
    castState second (castState first state) =
      castState (first.trans second) state := by
  cases first
  cases second
  rfl

private theorem castState_proof_irrel {left right : Nat}
    (first second : left = right) (state : BitState left) :
    castState first state = castState second state := by
  have equality : first = second := Subsingleton.elim _ _
  cases equality
  rfl

private theorem castState_append_left {a b c : Nat} (width : a = b)
    (left : BitState a) (right : BitState c) :
    castState (congrArg (fun n => n + c) width)
        (BitState.append left right) =
      BitState.append (castState width left) right := by
  cases width
  rfl

private theorem castState_append_right {a b c : Nat} (width : b = c)
    (left : BitState a) (right : BitState b) :
    castState (congrArg (fun n => a + n) width)
        (BitState.append left right) =
      BitState.append left (castState width right) := by
  cases width
  rfl

private theorem castState_append_both {a b c d : Nat}
    (leftWidth : a = b) (rightWidth : c = d)
    (left : BitState a) (right : BitState c) :
    castState (congrArg₂ Nat.add leftWidth rightWidth)
        (BitState.append left right) =
      BitState.append (castState leftWidth left)
        (castState rightWidth right) := by
  cases leftWidth
  cases rightWidth
  rfl

private theorem append_noBits_right {width : Nat} (state : BitState width) :
    BitState.append state Realization.Primitive.noBits =
      castState (Nat.add_zero width).symm state := by
  funext index
  refine Fin.addCases ?_ (fun impossible => Fin.elim0 impossible) index
  intro inner
  rw [BitState.append_castAdd, castState_apply]
  congr 1

private theorem castState_append_noBits_right {width : Nat}
    (state : BitState width) :
    castState (Nat.add_zero width)
        (BitState.append state Realization.Primitive.noBits) = state := by
  rw [append_noBits_right, castState_trans]
  rfl

private theorem castState_append_assoc {a b c : Nat}
    (first : BitState a) (second : BitState b) (third : BitState c) :
    castState (Nat.add_assoc a b c)
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

private theorem castState_append_assoc_symm {a b c : Nat}
    (first : BitState a) (second : BitState b) (third : BitState c) :
    castState (Nat.add_assoc a b c).symm
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

private def stateTail {n : Nat} (state : BitState (n + 1)) : BitState n :=
  fun index => state index.succ

private theorem interleaveThree_succ {n : Nat}
    (first second third : BitState (n + 1)) :
    interleaveThree first second third =
      castState (copyRegisterWidth_succ n)
        (BitState.append
          (PaperFredkin.state (first 0) (second 0) (third 0))
          (interleaveThree (stateTail first) (stateTail second)
            (stateTail third))) := by
  funext output
  obtain ⟨coordinate, rfl⟩ :=
    (interleavedCoordinates (n + 1)).symm.surjective output
  rcases coordinate with ⟨index, port⟩
  rw [interleaveThree_apply]
  refine Fin.cases ?_ ?_ index
  · rw [castState_apply]
    rw [show
      Fin.cast (copyRegisterWidth_succ n).symm
          ((interleavedCoordinates (n + 1)).symm (0, port)) =
        Fin.castAdd (copyRegisterWidth n) port by
      apply Fin.ext
      simp [interleavedCoordinates, finProdFinEquiv]]
    simp
  · intro tail
    rw [castState_apply]
    rw [show
      Fin.cast (copyRegisterWidth_succ n).symm
          ((interleavedCoordinates (n + 1)).symm (tail.succ, port)) =
        Fin.natAdd 3 ((interleavedCoordinates n).symm (tail, port)) by
      apply Fin.ext
      simp [interleavedCoordinates, finProdFinEquiv]
      omega]
    rw [BitState.append_natAdd, interleaveThree_apply]
    rfl

/-- An interleaved tensor bank containing exactly one canonical spy per bit. -/
private def copyPairBank : (n : Nat) → Circuit (copyRegisterWidth n)
  | 0 => .identity 0
  | n + 1 =>
      Simulation.castCircuit (copyRegisterWidth_succ n)
        (.tensor copyPair (copyPairBank n))

private theorem copyPairBank_spec {n : Nat} (value : BitState n) :
    Circuit.eval (copyPairBank n)
        (interleaveThree value (zeroRegister n) (oneRegister n)) =
      interleaveThree value value (bitwiseNot value) := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n inductionHypothesis =>
      rw [interleaveThree_succ]
      simp only [copyPairBank]
      rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append]
      change castState _
        (BitState.append
          (Circuit.eval copyPair (PaperFredkin.state (value 0) false true))
          (Circuit.eval (copyPairBank n)
            (interleaveThree (stateTail value) (zeroRegister n)
              (oneRegister n)))) = _
      rw [copyPair_spec]
      rw [inductionHypothesis (value := stateTail value)]
      change castState _
        (BitState.append
          (PaperFredkin.state (value 0) (value 0) ((bitwiseNot value) 0))
          (interleaveThree (stateTail value) (stateTail value)
            (stateTail (bitwiseNot value)))) =
        interleaveThree value value (bitwiseNot value)
      exact (interleaveThree_succ value value (bitwiseNot value)).symm

/--
The all-width copy layer.  Its external order is grouped
`(through,0ⁿ,1ⁿ)` / `(through,copy,complement)`; its body is an explicitly
interleaved disjoint tensor bank.
-/
def copyRegisterCircuit (n : Nat) : Circuit (copyRegisterWidth n) :=
  .seq (.permute (copyRegisterInputWiring n))
    (.seq (copyPairBank n) (.permute (copyRegisterOutputWiring n)))

/--
Complete all-width initialized-slice equation.  The through register is
retained, while the explicit `(0ⁿ,1ⁿ)` target becomes `(value,¬value)`.
-/
@[simp]
theorem copyRegister_spec {n : Nat} (value : BitState n) :
    Circuit.eval (copyRegisterCircuit n)
        (BitState.append value (resultRegisterInput n)) =
      BitState.append value (resultRegisterOutput value) := by
  change WirePerm.onState (copyRegisterOutputWiring n)
      (Circuit.eval (copyPairBank n)
        (interleaveThree value (zeroRegister n) (oneRegister n))) = _
  rw [copyPairBank_spec]
  change WirePerm.onState (copyRegisterInputWiring n).symm
      (WirePerm.onState (copyRegisterInputWiring n)
        (BitState.append value
          (BitState.append value (bitwiseNot value)))) = _
  exact (WirePerm.onState (copyRegisterInputWiring n)).symm_apply_apply _

/-- A register and its pointwise complement contain exactly `n` true bits. -/
theorem hammingWeight_add_bitwiseNot {n : Nat} (state : BitState n) :
    hammingWeight state + hammingWeight (bitwiseNot state) = n := by
  unfold hammingWeight bitwiseNot
  simpa using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun index : Fin n => state index = true))

/-- Every ordered output pair `(value,¬value)` has exactly `n` true bits. -/
@[simp]
theorem hammingWeight_resultRegisterOutput {n : Nat} (value : BitState n) :
    hammingWeight (resultRegisterOutput value) = n := by
  rw [resultRegisterOutput, hammingWeight_append,
    hammingWeight_add_bitwiseNot]

/-! ## Copying the selected result block of a complete realization output -/

private abbrev copyResultCoreWidth (scratchWidth resultWidth garbageWidth : Nat) :
    Nat :=
  ((scratchWidth + resultWidth) + garbageWidth) +
    ((resultWidth + resultWidth) + 0)

private theorem copyResultRouteOutputWidth
    (scratchWidth resultWidth garbageWidth : Nat) :
    ((scratchWidth + resultWidth) + (resultWidth + resultWidth)) +
        (garbageWidth + 0) =
      copyResultCoreWidth scratchWidth resultWidth garbageWidth := by
  simp only [copyResultCoreWidth]
  omega

private def copyResultRouteWiring
    (scratchWidth resultWidth garbageWidth : Nat) :
    WirePerm (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  Simulation.middleSwapWiring
    (scratchWidth + resultWidth) garbageWidth
    (resultWidth + resultWidth) 0

private def copyResultRoute
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  .permute (copyResultRouteWiring scratchWidth resultWidth garbageWidth)

private def copyResultBody
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  Simulation.castCircuit
    (copyResultRouteOutputWidth scratchWidth resultWidth garbageWidth)
    (.tensor
      (Simulation.castCircuit
        (Nat.add_assoc scratchWidth resultWidth
          (resultWidth + resultWidth)).symm
        (.tensor (.identity scratchWidth)
          (copyRegisterCircuit resultWidth)))
      (.identity (garbageWidth + 0)))

private def copyResultCore
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  .seq (copyResultRoute scratchWidth resultWidth garbageWidth)
    (.seq (copyResultBody scratchWidth resultWidth garbageWidth)
      (Circuit.inverse
        (copyResultRoute scratchWidth resultWidth garbageWidth)))

private def copyResultCoreState
    {scratchWidth resultWidth garbageWidth : Nat}
    (scratch : BitState scratchWidth) (result : BitState resultWidth)
    (garbage : BitState garbageWidth)
    (register : BitState (resultWidth + resultWidth)) :
    BitState (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  BitState.append
    (BitState.append (BitState.append scratch result) garbage)
    (BitState.append register Realization.Primitive.noBits)

private def copyResultRoutedState
    {scratchWidth resultWidth garbageWidth : Nat}
    (scratch : BitState scratchWidth) (result : BitState resultWidth)
    (garbage : BitState garbageWidth)
    (register : BitState (resultWidth + resultWidth)) :
    BitState (copyResultCoreWidth scratchWidth resultWidth garbageWidth) :=
  castState
    (copyResultRouteOutputWidth scratchWidth resultWidth garbageWidth)
    (BitState.append
      (BitState.append (BitState.append scratch result) register)
      (BitState.append garbage Realization.Primitive.noBits))

private theorem copyResultRoute_spec
    {scratchWidth resultWidth garbageWidth : Nat}
    (scratch : BitState scratchWidth) (result : BitState resultWidth)
    (garbage : BitState garbageWidth)
    (register : BitState (resultWidth + resultWidth)) :
    Circuit.eval (copyResultRoute scratchWidth resultWidth garbageWidth)
        (copyResultCoreState scratch result garbage register) =
      copyResultRoutedState scratch result garbage register := by
  simpa [copyResultRoute, copyResultRouteWiring, copyResultCoreState,
    copyResultRoutedState] using
    (Simulation.middleSwapWiring_on_append
      (BitState.append scratch result) garbage register
      Realization.Primitive.noBits)

private theorem copyResultBody_spec
    {scratchWidth resultWidth garbageWidth : Nat}
    (scratch : BitState scratchWidth) (result : BitState resultWidth)
    (garbage : BitState garbageWidth) :
    Circuit.eval (copyResultBody scratchWidth resultWidth garbageWidth)
        (copyResultRoutedState scratch result garbage
          (resultRegisterInput resultWidth)) =
      copyResultRoutedState scratch result garbage
        (resultRegisterOutput result) := by
  unfold copyResultRoutedState copyResultBody
  rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    Circuit.eval_identity]
  rw [← castState_append_assoc_symm scratch result
    (resultRegisterInput resultWidth)]
  rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append,
    Circuit.eval_identity, copyRegister_spec]
  apply congrArg (castState
    (copyResultRouteOutputWidth scratchWidth resultWidth garbageWidth))
  apply congrArg (fun state =>
    BitState.append state
      (BitState.append garbage Realization.Primitive.noBits))
  exact castState_append_assoc_symm scratch result
    (resultRegisterOutput result)

private theorem copyResultCore_spec
    {scratchWidth resultWidth garbageWidth : Nat}
    (scratch : BitState scratchWidth) (result : BitState resultWidth)
    (garbage : BitState garbageWidth) :
    Circuit.eval (copyResultCore scratchWidth resultWidth garbageWidth)
        (copyResultCoreState scratch result garbage
          (resultRegisterInput resultWidth)) =
      copyResultCoreState scratch result garbage
        (resultRegisterOutput result) := by
  simp only [copyResultCore, Circuit.eval_seq]
  rw [copyResultRoute_spec, copyResultBody_spec]
  rw [← copyResultRoute_spec scratch result garbage
    (resultRegisterOutput result)]
  exact Circuit.eval_inverse_eval
    (copyResultRoute scratchWidth resultWidth garbageWidth) _

/-- Total width of a computation register plus its explicit `2n` result register. -/
abbrev computeCopyUncomputeWidth (layout : Layout) : Nat :=
  layout.width + (layout.resultWidth + layout.resultWidth)

private theorem layoutOutputWidth (layout : Layout) :
    layout.scratchWidth +
        (layout.resultWidth + layout.garbageWidth) = layout.width :=
  (congrArg (fun width => layout.scratchWidth + width)
    layout.balanced).symm

private theorem copyResultCoreNormalizedWidth (layout : Layout) :
    copyResultCoreWidth layout.scratchWidth layout.resultWidth
        layout.garbageWidth =
      (layout.scratchWidth +
          (layout.resultWidth + layout.garbageWidth)) +
        (layout.resultWidth + layout.resultWidth) := by
  simp only [copyResultCoreWidth]
  omega

private theorem copyResultCoreToLayoutWidth (layout : Layout) :
    copyResultCoreWidth layout.scratchWidth layout.resultWidth
        layout.garbageWidth = computeCopyUncomputeWidth layout :=
  (copyResultCoreNormalizedWidth layout).trans
    (congrArg
      (fun width => width + (layout.resultWidth + layout.resultWidth))
      (layoutOutputWidth layout))

private theorem copyResultCoreState_to_layout
    (layout : Layout) (scratch : BitState layout.scratchWidth)
    (result : BitState layout.resultWidth)
    (garbage : BitState layout.garbageWidth)
    (register : BitState (layout.resultWidth + layout.resultWidth)) :
    castState (copyResultCoreToLayoutWidth layout)
        (copyResultCoreState scratch result garbage register) =
      BitState.append (layout.packOutput scratch result garbage) register := by
  let mainAssoc := Nat.add_assoc layout.scratchWidth layout.resultWidth
    layout.garbageWidth
  let registerZero := Nat.add_zero (layout.resultWidth + layout.resultWidth)
  let normalize := congrArg₂ Nat.add mainAssoc registerZero
  let liftOutput := congrArg
    (fun width => width + (layout.resultWidth + layout.resultWidth))
    (layoutOutputWidth layout)
  calc
    castState (copyResultCoreToLayoutWidth layout)
        (copyResultCoreState scratch result garbage register) =
      castState liftOutput
        (castState normalize
          (copyResultCoreState scratch result garbage register)) := by
        rw [castState_trans]
    _ = castState liftOutput
        (BitState.append
          (castState mainAssoc
            (BitState.append (BitState.append scratch result) garbage))
          (castState registerZero
            (BitState.append register Realization.Primitive.noBits))) := by
        apply congrArg (castState liftOutput)
        exact castState_append_both mainAssoc registerZero _ _
    _ = castState liftOutput
        (BitState.append
          (BitState.append scratch (BitState.append result garbage))
          register) := by
        rw [castState_append_assoc, castState_append_noBits_right]
    _ = BitState.append
        (castState (layoutOutputWidth layout)
          (BitState.append scratch (BitState.append result garbage)))
        register := castState_append_left _ _ _
    _ = BitState.append (layout.packOutput scratch result garbage) register := by
        unfold Layout.packOutput
        apply congrArg (fun state => BitState.append state register)
        exact castState_proof_irrel _ _ _

/--
Copy only the selected result block of a complete packed realization output.
Scratch, the through result, and every transient garbage wire remain available
for the subsequent inverse.
-/
def copyResultCircuit (layout : Layout) :
    Circuit (computeCopyUncomputeWidth layout) :=
  Simulation.castCircuit (copyResultCoreToLayoutWidth layout)
    (copyResultCore layout.scratchWidth layout.resultWidth
      layout.garbageWidth)

/-- Exact embedded copy equation on an arbitrary complete packed midpoint. -/
@[simp]
theorem copyResult_spec (layout : Layout)
    (scratch : BitState layout.scratchWidth)
    (result : BitState layout.resultWidth)
    (garbage : BitState layout.garbageWidth) :
    Circuit.eval (copyResultCircuit layout)
        (BitState.append (layout.packOutput scratch result garbage)
          (resultRegisterInput layout.resultWidth)) =
      BitState.append (layout.packOutput scratch result garbage)
        (resultRegisterOutput result) := by
  rw [← copyResultCoreState_to_layout layout scratch result garbage
    (resultRegisterInput layout.resultWidth)]
  rw [copyResultCircuit, Simulation.eval_castCircuit, copyResultCore_spec]
  exact copyResultCoreState_to_layout layout scratch result garbage
    (resultRegisterOutput result)

/-! ## Complete compute-copy-uncompute -/

/--
Run a balanced computation on the main register, copy its selected result into
the explicit initialized `2n` register, and run the structural inverse on the
complete main register.
-/
def computeCopyUncompute (layout : Layout)
    (circuit : Circuit layout.width) :
    Circuit (computeCopyUncomputeWidth layout) :=
  .seq
    (.tensor circuit
      (.identity (layout.resultWidth + layout.resultWidth)))
    (.seq (copyResultCircuit layout)
      (.tensor (Circuit.inverse circuit)
        (.identity (layout.resultWidth + layout.resultWidth))))

/--
Complete initialized-slice equation.  The exact original packed
`(scratch,source,argument)` register is restored, the transient garbage is
absent, and the separate initialized register contains `(target,¬target)`.
-/
theorem compute_copy_uncompute_spec
    {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth}
    {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (argument : BitState layout.argumentWidth) :
    Circuit.eval (computeCopyUncompute layout circuit)
        (BitState.append (layout.packInput scratch source argument)
          (resultRegisterInput layout.resultWidth)) =
      BitState.append (layout.packInput scratch source argument)
        (resultRegisterOutput (target argument)) := by
  simp only [computeCopyUncompute, Circuit.eval_seq,
    Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [realizes argument, copyResult_spec]
  rw [Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [← realizes argument, Circuit.eval_inverse_eval]

/-- The complete construction is globally reversible on all boundary states. -/
theorem compute_copy_uncompute_isReversible (layout : Layout)
    (circuit : Circuit layout.width) :
    IsReversible (Circuit.eval (computeCopyUncompute layout circuit)) :=
  Circuit.eval_isReversible _

/-- The complete construction globally preserves total Hamming weight. -/
theorem compute_copy_uncompute_conservative (layout : Layout)
    (circuit : Circuit layout.width) :
    WeightPreserving (Circuit.eval (computeCopyUncompute layout circuit)) :=
  Circuit.eval_weightPreserving _

/-! ## Exact structural resources -/

private theorem fredkinCount_inverse {width : Nat} (circuit : Circuit width) :
    Circuit.fredkinCount (Circuit.inverse circuit) =
      Circuit.fredkinCount circuit := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => rfl
  | permute wiring => rfl
  | seq first second firstIH secondIH =>
      simp only [Circuit.inverse_seq, Circuit.fredkinCount,
        firstIH, secondIH]
      omega
  | tensor left right leftIH rightIH =>
      simp only [Circuit.inverse_tensor, Circuit.fredkinCount,
        leftIH, rightIH]

@[simp]
theorem copyPair_fredkinCount : Circuit.fredkinCount copyPair = 1 := by
  rfl

private theorem copyPairBank_fredkinCount (n : Nat) :
    Circuit.fredkinCount (copyPairBank n) = n := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp only [copyPairBank, Circuit.fredkinCount_castCircuit,
        Circuit.fredkinCount, copyPair_fredkinCount, inductionHypothesis]
      omega

/-- The all-width copy layer contains exactly one Fredkin constructor per bit. -/
@[simp]
theorem copyRegisterCircuit_fredkinCount (n : Nat) :
    Circuit.fredkinCount (copyRegisterCircuit n) = n := by
  simp [copyRegisterCircuit, Circuit.fredkinCount,
    copyPairBank_fredkinCount]

private theorem copyResultRoute_fredkinCount
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.fredkinCount
        (copyResultRoute scratchWidth resultWidth garbageWidth) = 0 := by
  rfl

private theorem copyResultBody_fredkinCount
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.fredkinCount
        (copyResultBody scratchWidth resultWidth garbageWidth) = resultWidth := by
  simp [copyResultBody, Circuit.fredkinCount,
    copyRegisterCircuit_fredkinCount]

private theorem copyResultCore_fredkinCount
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.fredkinCount
        (copyResultCore scratchWidth resultWidth garbageWidth) = resultWidth := by
  simp [copyResultCore, Circuit.fredkinCount,
    copyResultRoute_fredkinCount, copyResultBody_fredkinCount,
    fredkinCount_inverse]

/-- Embedded result copying adds exactly one Fredkin per selected result bit. -/
@[simp]
theorem copyResultCircuit_fredkinCount (layout : Layout) :
    Circuit.fredkinCount (copyResultCircuit layout) = layout.resultWidth := by
  simp [copyResultCircuit, copyResultCore_fredkinCount]

/--
Exact syntax count: the computation occurs once forward and once inversely,
with one additional spy Fredkin for each selected result bit.  This is not an
optimality, depth, or physical-routing theorem.
-/
theorem computeCopyUncompute_fredkinCount (layout : Layout)
    (circuit : Circuit layout.width) :
    Circuit.fredkinCount (computeCopyUncompute layout circuit) =
      Circuit.fredkinCount circuit +
        (layout.resultWidth + Circuit.fredkinCount circuit) := by
  simp [computeCopyUncompute, Circuit.fredkinCount,
    copyResultCircuit_fredkinCount, fredkinCount_inverse]

/-! ## Accurately scoped zero-latency certificates -/

private theorem hasLatency_castCircuit {leftWidth rightWidth latency : Nat}
    (width : leftWidth = rightWidth) {circuit : Circuit leftWidth}
    (timed : Circuit.HasLatency circuit latency) :
    Circuit.HasLatency (Simulation.castCircuit width circuit) latency := by
  cases width
  exact timed

private theorem hasLatency_seq_zero {width : Nat}
    {first second : Circuit width}
    (firstTimed : Circuit.HasLatency first 0)
    (secondTimed : Circuit.HasLatency second 0) :
    Circuit.HasLatency (.seq first second) 0 := by
  intro input output actual path
  have equality := Circuit.HasLatency.seq firstTimed secondTimed path
  simpa using equality

private theorem hasLatency_tensor_zero {leftWidth rightWidth : Nat}
    {left : Circuit leftWidth} {right : Circuit rightWidth}
    (leftTimed : Circuit.HasLatency left 0)
    (rightTimed : Circuit.HasLatency right 0) :
    Circuit.HasLatency (.tensor left right) 0 := by
  intro input output actual path
  exact Circuit.HasLatency.tensor leftTimed rightTimed path

private theorem copyPair_hasLatency_zero :
    Circuit.HasLatency copyPair 0 := by
  apply hasLatency_seq_zero
  · exact Circuit.hasLatency_permute copyPairInputWiring
  · exact Circuit.hasLatency_fredkin

private theorem copyPairBank_hasLatency_zero (n : Nat) :
    Circuit.HasLatency (copyPairBank n) 0 := by
  induction n with
  | zero => exact Circuit.hasLatency_identity 0
  | succ n inductionHypothesis =>
      apply hasLatency_castCircuit (copyRegisterWidth_succ n)
      exact hasLatency_tensor_zero copyPair_hasLatency_zero
        inductionHypothesis

/-- Every path through the explicit all-width copy layer has delay zero. -/
theorem copyRegisterCircuit_hasLatency_zero (n : Nat) :
    Circuit.HasLatency (copyRegisterCircuit n) 0 := by
  unfold copyRegisterCircuit
  apply hasLatency_seq_zero
  · exact Circuit.hasLatency_permute (copyRegisterInputWiring n)
  · apply hasLatency_seq_zero
    · exact copyPairBank_hasLatency_zero n
    · exact Circuit.hasLatency_permute (copyRegisterOutputWiring n)

private theorem copyResultRoute_hasLatency_zero
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.HasLatency
      (copyResultRoute scratchWidth resultWidth garbageWidth) 0 :=
  Circuit.hasLatency_permute _

private theorem copyResultBody_hasLatency_zero
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.HasLatency
      (copyResultBody scratchWidth resultWidth garbageWidth) 0 := by
  unfold copyResultBody
  apply hasLatency_castCircuit
    (copyResultRouteOutputWidth scratchWidth resultWidth garbageWidth)
  have left : Circuit.HasLatency
      (Circuit.tensor (Circuit.identity scratchWidth)
        (copyRegisterCircuit resultWidth)) 0 :=
    hasLatency_tensor_zero (Circuit.hasLatency_identity scratchWidth)
      (copyRegisterCircuit_hasLatency_zero resultWidth)
  have leftCast : Circuit.HasLatency
      (Simulation.castCircuit
        (Nat.add_assoc scratchWidth resultWidth
          (resultWidth + resultWidth)).symm
        (Circuit.tensor (Circuit.identity scratchWidth)
          (copyRegisterCircuit resultWidth))) 0 :=
    hasLatency_castCircuit _ left
  have combined : Circuit.HasLatency
      (Circuit.tensor
        (Simulation.castCircuit
          (Nat.add_assoc scratchWidth resultWidth
            (resultWidth + resultWidth)).symm
          (Circuit.tensor (Circuit.identity scratchWidth)
            (copyRegisterCircuit resultWidth)))
        (Circuit.identity (garbageWidth + 0))) 0 :=
    hasLatency_tensor_zero leftCast
      (Circuit.hasLatency_identity (garbageWidth + 0))
  exact combined

private theorem copyResultCore_hasLatency_zero
    (scratchWidth resultWidth garbageWidth : Nat) :
    Circuit.HasLatency
      (copyResultCore scratchWidth resultWidth garbageWidth) 0 := by
  unfold copyResultCore
  apply hasLatency_seq_zero
  · exact copyResultRoute_hasLatency_zero _ _ _
  · apply hasLatency_seq_zero
    · exact copyResultBody_hasLatency_zero _ _ _
    · exact Circuit.HasLatency.inverse
        (copyResultRoute_hasLatency_zero _ _ _)

/-- The embedded result-copy circuit has uniform zero unit-wire latency. -/
theorem copyResultCircuit_hasLatency_zero (layout : Layout) :
    Circuit.HasLatency (copyResultCircuit layout) 0 := by
  apply hasLatency_castCircuit
  exact copyResultCore_hasLatency_zero _ _ _

/--
The unpadded complete construction has uniform zero latency when the supplied
computation itself does.  No positive-latency generalization is claimed: the
unchanged result-register tensor branches would require separate delay
padding.
-/
theorem computeCopyUncompute_hasLatency_zero (layout : Layout)
    {circuit : Circuit layout.width}
    (timed : Circuit.HasLatency circuit 0) :
    Circuit.HasLatency (computeCopyUncompute layout circuit) 0 := by
  unfold computeCopyUncompute
  apply hasLatency_seq_zero
  · exact hasLatency_tensor_zero timed
      (Circuit.hasLatency_identity
        (layout.resultWidth + layout.resultWidth))
  · apply hasLatency_seq_zero
    · exact copyResultCircuit_hasLatency_zero layout
    · exact hasLatency_tensor_zero timed.inverse
        (Circuit.hasLatency_identity
          (layout.resultWidth + layout.resultWidth))

end ConservativeLogic.Ancilla
