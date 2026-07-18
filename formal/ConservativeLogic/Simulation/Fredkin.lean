import ConservativeLogic.Simulation.Source
import ConservativeLogic.Realization.Primitive
import ConservativeLogic.Circuit.Timed

/-!
# Constructive Fredkin simulation of finite source circuits

Every source-language node is compiled to the fixed target `Circuit` grammar.
The construction exposes its complete initialized source and complete garbage
function.  Serial compilation retains earlier garbage untouched; tensor
compilation uses proved structural permutations to keep its two inputs
disjoint.  No scratch wire, arbitrary target equivalence, semantic gate,
implicit FAN-OUT, or discard is introduced.

The result is a static theorem for the explicitly generated feed-forward
source language.  Target `WirePerm` nodes remain an admitted zero-delay
structural reindexing resource, so this is Fredkin-plus-reindexing simulation,
not pure physical Fredkin synthesis or a sequential-network theorem.
-/

namespace ConservativeLogic.Simulation

open Realization
open Realization.Primitive

namespace SourceCircuit

/-- Fixed source width used by the selected recursive compilation. -/
def sourceWidth : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → Nat
  | _, _, .identity _ => 0
  | _, _, .permute _ => 0
  | _, outputWidth, .constant _ => outputWidth
  | _, _, .discard _ => 0
  | _, _, .andGate => 1
  | _, _, .orGate => 1
  | _, _, .notGate => 2
  | _, _, .fanout => 2
  | _, _, .seq first second => sourceWidth second + sourceWidth first
  | _, _, .tensor left right => sourceWidth left + sourceWidth right

/-- Complete garbage width used by the selected recursive compilation. -/
def garbageWidth : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → Nat
  | _, _, .identity _ => 0
  | _, _, .permute _ => 0
  | _, _, .constant _ => 0
  | _, _, .discard inputWidth => inputWidth
  | _, _, .andGate => 2
  | _, _, .orGate => 2
  | _, _, .notGate => 2
  | _, _, .fanout => 1
  | _, _, .seq first second => garbageWidth second + garbageWidth first
  | _, _, .tensor left right => garbageWidth left + garbageWidth right

/-- Exact boundary-width balance for every source term. -/
theorem source_garbage_balance {inputWidth outputWidth : Nat}
    (circuit : SourceCircuit inputWidth outputWidth) :
    sourceWidth circuit + inputWidth = outputWidth + garbageWidth circuit := by
  induction circuit with
  | identity width => simp [sourceWidth, garbageWidth]
  | permute wiring => simp [sourceWidth, garbageWidth]
  | constant value => simp [sourceWidth, garbageWidth]
  | discard width => simp [sourceWidth, garbageWidth]
  | andGate => rfl
  | orGate => rfl
  | notGate => rfl
  | fanout => rfl
  | seq first second firstIH secondIH =>
      simp only [sourceWidth, garbageWidth]
      calc
        (sourceWidth second + sourceWidth first) + _ =
            sourceWidth second + (sourceWidth first + _) := Nat.add_assoc ..
        _ = sourceWidth second + (_ + garbageWidth first) :=
          congrArg (sourceWidth second + ·) firstIH
        _ = (sourceWidth second + _) + garbageWidth first := (Nat.add_assoc ..).symm
        _ = (_ + garbageWidth second) + garbageWidth first :=
          congrArg (· + garbageWidth first) secondIH
        _ = _ + (garbageWidth second + garbageWidth first) := Nat.add_assoc ..
  | tensor left right leftIH rightIH =>
      simp only [sourceWidth, garbageWidth]
      calc
        (sourceWidth left + sourceWidth right) + (_ + _) =
            (sourceWidth left + _) + (sourceWidth right + _) := by ac_rfl
        _ = (_ + garbageWidth left) + (_ + garbageWidth right) :=
          congrArg₂ Nat.add leftIH rightIH
        _ = (_ + _) + (garbageWidth left + garbageWidth right) := by ac_rfl

/-- Complete fixed source state, independent of the circuit argument. -/
def sourceState : {inputWidth outputWidth : Nat} →
    (circuit : SourceCircuit inputWidth outputWidth) → BitState (sourceWidth circuit)
  | _, _, .identity _ => noBits
  | _, _, .permute _ => noBits
  | _, _, .constant value => value
  | _, _, .discard _ => noBits
  | _, _, .andGate => andSource
  | _, _, .orGate => orSource
  | _, _, .notGate => notFanoutSource
  | _, _, .fanout => notFanoutSource
  | _, _, .seq first second => BitState.append (sourceState second) (sourceState first)
  | _, _, .tensor left right => BitState.append (sourceState left) (sourceState right)

/-- Complete final garbage state as a function of the original argument. -/
def garbage : {inputWidth outputWidth : Nat} →
    (circuit : SourceCircuit inputWidth outputWidth) →
    BitState inputWidth → BitState (garbageWidth circuit)
  | _, _, .identity _, _ => noBits
  | _, _, .permute _, _ => noBits
  | _, _, .constant _, _ => noBits
  | _, _, .discard _, input => input
  | _, _, .andGate, input => andGarbage input
  | _, _, .orGate, input => orGarbage input
  | _, _, .notGate, input => notGarbage input
  | _, _, .fanout, input => fanoutGarbage input
  | _, _, .seq first second, input =>
      BitState.append (garbage second (eval first input)) (garbage first input)
  | _, _, .tensor left right, input =>
      BitState.append
        (garbage left (BitState.split _ _ input).1)
        (garbage right (BitState.split _ _ input).2)

/-- The exhaustive zero-scratch layout selected by the compiler. -/
abbrev simulationLayout {inputWidth outputWidth : Nat}
    (circuit : SourceCircuit inputWidth outputWidth) : Layout where
  sourceWidth := sourceWidth circuit
  scratchWidth := 0
  argumentWidth := inputWidth
  resultWidth := outputWidth
  garbageWidth := garbageWidth circuit
  balanced := source_garbage_balance circuit

end SourceCircuit

/-! ## Width transport and explicit structural block routing -/

/-- Dependent width transport for target syntax; it changes no wire order. -/
def castCircuit {leftWidth rightWidth : Nat} (width : leftWidth = rightWidth)
    (circuit : Circuit leftWidth) : Circuit rightWidth :=
  width ▸ circuit

/-- Circuit evaluation commutes exactly with width transport. -/
theorem eval_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth)
    (input : BitState leftWidth) :
    Circuit.eval (castCircuit width circuit) (castState width input) =
      castState width (Circuit.eval circuit input) := by
  cases width
  rfl

private def fourDecompose (a b c d : Nat) :
    Fin ((a + b) + (c + d)) ≃ (Fin a ⊕ Fin b) ⊕ (Fin c ⊕ Fin d) :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm)

private def fourCompose (a b c d : Nat) :
    (Fin a ⊕ Fin b) ⊕ (Fin c ⊕ Fin d) ≃ Fin ((a + b) + (c + d)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- Actively exchange the middle two of four adjacent ordered wire blocks. -/
def middleSwapWiring (a b c d : Nat) : WirePerm ((a + b) + (c + d)) :=
  (fourDecompose a b c d).trans <|
      (Equiv.sumSumSumComm (Fin a) (Fin b) (Fin c) (Fin d)).trans <|
      (fourCompose a c b d).trans <|
        finCongr (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d))

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

/-- The active middle-block permutation has the stated four-block action. -/
theorem middleSwapWiring_on_append {a b c d : Nat}
    (as : BitState a) (bs : BitState b) (cs : BitState c) (ds : BitState d) :
    WirePerm.onState (middleSwapWiring a b c d)
        (BitState.append (BitState.append as bs) (BitState.append cs ds)) =
      castState (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d))
        (BitState.append (BitState.append as cs) (BitState.append bs ds)) := by
  funext output
  obtain ⟨input, rfl⟩ := (middleSwapWiring a b c d).surjective output
  rw [WirePerm.onState_apply_image, castState_apply]
  let tagged := fourDecompose a b c d input
  have taggedBack : (fourDecompose a b c d).symm tagged = input := by
    simp [tagged]
  rcases tagged with ((index | index) | (index | index))
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.castAdd b index))) =
          Fin.castAdd (b + d) (Fin.castAdd c index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp

  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.castAdd (c + d) (Fin.natAdd a index))) =
          Fin.natAdd (a + c) (Fin.castAdd d index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.castAdd d index))) =
          Fin.castAdd (b + d) (Fin.natAdd a index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp
  · simp [fourDecompose] at taggedBack
    subst input
    have route :
        Fin.cast (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d)).symm
            (middleSwapWiring a b c d
              (Fin.natAdd (a + b) (Fin.natAdd c index))) =
          Fin.natAdd (a + c) (Fin.natAdd b index) := by
      apply Fin.ext
      simp [middleSwapWiring, fourDecompose, fourCompose]
    rw [route]
    simp

/-! ## State/circuit width transport used by the compiler proofs -/

@[simp]
private theorem castState_trans {left middle right : Nat}
    (first : left = middle) (second : middle = right) (state : BitState left) :
    castState second (castState first state) = castState (first.trans second) state := by
  cases first
  cases second
  rfl

private theorem castState_proof_irrel {left right : Nat}
    (first second : left = right) (state : BitState left) :
    castState first state = castState second state := by
  have : first = second := Subsingleton.elim _ _
  cases this
  rfl

private theorem castState_append_assoc {a b c : Nat} (as : BitState a)
    (bs : BitState b) (cs : BitState c) :
    castState (Nat.add_assoc a b c)
        (BitState.append (BitState.append as bs) cs) =
      BitState.append as (BitState.append bs cs) := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro ai
    rw [castState_apply]
    rw [show Fin.cast (Nat.add_assoc a b c).symm (Fin.castAdd (b + c) ai) =
          Fin.castAdd c (Fin.castAdd b ai) by
        apply Fin.ext
        rfl]
    simp
  · intro bc
    refine Fin.addCases ?_ ?_ bc
    · intro bi
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c).symm
            (Fin.natAdd a (Fin.castAdd c bi)) =
            Fin.castAdd c (Fin.natAdd a bi) by
          apply Fin.ext
          rfl]
      simp
    · intro ci
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c).symm
            (Fin.natAdd a (Fin.natAdd b ci)) = Fin.natAdd (a + b) ci by
          apply Fin.ext
          simp [Nat.add_assoc]]
      simp

private theorem castState_append_assoc_symm {a b c : Nat} (as : BitState a)
    (bs : BitState b) (cs : BitState c) :
    castState (Nat.add_assoc a b c).symm
        (BitState.append as (BitState.append bs cs)) =
      BitState.append (BitState.append as bs) cs := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro ab
    refine Fin.addCases ?_ ?_ ab
    · intro ai
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c)
            (Fin.castAdd c (Fin.castAdd b ai)) = Fin.castAdd (b + c) ai by
          apply Fin.ext
          rfl]
      simp
    · intro bi
      rw [castState_apply]
      rw [show Fin.cast (Nat.add_assoc a b c)
            (Fin.castAdd c (Fin.natAdd a bi)) =
            Fin.natAdd a (Fin.castAdd c bi) by
          apply Fin.ext
          rfl]
      simp
  · intro ci
    rw [castState_apply]
    rw [show Fin.cast (Nat.add_assoc a b c) (Fin.natAdd (a + b) ci) =
          Fin.natAdd a (Fin.natAdd b ci) by
        apply Fin.ext
        simp [Nat.add_assoc]]
    simp

private theorem castState_append_right {a b c : Nat} (width : b = c)
    (left : BitState a) (right : BitState b) :
    castState (congrArg (fun n => a + n) width) (BitState.append left right) =
      BitState.append left (castState width right) := by
  cases width
  rfl

private theorem castState_append_left {a b c : Nat} (width : a = b)
    (left : BitState a) (right : BitState c) :
    castState (congrArg (fun n => n + c) width) (BitState.append left right) =
      BitState.append (castState width left) right := by
  cases width
  rfl

private theorem castState_append_both {a b c d : Nat} (leftWidth : a = b)
    (rightWidth : c = d) (left : BitState a) (right : BitState c) :
    castState (congrArg₂ Nat.add leftWidth rightWidth) (BitState.append left right) =
      BitState.append (castState leftWidth left) (castState rightWidth right) := by
  cases leftWidth
  cases rightWidth
  rfl

private theorem append_noBits_left {width : Nat} (state : BitState width) :
    BitState.append noBits state =
      castState (Nat.zero_add width).symm state := by
  funext index
  refine Fin.addCases (fun impossible => Fin.elim0 impossible) ?_ index
  intro inner
  rw [BitState.append_natAdd, castState_apply]
  congr 1
  apply Fin.ext
  simp

private abbrev zeroLayout {sourceWidth argumentWidth resultWidth garbageWidth : Nat}
    (balanced : sourceWidth + argumentWidth = resultWidth + garbageWidth) : Layout where
  sourceWidth := sourceWidth
  scratchWidth := 0
  argumentWidth := argumentWidth
  resultWidth := resultWidth
  garbageWidth := garbageWidth
  balanced := balanced

private theorem zeroLayout_packInput {s a r g : Nat} (balanced : s + a = r + g)
    (source : BitState s) (argument : BitState a) :
    (zeroLayout balanced).packInput noBits source argument =
      castState (Nat.zero_add (s + a)).symm (BitState.append source argument) := by
  simpa [zeroLayout, Layout.packInput] using
    append_noBits_left (BitState.append source argument)

private theorem zeroLayout_packOutput {s a r g : Nat} (balanced : s + a = r + g)
    (result : BitState r) (garbage : BitState g) :
    (zeroLayout balanced).packOutput noBits result garbage =
      castState (Nat.zero_add (s + a)).symm
        (castState balanced.symm (BitState.append result garbage)) := by
  unfold Layout.packOutput
  rw [append_noBits_left, castState_trans, castState_trans]

/-- Normalized full-state equation for zero-scratch realizations. -/
private def ZeroRealizes {s a r g : Nat} (balanced : s + a = r + g)
    (circuit : Circuit (s + a)) (source : BitState s)
    (target : BitState a → BitState r) (garbage : BitState a → BitState g) : Prop :=
  ∀ argument,
    Circuit.eval circuit (BitState.append source argument) =
      castState balanced.symm (BitState.append (target argument) (garbage argument))

private theorem zero_realizes_iff {s a r g : Nat} (balanced : s + a = r + g)
    (circuit : Circuit (s + a)) (source : BitState s)
    (target : BitState a → BitState r) (garbage : BitState a → BitState g) :
    Realizes (zeroLayout balanced)
        (castCircuit (Nat.zero_add (s + a)).symm circuit)
        noBits source target garbage ↔
      ZeroRealizes balanced circuit source target garbage := by
  constructor <;> intro realizes argument
  · have raw := realizes argument
    rw [zeroLayout_packInput, eval_castCircuit, zeroLayout_packOutput] at raw
    exact castState_injective (Nat.zero_add (s + a)).symm raw
  · rw [zeroLayout_packInput, eval_castCircuit, zeroLayout_packOutput]
    exact congrArg (castState (Nat.zero_add (s + a)).symm) (realizes argument)

/-! ## Full-state serial composition -/

private theorem serialBalance {s₁ a b g₁ s₂ c g₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    (secondBalance : s₂ + b = c + g₂) :
    (s₂ + s₁) + a = c + (g₂ + g₁) := by
  calc
    (s₂ + s₁) + a = s₂ + (s₁ + a) := Nat.add_assoc s₂ s₁ a
    _ = s₂ + (b + g₁) := congrArg (s₂ + ·) firstBalance
    _ = (s₂ + b) + g₁ := (Nat.add_assoc s₂ b g₁).symm
    _ = (c + g₂) + g₁ := congrArg (· + g₁) secondBalance
    _ = c + (g₂ + g₁) := Nat.add_assoc c g₂ g₁

private theorem serialSecondWidth {s₁ a b g₁ s₂ : Nat}
    (firstBalance : s₁ + a = b + g₁) :
    (s₂ + b) + g₁ = (s₂ + s₁) + a := by
  calc
    (s₂ + b) + g₁ = s₂ + (b + g₁) := Nat.add_assoc s₂ b g₁
    _ = s₂ + (s₁ + a) := congrArg (s₂ + ·) firstBalance.symm
    _ = (s₂ + s₁) + a := (Nat.add_assoc s₂ s₁ a).symm

private def serialCircuit {s₁ a b g₁ s₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    (first : Circuit (s₁ + a)) (second : Circuit (s₂ + b)) :
    Circuit ((s₂ + s₁) + a) :=
  Circuit.seq
    (castCircuit (Nat.add_assoc s₂ s₁ a).symm
      (Circuit.tensor (Circuit.identity s₂) first))
    (castCircuit (serialSecondWidth (s₂ := s₂) firstBalance)
      (Circuit.tensor second (Circuit.identity g₁)))

private theorem serialIntermediate {s₁ a b g₁ s₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    (secondSource : BitState s₂) (result : BitState b)
    (firstGarbage : BitState g₁) :
    castState (Nat.add_assoc s₂ s₁ a).symm
        (BitState.append secondSource
          (castState firstBalance.symm (BitState.append result firstGarbage))) =
      castState (serialSecondWidth (s₂ := s₂) firstBalance)
        (BitState.append (BitState.append secondSource result) firstGarbage) := by
  let rightCast : s₂ + (b + g₁) = s₂ + (s₁ + a) :=
    congrArg (fun n => s₂ + n) firstBalance.symm
  let reassociate : s₂ + (b + g₁) = (s₂ + b) + g₁ :=
    (Nat.add_assoc s₂ b g₁).symm
  let base := BitState.append secondSource (BitState.append result firstGarbage)
  calc
    castState (Nat.add_assoc s₂ s₁ a).symm
        (BitState.append secondSource
          (castState firstBalance.symm (BitState.append result firstGarbage))) =
      castState (Nat.add_assoc s₂ s₁ a).symm (castState rightCast base) := by
        rw [castState_append_right]
    _ = castState (rightCast.trans (Nat.add_assoc s₂ s₁ a).symm) base :=
      castState_trans _ _ _
    _ = castState (reassociate.trans
          (serialSecondWidth (s₂ := s₂) firstBalance)) base :=
      castState_proof_irrel _ _ _
    _ = castState (serialSecondWidth (s₂ := s₂) firstBalance)
          (castState reassociate base) := (castState_trans _ _ _).symm
    _ = castState (serialSecondWidth (s₂ := s₂) firstBalance)
          (BitState.append (BitState.append secondSource result) firstGarbage) := by
      rw [castState_append_assoc_symm]

private theorem serialFinal {s₁ a b g₁ s₂ c g₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    (secondBalance : s₂ + b = c + g₂)
    (result : BitState c) (secondGarbage : BitState g₂)
    (firstGarbage : BitState g₁) :
    castState (serialSecondWidth (s₂ := s₂) firstBalance)
        (BitState.append
          (castState secondBalance.symm (BitState.append result secondGarbage))
          firstGarbage) =
      castState (serialBalance firstBalance secondBalance).symm
        (BitState.append result (BitState.append secondGarbage firstGarbage)) := by
  let reassociate : c + (g₂ + g₁) = (c + g₂) + g₁ :=
    (Nat.add_assoc c g₂ g₁).symm
  let leftCast : (c + g₂) + g₁ = (s₂ + b) + g₁ :=
    congrArg (fun n => n + g₁) secondBalance.symm
  let base := BitState.append result (BitState.append secondGarbage firstGarbage)
  calc
    castState (serialSecondWidth (s₂ := s₂) firstBalance)
        (BitState.append
          (castState secondBalance.symm (BitState.append result secondGarbage))
          firstGarbage) =
      castState (serialSecondWidth (s₂ := s₂) firstBalance)
        (castState leftCast
          (BitState.append (BitState.append result secondGarbage) firstGarbage)) := by
        rw [castState_append_left]
    _ = castState (serialSecondWidth (s₂ := s₂) firstBalance)
        (castState leftCast (castState reassociate base)) := by
      rw [castState_append_assoc_symm]
    _ = castState
        (reassociate.trans
          (leftCast.trans (serialSecondWidth (s₂ := s₂) firstBalance))) base := by
      rw [castState_trans, castState_trans]
    _ = castState (serialBalance firstBalance secondBalance).symm base :=
      castState_proof_irrel _ _ _

private theorem zeroRealizes_serial {s₁ a b g₁ s₂ c g₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    (secondBalance : s₂ + b = c + g₂)
    {first : Circuit (s₁ + a)} {second : Circuit (s₂ + b)}
    {firstSource : BitState s₁} {secondSource : BitState s₂}
    {firstTarget : BitState a → BitState b}
    {secondTarget : BitState b → BitState c}
    {firstGarbage : BitState a → BitState g₁}
    {secondGarbage : BitState b → BitState g₂}
    (firstRealizes : ZeroRealizes firstBalance first firstSource
      firstTarget firstGarbage)
    (secondRealizes : ZeroRealizes secondBalance second secondSource
      secondTarget secondGarbage) :
    @ZeroRealizes (s₂ + s₁) a c (g₂ + g₁)
      (serialBalance firstBalance secondBalance)
      (serialCircuit firstBalance first second)
      (BitState.append secondSource firstSource)
      (fun argument => secondTarget (firstTarget argument))
      (fun argument => BitState.append (secondGarbage (firstTarget argument))
        (firstGarbage argument)) := by
  intro argument
  simp only [serialCircuit, Circuit.eval_seq]
  rw [← castState_append_assoc_symm secondSource firstSource argument]
  rw [eval_castCircuit, Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [firstRealizes argument,
    serialIntermediate (s₁ := s₁) (a := a) (b := b) (g₁ := g₁)
      (s₂ := s₂) firstBalance secondSource (firstTarget argument)
      (firstGarbage argument)]
  rw [eval_castCircuit, Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [secondRealizes (firstTarget argument),
    serialFinal (s₁ := s₁) (a := a) (b := b) (g₁ := g₁)
      (s₂ := s₂) (c := c) (g₂ := g₂) firstBalance secondBalance
      (secondTarget (firstTarget argument))
      (secondGarbage (firstTarget argument)) (firstGarbage argument)]

/-! ## Full-state tensor composition -/

private theorem tensorBalance {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂) :
    (s₁ + s₂) + (a₁ + a₂) = (r₁ + r₂) + (g₁ + g₂) := by
  calc
    (s₁ + s₂) + (a₁ + a₂) = (s₁ + a₁) + (s₂ + a₂) := by ac_rfl
    _ = (r₁ + g₁) + (r₂ + g₂) := congrArg₂ Nat.add leftBalance rightBalance
    _ = (r₁ + r₂) + (g₁ + g₂) := by ac_rfl

private theorem tensorProcessWidth (s₁ s₂ a₁ a₂ : Nat) :
    (s₁ + a₁) + (s₂ + a₂) = (s₁ + s₂) + (a₁ + a₂) := by
  ac_rfl

private theorem tensorOutputWidth {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂) :
    (r₁ + g₁) + (r₂ + g₂) = (s₁ + s₂) + (a₁ + a₂) := by
  calc
    (r₁ + g₁) + (r₂ + g₂) = (s₁ + a₁) + (s₂ + a₂) :=
      congrArg₂ Nat.add leftBalance.symm rightBalance.symm
    _ = (s₁ + s₂) + (a₁ + a₂) := by ac_rfl

private def tensorCircuit {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂)
    (left : Circuit (s₁ + a₁)) (right : Circuit (s₂ + a₂)) :
    Circuit ((s₁ + s₂) + (a₁ + a₂)) :=
  Circuit.seq
    (Circuit.permute (middleSwapWiring s₁ s₂ a₁ a₂))
    (Circuit.seq
      (castCircuit (tensorProcessWidth s₁ s₂ a₁ a₂) (Circuit.tensor left right))
      (castCircuit (tensorOutputWidth leftBalance rightBalance)
        (Circuit.permute (middleSwapWiring r₁ g₁ r₂ g₂))))

private theorem tensorIntermediate {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂)
    (result₁ : BitState r₁) (garbage₁ : BitState g₁)
    (result₂ : BitState r₂) (garbage₂ : BitState g₂) :
    castState (tensorProcessWidth s₁ s₂ a₁ a₂)
        (BitState.append
          (castState leftBalance.symm (BitState.append result₁ garbage₁))
          (castState rightBalance.symm (BitState.append result₂ garbage₂))) =
      castState (tensorOutputWidth leftBalance rightBalance)
        (BitState.append (BitState.append result₁ garbage₁)
          (BitState.append result₂ garbage₂)) := by
  let bothCast : (r₁ + g₁) + (r₂ + g₂) =
      (s₁ + a₁) + (s₂ + a₂) :=
    congrArg₂ Nat.add leftBalance.symm rightBalance.symm
  let base := BitState.append (BitState.append result₁ garbage₁)
    (BitState.append result₂ garbage₂)
  calc
    castState (tensorProcessWidth s₁ s₂ a₁ a₂)
        (BitState.append
          (castState leftBalance.symm (BitState.append result₁ garbage₁))
          (castState rightBalance.symm (BitState.append result₂ garbage₂))) =
      castState (tensorProcessWidth s₁ s₂ a₁ a₂) (castState bothCast base) := by
        rw [castState_append_both]
    _ = castState (bothCast.trans (tensorProcessWidth s₁ s₂ a₁ a₂)) base :=
      castState_trans _ _ _
    _ = castState (tensorOutputWidth leftBalance rightBalance) base :=
      castState_proof_irrel _ _ _

private theorem tensorFinal {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂)
    (result₁ : BitState r₁) (garbage₁ : BitState g₁)
    (result₂ : BitState r₂) (garbage₂ : BitState g₂) :
    castState (tensorOutputWidth leftBalance rightBalance)
        (castState (by ac_rfl : (r₁ + r₂) + (g₁ + g₂) =
            (r₁ + g₁) + (r₂ + g₂))
          (BitState.append (BitState.append result₁ result₂)
            (BitState.append garbage₁ garbage₂))) =
      castState (tensorBalance leftBalance rightBalance).symm
        (BitState.append (BitState.append result₁ result₂)
          (BitState.append garbage₁ garbage₂)) := by
  rw [castState_trans]
  apply castState_proof_irrel

private theorem zeroRealizes_tensor {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂)
    {leftCircuit : Circuit (s₁ + a₁)} {rightCircuit : Circuit (s₂ + a₂)}
    {leftSource : BitState s₁} {rightSource : BitState s₂}
    {leftTarget : BitState a₁ → BitState r₁}
    {rightTarget : BitState a₂ → BitState r₂}
    {leftGarbage : BitState a₁ → BitState g₁}
    {rightGarbage : BitState a₂ → BitState g₂}
    (leftRealizes : ZeroRealizes leftBalance leftCircuit leftSource
      leftTarget leftGarbage)
    (rightRealizes : ZeroRealizes rightBalance rightCircuit rightSource
      rightTarget rightGarbage) :
    @ZeroRealizes (s₁ + s₂) (a₁ + a₂) (r₁ + r₂) (g₁ + g₂)
      (tensorBalance leftBalance rightBalance)
      (tensorCircuit leftBalance rightBalance leftCircuit rightCircuit)
      (BitState.append leftSource rightSource)
      (fun argument => BitState.append
        (leftTarget (BitState.split a₁ a₂ argument).1)
        (rightTarget (BitState.split a₁ a₂ argument).2))
      (fun argument => BitState.append
        (leftGarbage (BitState.split a₁ a₂ argument).1)
        (rightGarbage (BitState.split a₁ a₂ argument).2)) := by
  intro argument
  let argument₁ := (BitState.split a₁ a₂ argument).1
  let argument₂ := (BitState.split a₁ a₂ argument).2
  have argument_eq : argument = BitState.append argument₁ argument₂ :=
    (BitState.append_split argument).symm
  rw [argument_eq]
  simp only [tensorCircuit, BitState.split_append, Circuit.eval_seq]
  rw [Circuit.eval_permute, middleSwapWiring_on_append]
  rw [eval_castCircuit, Circuit.eval_tensor_append]
  rw [leftRealizes argument₁, rightRealizes argument₂]
  rw [tensorIntermediate (s₁ := s₁) (a₁ := a₁) (r₁ := r₁) (g₁ := g₁)
    (s₂ := s₂) (a₂ := a₂) (r₂ := r₂) (g₂ := g₂)
    leftBalance rightBalance (leftTarget argument₁) (leftGarbage argument₁)
    (rightTarget argument₂) (rightGarbage argument₂)]
  rw [eval_castCircuit, Circuit.eval_permute, middleSwapWiring_on_append]
  rw [tensorFinal (s₁ := s₁) (a₁ := a₁) (r₁ := r₁) (g₁ := g₁)
    (s₂ := s₂) (a₂ := a₂) (r₂ := r₂) (g₂ := g₂)
    leftBalance rightBalance (leftTarget argument₁) (leftGarbage argument₁)
    (rightTarget argument₂) (rightGarbage argument₂)]

end ConservativeLogic.Simulation
