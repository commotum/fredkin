import ConservativeLogic.Simulation.Source
import ConservativeLogic.Realization.Primitive
import ConservativeLogic.Circuit.Timed
import ConservativeLogic.Circuit.Structural
import ConservativeLogic.Circuit.Resources

/-!
# Constructive Fredkin simulation of finite source circuits

Every source-language node is compiled to the fixed target `Circuit` grammar.
The construction exposes its complete initialized source and complete garbage
function.  Serial compilation retains earlier garbage untouched; tensor
compilation uses proved structural permutations to keep its two inputs
disjoint.  No scratch wire, arbitrary target equivalence, semantic gate,
implicit FAN-OUT, or discard is introduced.

The result is a static theorem for the explicitly generated feed-forward
source language.  Target `WirePerm` nodes remain a selected zero-delay
structural reindexing resource, so this is Fredkin-plus-reindexing simulation,
not pure physical Fredkin synthesis or a sequential-network theorem.
-/

namespace ConservativeLogic.Simulation

open Realization
open Realization.Primitive

namespace SourceCircuit

/-- Fixed source width used by the selected recursive compilation. -/
abbrev sourceWidth : {inputWidth outputWidth : Nat} →
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
abbrev garbageWidth : {inputWidth outputWidth : Nat} →
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
abbrev sourceState : {inputWidth outputWidth : Nat} →
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
abbrev garbage : {inputWidth outputWidth : Nat} →
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

/-! ## Compatibility names for the former compiler-owned structural API -/

/-- Compatibility alias for `Circuit.cast`; new code should use the circuit-owned name. -/
abbrev castCircuit {leftWidth rightWidth : Nat} (width : leftWidth = rightWidth)
    (circuit : Circuit leftWidth) : Circuit rightWidth :=
  Circuit.cast width circuit

/-- Compatibility theorem for `Circuit.eval_cast`. -/
theorem eval_castCircuit {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (circuit : Circuit leftWidth)
    (input : BitState leftWidth) :
    Circuit.eval (castCircuit width circuit) (castState width input) =
      castState width (Circuit.eval circuit input) :=
  Circuit.eval_cast width circuit input

/-- Compatibility alias for the circuit-owned four-block middle swap. -/
abbrev middleSwapWiring (a b c d : Nat) : WirePerm ((a + b) + (c + d)) :=
  Circuit.middleSwapWiring a b c d

/-- Compatibility theorem for `Circuit.middleSwapWiring_on_append`. -/
theorem middleSwapWiring_on_append {a b c d : Nat}
    (as : BitState a) (bs : BitState b) (cs : BitState c) (ds : BitState d) :
    WirePerm.onState (middleSwapWiring a b c d)
        (BitState.append (BitState.append as bs) (BitState.append cs ds)) =
      castState (by ac_rfl : (a + c) + (b + d) = (a + b) + (c + d))
        (BitState.append (BitState.append as cs) (BitState.append bs ds)) :=
  Circuit.middleSwapWiring_on_append as bs cs ds

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
        (Circuit.cast (Nat.zero_add (s + a)).symm circuit)
        noBits source target garbage ↔
      ZeroRealizes balanced circuit source target garbage := by
  constructor <;> intro realizes argument
  · have raw := realizes argument
    rw [zeroLayout_packInput, Circuit.eval_cast, zeroLayout_packOutput] at raw
    exact castState_injective (Nat.zero_add (s + a)).symm raw
  · rw [zeroLayout_packInput, Circuit.eval_cast, zeroLayout_packOutput]
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
    (Circuit.cast (Nat.add_assoc s₂ s₁ a).symm
      (Circuit.tensor (Circuit.identity s₂) first))
    (Circuit.cast (serialSecondWidth (s₂ := s₂) firstBalance)
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
  rw [Circuit.eval_cast, Circuit.eval_tensor_append, Circuit.eval_identity]
  rw [firstRealizes argument,
    serialIntermediate (s₁ := s₁) (a := a) (b := b) (g₁ := g₁)
      (s₂ := s₂) firstBalance secondSource (firstTarget argument)
      (firstGarbage argument)]
  rw [Circuit.eval_cast, Circuit.eval_tensor_append, Circuit.eval_identity]
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
    (Circuit.permute (Circuit.middleSwapWiring s₁ s₂ a₁ a₂))
    (Circuit.seq
      (Circuit.cast (tensorProcessWidth s₁ s₂ a₁ a₂) (Circuit.tensor left right))
      (Circuit.cast (tensorOutputWidth leftBalance rightBalance)
        (Circuit.permute (Circuit.middleSwapWiring r₁ g₁ r₂ g₂))))

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
        exact congrArg (castState (tensorProcessWidth s₁ s₂ a₁ a₂))
          (castState_append_both leftBalance.symm rightBalance.symm
            (BitState.append result₁ garbage₁)
            (BitState.append result₂ garbage₂)).symm
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
  rw [Circuit.eval_permute, Circuit.middleSwapWiring_on_append]
  rw [Circuit.eval_cast, Circuit.eval_tensor_append]
  rw [leftRealizes argument₁, rightRealizes argument₂]
  rw [tensorIntermediate (s₁ := s₁) (a₁ := a₁) (r₁ := r₁) (g₁ := g₁)
    (s₂ := s₂) (a₂ := a₂) (r₂ := r₂) (g₂ := g₂)
    leftBalance rightBalance (leftTarget argument₁) (leftGarbage argument₁)
    (rightTarget argument₂) (rightGarbage argument₂)]
  rw [Circuit.eval_cast, Circuit.eval_permute, Circuit.middleSwapWiring_on_append]
  rw [tensorFinal (s₁ := s₁) (a₁ := a₁) (r₁ := r₁) (g₁ := g₁)
    (s₂ := s₂) (a₂ := a₂) (r₂ := r₂) (g₂ := g₂)
    leftBalance rightBalance (leftTarget argument₁) (leftGarbage argument₁)
    (rightTarget argument₂) (rightGarbage argument₂)]

/-! ## Recursive compiler -/

namespace SourceCircuit

/-- Normalized target term before the public leading-zero scratch transport. -/
private def compileCore : {inputWidth outputWidth : Nat} →
    (source : SourceCircuit inputWidth outputWidth) →
    Circuit (sourceWidth source + inputWidth)
  | _, _, .identity width => Circuit.identity (0 + width)
  | _, _, .permute wiring =>
      Circuit.cast (Nat.zero_add _).symm (Circuit.permute wiring)
  | _, _, .constant _ => Circuit.identity (_ + 0)
  | _, _, .discard width => Circuit.identity (0 + width)
  | _, _, .andGate => fredkinAndCircuit
  | _, _, .orGate => fredkinOrCircuit
  | _, _, .notGate => fredkinNotCircuit
  | _, _, .fanout => fredkinFanoutCircuit
  | _, _, .seq first second =>
      serialCircuit (source_garbage_balance first)
        (compileCore first) (compileCore second)
  | _, _, .tensor left right =>
      tensorCircuit (source_garbage_balance left) (source_garbage_balance right)
        (compileCore left) (compileCore right)

/--
Compile an explicit finite source term to the balanced target grammar. The
leading transport accounts only for the canonical width-zero scratch prefix.
-/
def compile {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Circuit (simulationLayout source).width :=
  Circuit.cast (Nat.zero_add (sourceWidth source + inputWidth)).symm
    (compileCore source)

private theorem append_noBits_right {width : Nat} (state : BitState width) :
    BitState.append state noBits = castState (Nat.add_zero width).symm state := by
  funext index
  refine Fin.addCases ?_ (fun impossible => Fin.elim0 impossible) index
  intro inner
  rw [BitState.append_castAdd, castState_apply]
  congr 1

private theorem identityCore_realizes (width : Nat) :
    ZeroRealizes (source_garbage_balance (.identity width))
      (compileCore (.identity width)) (sourceState (.identity width))
      (eval (.identity width)) (garbage (.identity width)) := by
  intro argument
  simp only [compileCore, Circuit.eval_identity, sourceState, eval, garbage]
  rw [append_noBits_left, append_noBits_right, castState_trans]

private theorem permuteCore_realizes {width : Nat} (wiring : WirePerm width) :
    ZeroRealizes (source_garbage_balance (.permute wiring))
      (compileCore (.permute wiring)) (sourceState (.permute wiring))
      (eval (.permute wiring)) (garbage (.permute wiring)) := by
  intro argument
  simp only [compileCore, sourceState, eval, garbage]
  rw [append_noBits_left, Circuit.eval_cast, Circuit.eval_permute]
  rw [append_noBits_right, castState_trans]

private theorem constantCore_realizes {width : Nat} (value : BitState width) :
    ZeroRealizes (source_garbage_balance (.constant value))
      (compileCore (.constant value)) (sourceState (.constant value))
      (eval (.constant value)) (garbage (.constant value)) := by
  intro argument
  have argument_eq : argument = noBits := by
    funext index
    exact Fin.elim0 index
  subst argument
  rfl

private theorem discardCore_realizes (width : Nat) :
    ZeroRealizes (source_garbage_balance (.discard width))
      (compileCore (.discard width)) (sourceState (.discard width))
      (eval (.discard width)) (garbage (.discard width)) := by
  intro argument
  rfl

private theorem andCore_realizes :
    ZeroRealizes (source_garbage_balance .andGate)
      (compileCore .andGate) (sourceState .andGate)
      andTarget (garbage .andGate) := by
  apply (zero_realizes_iff (source_garbage_balance .andGate)
    fredkinAndCircuit andSource andTarget andGarbage).1
  simpa [zeroLayout, andLayout, Circuit.cast, source_garbage_balance,
    sourceWidth, garbageWidth, garbage] using fredkin_realizes_and

private theorem orCore_realizes :
    ZeroRealizes (source_garbage_balance .orGate)
      (compileCore .orGate) (sourceState .orGate)
      orTarget (garbage .orGate) := by
  apply (zero_realizes_iff (source_garbage_balance .orGate)
    fredkinOrCircuit orSource orTarget orGarbage).1
  simpa [zeroLayout, orLayout, andLayout, Circuit.cast, source_garbage_balance,
    sourceWidth, garbageWidth, garbage] using fredkin_realizes_or

private theorem notCore_realizes :
    ZeroRealizes (source_garbage_balance .notGate)
      (compileCore .notGate) (sourceState .notGate)
      notTarget (garbage .notGate) := by
  apply (zero_realizes_iff (source_garbage_balance .notGate)
    fredkinNotCircuit notFanoutSource notTarget notGarbage).1
  simpa [zeroLayout, notLayout, Circuit.cast, source_garbage_balance,
    sourceWidth, garbageWidth, garbage] using fredkin_realizes_not

private theorem fanoutCore_realizes :
    ZeroRealizes (source_garbage_balance .fanout)
      (compileCore .fanout) (sourceState .fanout)
      fanoutTarget (garbage .fanout) := by
  apply (zero_realizes_iff (source_garbage_balance .fanout)
    fredkinFanoutCircuit notFanoutSource fanoutTarget fanoutGarbage).1
  simpa [zeroLayout, fanoutLayout, Circuit.cast, source_garbage_balance,
    sourceWidth, garbageWidth, garbage] using fredkin_realizes_fanout

private theorem eval_andGate_eq : eval .andGate = andTarget := by
  rfl

private theorem eval_orGate_eq : eval .orGate = orTarget := by
  rfl

private theorem eval_notGate_eq : eval .notGate = notTarget := by
  rfl

private theorem eval_fanout_eq : eval .fanout = fanoutTarget := by
  funext input index
  refine Fin.cases rfl ?_ index
  intro tail
  refine Fin.cases rfl ?_ tail
  intro impossible
  exact Fin.elim0 impossible

private theorem compileCore_realizes {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    ZeroRealizes (source_garbage_balance source) (compileCore source)
      (sourceState source) (eval source) (garbage source) := by
  induction source with
  | identity width => exact identityCore_realizes width
  | permute wiring => exact permuteCore_realizes wiring
  | constant value => exact constantCore_realizes value
  | discard width => exact discardCore_realizes width
  | andGate =>
      rw [eval_andGate_eq]
      exact andCore_realizes
  | orGate =>
      rw [eval_orGate_eq]
      exact orCore_realizes
  | notGate =>
      rw [eval_notGate_eq]
      exact notCore_realizes
  | fanout =>
      rw [eval_fanout_eq]
      exact fanoutCore_realizes
  | seq first second firstIH secondIH =>
      exact zeroRealizes_serial (source_garbage_balance first)
        (source_garbage_balance second) firstIH secondIH
  | tensor left right leftIH rightIH =>
      exact zeroRealizes_tensor (source_garbage_balance left)
        (source_garbage_balance right) leftIH rightIH

/--
The compiled target realizes the complete source semantics with its exact
fixed source, exact result, exact garbage, and no scratch wires.
-/
theorem compile_realizes {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Realizes (simulationLayout source) (compile source) noBits
      (sourceState source) (eval source) (garbage source) := by
  have normalized := (zero_realizes_iff (source_garbage_balance source)
    (compileCore source) (sourceState source) (eval source) (garbage source)).2
      (compileCore_realizes source)
  simpa [simulationLayout, zeroLayout, compile] using normalized

end SourceCircuit

end ConservativeLogic.Simulation

namespace ConservativeLogic.Simulation.SourceCircuit

private theorem compileCore_fredkinCount {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Circuit.fredkinCount (compileCore source) = logicGateCount source := by
  induction source with
  | identity width => rfl
  | permute wiring => simp [compileCore, Circuit.fredkinCount, logicGateCount]
  | constant value => rfl
  | discard width => rfl
  | andGate =>
      simp [compileCore, Circuit.fredkinCount, logicGateCount,
        Realization.Primitive.fredkinAndCircuit,
        Realization.Primitive.routedFredkin]
  | orGate =>
      simp [compileCore, Circuit.fredkinCount, logicGateCount,
        Realization.Primitive.fredkinOrCircuit,
        Realization.Primitive.routedFredkin]
  | notGate =>
      simp [compileCore, Circuit.fredkinCount, logicGateCount,
        Realization.Primitive.fredkinNotCircuit,
        Realization.Primitive.routedFredkin]
  | fanout =>
      simp [compileCore, Circuit.fredkinCount, logicGateCount,
        Realization.Primitive.fredkinFanoutCircuit,
        Realization.Primitive.routedFredkin]
  | seq first second firstIH secondIH =>
      simp [compileCore, Simulation.serialCircuit, Circuit.fredkinCount,
        logicGateCount, firstIH, secondIH]
  | tensor left right leftIH rightIH =>
      simp [compileCore, Simulation.tensorCircuit, Circuit.fredkinCount,
        logicGateCount, leftIH, rightIH]

/-- Compilation uses exactly one target Fredkin per source logic gate. -/
theorem compile_fredkinCount {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Circuit.fredkinCount (compile source) = logicGateCount source := by
  rw [compile, Circuit.fredkinCount_castCircuit]
  exact compileCore_fredkinCount source

/-! ## Static timing of compiled circuits -/

private theorem hasLatency_castCircuit {leftWidth rightWidth latency : Nat}
    (width : leftWidth = rightWidth) {circuit : Circuit leftWidth}
    (timed : Circuit.HasLatency circuit latency) :
    Circuit.HasLatency (Circuit.cast width circuit) latency := by
  cases width
  exact timed

private theorem routedFredkin_hasLatency_zero
    (inputWiring outputWiring : WirePerm 3) :
    Circuit.HasLatency
      (Realization.Primitive.routedFredkin inputWiring outputWiring) 0 := by
  unfold Realization.Primitive.routedFredkin
  have timed : Circuit.HasLatency
      (Circuit.seq (Circuit.permute inputWiring)
        (Circuit.seq Circuit.fredkin (Circuit.permute outputWiring)))
      (0 + (0 + 0)) :=
    Circuit.HasLatency.seq (Circuit.hasLatency_permute inputWiring)
      (Circuit.HasLatency.seq Circuit.hasLatency_fredkin
        (Circuit.hasLatency_permute outputWiring))
  intro input output actual path
  have delay : actual = 0 + (0 + 0) := timed path
  simpa using delay

private theorem serialCircuit_hasLatency_zero {s₁ a b g₁ s₂ : Nat}
    (firstBalance : s₁ + a = b + g₁)
    {first : Circuit (s₁ + a)} {second : Circuit (s₂ + b)}
    (firstTimed : Circuit.HasLatency first 0)
    (secondTimed : Circuit.HasLatency second 0) :
    Circuit.HasLatency
      (Simulation.serialCircuit firstBalance first second) 0 := by
  have firstStage : Circuit.HasLatency
      (Circuit.tensor (Circuit.identity s₂) first) 0 :=
    Circuit.HasLatency.tensor (Circuit.hasLatency_identity s₂) firstTimed
  have firstStageCast : Circuit.HasLatency
      (Circuit.cast (Nat.add_assoc s₂ s₁ a).symm
        (Circuit.tensor (Circuit.identity s₂) first)) 0 :=
    hasLatency_castCircuit (Nat.add_assoc s₂ s₁ a).symm firstStage
  have secondStage : Circuit.HasLatency
      (Circuit.tensor second (Circuit.identity g₁)) 0 :=
    Circuit.HasLatency.tensor secondTimed (Circuit.hasLatency_identity g₁)
  have secondStageCast : Circuit.HasLatency
      (Circuit.cast
        (Simulation.serialSecondWidth (s₂ := s₂) firstBalance)
        (Circuit.tensor second (Circuit.identity g₁))) 0 :=
    hasLatency_castCircuit
      (Simulation.serialSecondWidth (s₂ := s₂) firstBalance) secondStage
  have timed : Circuit.HasLatency
      (Circuit.seq
        (Circuit.cast (Nat.add_assoc s₂ s₁ a).symm
          (Circuit.tensor (Circuit.identity s₂) first))
        (Circuit.cast
          (Simulation.serialSecondWidth (s₂ := s₂) firstBalance)
          (Circuit.tensor second (Circuit.identity g₁)))) (0 + 0) :=
    Circuit.HasLatency.seq firstStageCast secondStageCast
  unfold Simulation.serialCircuit
  intro input output actual path
  have delay : actual = 0 + 0 := timed path
  simpa using delay

private theorem tensorCircuit_hasLatency_zero
    {s₁ a₁ r₁ g₁ s₂ a₂ r₂ g₂ : Nat}
    (leftBalance : s₁ + a₁ = r₁ + g₁)
    (rightBalance : s₂ + a₂ = r₂ + g₂)
    {left : Circuit (s₁ + a₁)} {right : Circuit (s₂ + a₂)}
    (leftTimed : Circuit.HasLatency left 0)
    (rightTimed : Circuit.HasLatency right 0) :
    Circuit.HasLatency
      (Simulation.tensorCircuit leftBalance rightBalance left right) 0 := by
  have inputRouting : Circuit.HasLatency
      (Circuit.permute (Circuit.middleSwapWiring s₁ s₂ a₁ a₂)) 0 :=
    Circuit.hasLatency_permute _
  have body : Circuit.HasLatency (Circuit.tensor left right) 0 :=
    Circuit.HasLatency.tensor leftTimed rightTimed
  have bodyCast : Circuit.HasLatency
      (Circuit.cast
        (Simulation.tensorProcessWidth s₁ s₂ a₁ a₂)
        (Circuit.tensor left right)) 0 :=
    hasLatency_castCircuit
      (Simulation.tensorProcessWidth s₁ s₂ a₁ a₂) body
  have outputRouting : Circuit.HasLatency
      (Circuit.permute (Circuit.middleSwapWiring r₁ g₁ r₂ g₂)) 0 :=
    Circuit.hasLatency_permute _
  have outputRoutingCast : Circuit.HasLatency
      (Circuit.cast
        (Simulation.tensorOutputWidth leftBalance rightBalance)
        (Circuit.permute (Circuit.middleSwapWiring r₁ g₁ r₂ g₂))) 0 :=
    hasLatency_castCircuit
      (Simulation.tensorOutputWidth leftBalance rightBalance) outputRouting
  have processThenRoute : Circuit.HasLatency
      (Circuit.seq
        (Circuit.cast
          (Simulation.tensorProcessWidth s₁ s₂ a₁ a₂)
          (Circuit.tensor left right))
        (Circuit.cast
          (Simulation.tensorOutputWidth leftBalance rightBalance)
          (Circuit.permute
            (Circuit.middleSwapWiring r₁ g₁ r₂ g₂)))) (0 + 0) :=
    Circuit.HasLatency.seq bodyCast outputRoutingCast
  have timed : Circuit.HasLatency
      (Circuit.seq
        (Circuit.permute (Circuit.middleSwapWiring s₁ s₂ a₁ a₂))
        (Circuit.seq
          (Circuit.cast
            (Simulation.tensorProcessWidth s₁ s₂ a₁ a₂)
            (Circuit.tensor left right))
          (Circuit.cast
            (Simulation.tensorOutputWidth leftBalance rightBalance)
            (Circuit.permute
              (Circuit.middleSwapWiring r₁ g₁ r₂ g₂)))))
      (0 + (0 + 0)) :=
    Circuit.HasLatency.seq inputRouting processThenRoute
  unfold Simulation.tensorCircuit
  intro input output actual path
  have delay : actual = 0 + (0 + 0) := timed path
  simpa using delay

private theorem compileCore_hasLatency_zero {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Circuit.HasLatency (compileCore source) 0 := by
  induction source with
  | identity width => exact Circuit.hasLatency_identity (0 + width)
  | permute wiring =>
      exact hasLatency_castCircuit (Nat.zero_add _).symm
        (Circuit.hasLatency_permute wiring)
  | constant value => exact Circuit.hasLatency_identity (_ + 0)
  | discard width => exact Circuit.hasLatency_identity (0 + width)
  | andGate =>
      change Circuit.HasLatency
        (Realization.Primitive.routedFredkin
          Realization.Primitive.andInputWiring
          Realization.Primitive.resultFromDataOneWiring) 0
      exact routedFredkin_hasLatency_zero
        Realization.Primitive.andInputWiring
        Realization.Primitive.resultFromDataOneWiring
  | orGate =>
      change Circuit.HasLatency
        (Realization.Primitive.routedFredkin
          Realization.Primitive.orInputWiring
          Realization.Primitive.resultFromDataOneWiring) 0
      exact routedFredkin_hasLatency_zero
        Realization.Primitive.orInputWiring
        Realization.Primitive.resultFromDataOneWiring
  | notGate =>
      change Circuit.HasLatency
        (Realization.Primitive.routedFredkin
          Realization.Primitive.notFanoutInputWiring
          Realization.Primitive.resultFromDataTwoWiring) 0
      exact routedFredkin_hasLatency_zero
        Realization.Primitive.notFanoutInputWiring
        Realization.Primitive.resultFromDataTwoWiring
  | fanout =>
      change Circuit.HasLatency
        (Realization.Primitive.routedFredkin
          Realization.Primitive.notFanoutInputWiring (Equiv.refl _)) 0
      exact routedFredkin_hasLatency_zero
        Realization.Primitive.notFanoutInputWiring (Equiv.refl _)
  | seq first second firstIH secondIH =>
      exact serialCircuit_hasLatency_zero
        (source_garbage_balance first) firstIH secondIH
  | tensor left right leftIH rightIH =>
      exact tensorCircuit_hasLatency_zero
        (source_garbage_balance left) (source_garbage_balance right)
        leftIH rightIH

/-- Every path through a compiled source circuit has zero unit-wire latency. -/
theorem compile_hasLatency_zero {inputWidth outputWidth : Nat}
    (source : SourceCircuit inputWidth outputWidth) :
    Circuit.HasLatency (compile source) 0 := by
  unfold compile
  exact hasLatency_castCircuit _ (compileCore_hasLatency_zero source)

end ConservativeLogic.Simulation.SourceCircuit
