import Mathlib.Data.Fintype.BigOperators
import ConservativeLogic.Circuit.Semantics

/-!
# Explicit source, scratch, result, and garbage interfaces

This module formalizes the paper's static realization pattern with every wire
classified. A `Layout` has a fixed source block, a returned-clean scratch
block, an argument block, a result block, and a complete garbage block.
Canonical boundaries are ordered

`(scratch, source, argument) → (scratch, result, garbage)`.

The same explicit scratch value occurs on both sides of `Realizes`; workspace
that is not restored belongs in garbage. Source is fixed independently of the
argument but need not be returned. Garbage is an explicit function, never an
existentially hidden output or a circuit-level discard.

These are initialized-slice facts about static `Circuit.eval`. They do not add
an arbitrary semantic gate to `Circuit`, construct an inverse/uncompute
network, or claim timing, physical routing, entropy, or energy results.
-/

namespace ConservativeLogic.Realization

/-- Transport a Boolean state along an equality of widths, without changing any value. -/
def castState {m n : Nat} (width : m = n) (state : BitState m) : BitState n :=
  width ▸ state

/-- Pointwise form of width transport, with the index transported in the reverse direction. -/
theorem castState_apply {m n : Nat} (width : m = n) (state : BitState m)
    (index : Fin n) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

/-- Width transport does not alter Hamming weight. -/
@[simp]
theorem hammingWeight_castState {m n : Nat} (width : m = n) (state : BitState m) :
    hammingWeight (castState width state) = hammingWeight state := by
  cases width
  rfl

/-- Width transport is injective. -/
theorem castState_injective {m n : Nat} (width : m = n) :
    Function.Injective (castState width) := by
  cases width
  exact Function.injective_id

/-- There are exactly `2 ^ n` width-`n` Boolean states. -/
@[simp]
theorem card_bitState (n : Nat) : Fintype.card (BitState n) = 2 ^ n := by
  rw [Fintype.card_pi_const]
  rfl

/--
An exhaustive clean-scratch realization layout.

`balanced` accounts for every non-scratch wire. Scratch has the same explicit
width and value at both boundaries and is prefixed by `packInput` and
`packOutput`; it therefore cannot hide argument information.
-/
structure Layout where
  sourceWidth : Nat
  scratchWidth : Nat
  argumentWidth : Nat
  resultWidth : Nat
  garbageWidth : Nat
  balanced : sourceWidth + argumentWidth = resultWidth + garbageWidth

namespace Layout

/-- Total width of the balanced circuit implementing this layout. -/
abbrev width (layout : Layout) : Nat :=
  layout.scratchWidth + (layout.sourceWidth + layout.argumentWidth)

/-- Pack the complete canonical input boundary `(scratch, source, argument)`. -/
def packInput (layout : Layout) (scratch : BitState layout.scratchWidth)
    (source : BitState layout.sourceWidth) (argument : BitState layout.argumentWidth) :
    BitState layout.width :=
  BitState.append scratch (BitState.append source argument)

/-- Pack the complete canonical output boundary `(scratch, result, garbage)`. -/
def packOutput (layout : Layout) (scratch : BitState layout.scratchWidth)
    (result : BitState layout.resultWidth) (garbage : BitState layout.garbageWidth) :
    BitState layout.width :=
  castState (congrArg (fun width => layout.scratchWidth + width) layout.balanced).symm
    (BitState.append scratch (BitState.append result garbage))

/-- With scratch and source fixed, input packing is injective in the argument. -/
theorem packInput_argument_injective (layout : Layout)
    (scratch : BitState layout.scratchWidth) (source : BitState layout.sourceWidth) :
    Function.Injective (layout.packInput scratch source) := by
  intro left right equality
  have outer := congrArg
    (BitState.split layout.scratchWidth
      (layout.sourceWidth + layout.argumentWidth)) equality
  have body : BitState.append source left = BitState.append source right := by
    simpa [packInput] using congrArg Prod.snd outer
  have inner := congrArg (BitState.split layout.sourceWidth layout.argumentWidth) body
  simpa using congrArg Prod.snd inner

/-- With scratch fixed, output packing loses neither result nor garbage. -/
theorem packOutput_resultGarbage_injective (layout : Layout)
    (scratch : BitState layout.scratchWidth) :
    Function.Injective
      (fun output : BitState layout.resultWidth × BitState layout.garbageWidth =>
        layout.packOutput scratch output.1 output.2) := by
  intro left right equality
  unfold packOutput at equality
  apply castState_injective at equality
  have outer := congrArg
    (BitState.split layout.scratchWidth
      (layout.resultWidth + layout.garbageWidth)) equality
  have body : BitState.append left.1 left.2 = BitState.append right.1 right.2 := by
    simpa using congrArg Prod.snd outer
  have inner := congrArg (BitState.split layout.resultWidth layout.garbageWidth) body
  simpa using inner

/-- Hamming weight of a packed input is the sum of all three named blocks. -/
@[simp]
theorem hammingWeight_packInput (layout : Layout)
    (scratch : BitState layout.scratchWidth) (source : BitState layout.sourceWidth)
    (argument : BitState layout.argumentWidth) :
    hammingWeight (layout.packInput scratch source argument) =
      hammingWeight scratch + (hammingWeight source + hammingWeight argument) := by
  rw [packInput, hammingWeight_append, hammingWeight_append]

/-- Hamming weight of a packed output is the sum of all three named blocks. -/
@[simp]
theorem hammingWeight_packOutput (layout : Layout)
    (scratch : BitState layout.scratchWidth) (result : BitState layout.resultWidth)
    (garbage : BitState layout.garbageWidth) :
    hammingWeight (layout.packOutput scratch result garbage) =
      hammingWeight scratch + (hammingWeight result + hammingWeight garbage) := by
  rw [packOutput, hammingWeight_castState, hammingWeight_append, hammingWeight_append]

end Layout

/-- A state-valued function is argument-independent when all arguments give the same state. -/
def ArgumentIndependent {m n : Nat} (function : BitState m → BitState n) : Prop :=
  ∀ left right, function left = function right

/-- Arguments in one fiber of an ordinary target function. -/
abbrev Fiber {m n : Nat} (target : BitState m → BitState n) (result : BitState n) :=
  {argument // target argument = result}

/--
`circuit` realizes `target` on the initialized source/scratch slice when its
entire output is exactly the returned scratch, selected result, and stated
garbage. No output is projected away or existentially chosen.
-/
def Realizes (layout : Layout) (circuit : Circuit layout.width)
    (scratch : BitState layout.scratchWidth) (source : BitState layout.sourceWidth)
    (target : BitState layout.argumentWidth → BitState layout.resultWidth)
    (garbage : BitState layout.argumentWidth → BitState layout.garbageWidth) : Prop :=
  ∀ argument,
    Circuit.eval circuit (layout.packInput scratch source argument) =
      layout.packOutput scratch (target argument) (garbage argument)

namespace Realizes

/-- A realization's complete `(result, garbage)` output is injective in its argument. -/
theorem targetGarbage_injective {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage) :
    Function.Injective (fun argument => (target argument, garbage argument)) := by
  intro left right outputEquality
  have targetEquality := congrArg Prod.fst outputEquality
  have garbageEquality := congrArg Prod.snd outputEquality
  change target left = target right at targetEquality
  change garbage left = garbage right at garbageEquality
  apply layout.packInput_argument_injective scratch source
  apply (Circuit.eval_isReversible circuit).1
  rw [realizes left, realizes right]
  rw [targetEquality, garbageEquality]

/-- Garbage must distinguish any two arguments on which the target collides. -/
theorem garbage_separates_collisions {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    {left right : BitState layout.argumentWidth} (sameTarget : target left = target right)
    (sameGarbage : garbage left = garbage right) : left = right :=
  realizes.targetGarbage_injective (Prod.ext sameTarget sameGarbage)

/-- Within each target fiber, the explicit garbage map is injective. -/
theorem garbage_injectiveOn_fiber {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (result : BitState layout.resultWidth) :
    Function.Injective (fun argument : Fiber target result => garbage argument.1) := by
  intro left right sameGarbage
  apply Subtype.ext
  apply realizes.garbage_separates_collisions
  · exact left.2.trans right.2.symm
  · exact sameGarbage

/-- Every target fiber fits into the `2 ^ garbageWidth` available garbage states. -/
theorem fiber_card_le {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (result : BitState layout.resultWidth) :
    Fintype.card (Fiber target result) ≤ 2 ^ layout.garbageWidth := by
  rw [← card_bitState]
  exact Fintype.card_le_of_injective _ (realizes.garbage_injectiveOn_fiber result)

/-- Total argument capacity cannot exceed the combined result/garbage capacity. -/
theorem card_argument_le_resultGarbage {layout : Layout}
    {circuit : Circuit layout.width} {scratch : BitState layout.scratchWidth}
    {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage) :
    2 ^ layout.argumentWidth ≤ 2 ^ layout.resultWidth * 2 ^ layout.garbageWidth := by
  simpa using Fintype.card_le_of_injective
    (fun argument => (target argument, garbage argument)) realizes.targetGarbage_injective

/-- If result equality determines garbage equality, the ordinary target is injective. -/
theorem target_injective_of_resultDeterminesGarbage {layout : Layout}
    {circuit : Circuit layout.width} {scratch : BitState layout.scratchWidth}
    {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (determines : ∀ left right, target left = target right → garbage left = garbage right) :
    Function.Injective target := by
  intro left right sameTarget
  exact realizes.garbage_separates_collisions sameTarget (determines left right sameTarget)

/-- In particular, argument-independent garbage forces the target to be injective. -/
theorem target_injective_of_argumentIndependentGarbage {layout : Layout}
    {circuit : Circuit layout.width} {scratch : BitState layout.scratchWidth}
    {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (independent : ArgumentIndependent garbage) : Function.Injective target :=
  realizes.target_injective_of_resultDeterminesGarbage
    (fun left right _ => independent left right)

/-- With zero garbage wires, every realized target is injective. -/
theorem target_injective_of_noGarbage {layout : Layout}
    (noGarbage : layout.garbageWidth = 0) {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage) :
    Function.Injective target := by
  apply realizes.target_injective_of_argumentIndependentGarbage
  intro left right
  funext i
  exact Fin.elim0 (Fin.cast noGarbage i)

/--
Static conservation gives the exact source/argument versus result/garbage
weight budget. The explicitly restored scratch weight cancels from both sides.
-/
theorem weight_balance {layout : Layout} {circuit : Circuit layout.width}
    {scratch : BitState layout.scratchWidth} {source : BitState layout.sourceWidth}
    {target : BitState layout.argumentWidth → BitState layout.resultWidth}
    {garbage : BitState layout.argumentWidth → BitState layout.garbageWidth}
    (realizes : Realizes layout circuit scratch source target garbage)
    (argument : BitState layout.argumentWidth) :
    hammingWeight source + hammingWeight argument =
      hammingWeight (target argument) + hammingWeight (garbage argument) := by
  have preserved := Circuit.eval_weightPreserving circuit
    (layout.packInput scratch source argument)
  rw [realizes argument, layout.hammingWeight_packOutput,
    layout.hammingWeight_packInput] at preserved
  exact (Nat.add_left_cancel preserved).symm

end Realizes

end ConservativeLogic.Realization
