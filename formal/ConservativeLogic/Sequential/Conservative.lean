import Mathlib.Logic.Function.Iterate
import ConservativeLogic.Reversible.Core
import ConservativeLogic.Sequential.Core

/-!
# Conservative discrete-time machines

An open conservative machine is a permutation of its complete synchronous
boundary.  The ordered convention is

`memory ++ input ↔ nextMemory ++ output`.

Consequently memory weight alone need not be invariant: the exact law is the
flux balance across both blocks.  Closing the equal-width port means storing
the output in a loop register for the following tick.  It is ordinary finite
iteration of the complete conservative permutation, never a same-time
fixed-point equation.
-/

namespace ConservativeLogic.Sequential

/-- A balanced open machine whose complete tick boundary is conservative. -/
structure ConservativeMachine (memoryWidth portWidth : Nat) where
  transition : Conservative (memoryWidth + portWidth)

namespace ConservativeMachine

/-- Split the complete conservative boundary into next memory and output. -/
def machine {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    Machine memoryWidth portWidth portWidth where
  tick memory input :=
    BitState.split memoryWidth portWidth
      (openMachine.transition (BitState.append memory input))

@[simp]
theorem machine_tick {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    openMachine.machine.tick memory input =
      BitState.split memoryWidth portWidth
        (openMachine.transition (BitState.append memory input)) := rfl

/-- Rejoining next memory and output recovers the complete transition result. -/
theorem tick_full {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    BitState.append (openMachine.machine.tick memory input).1
        (openMachine.machine.tick memory input).2 =
      openMachine.transition (BitState.append memory input) := by
  exact BitState.append_split _

/-- Exact one-tick flux law across memory and the complete balanced port. -/
theorem tick_weight_balance {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    hammingWeight (openMachine.machine.tick memory input).1 +
        hammingWeight (openMachine.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input := by
  change
    hammingWeight
          (BitState.split memoryWidth portWidth
            (openMachine.transition (BitState.append memory input))).1 +
        hammingWeight
          (BitState.split memoryWidth portWidth
            (openMachine.transition (BitState.append memory input))).2 =
      hammingWeight memory + hammingWeight input
  rw [← hammingWeight_append]
  rw [← hammingWeight_append]
  rw [BitState.append_split]
  exact openMachine.transition.weight_preserving _

/-- The joint memory/input to next-memory/output tick is an equivalence. -/
def tickEquiv {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    (BitState memoryWidth × BitState portWidth) ≃
      (BitState memoryWidth × BitState portWidth) :=
  (BitState.appendEquiv memoryWidth portWidth).trans
    (openMachine.transition.toEquiv.trans
      (BitState.appendEquiv memoryWidth portWidth).symm)

@[simp]
theorem tickEquiv_apply {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    openMachine.tickEquiv (memory, input) =
      openMachine.machine.tick memory input := rfl

/-- Retaining next memory and output lets the inverse tick recover both inputs. -/
@[simp]
theorem tickEquiv_symm_apply_tick {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    openMachine.tickEquiv.symm (openMachine.machine.tick memory input) =
      (memory, input) := by
  rw [← openMachine.tickEquiv_apply memory input]
  exact openMachine.tickEquiv.symm_apply_apply (memory, input)

/-- A forward tick cancels an inverse tick on a complete retained boundary. -/
@[simp]
theorem tick_after_inverse {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (nextMemory : BitState memoryWidth) (output : BitState portWidth) :
    openMachine.machine.tick
        (openMachine.tickEquiv.symm (nextMemory, output)).1
        (openMachine.tickEquiv.symm (nextMemory, output)).2 =
      (nextMemory, output) := by
  rw [← openMachine.tickEquiv_apply
    (openMachine.tickEquiv.symm (nextMemory, output)).1
    (openMachine.tickEquiv.symm (nextMemory, output)).2]
  exact openMachine.tickEquiv.apply_symm_apply (nextMemory, output)

/-- Execute a finite chronological input list and retain every output. -/
def executeList {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    BitState memoryWidth → List (BitState portWidth) →
      BitState memoryWidth × List (BitState portWidth)
  | memory, [] => (memory, [])
  | memory, input :: inputs =>
      let step := openMachine.machine.tick memory input
      let tail := openMachine.executeList step.1 inputs
      (tail.1, step.2 :: tail.2)

/--
Recover a finite open execution from terminal memory and chronological outputs.
The recursion reaches the list's end first, so inverse ticks are performed in
reverse chronological order.  The returned inputs are restored in their
original chronological order.
-/
def retrodictList {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    BitState memoryWidth → List (BitState portWidth) →
      BitState memoryWidth × List (BitState portWidth)
  | terminalMemory, [] => (terminalMemory, [])
  | terminalMemory, output :: outputs =>
      let recoveredTail := openMachine.retrodictList terminalMemory outputs
      let previous := openMachine.tickEquiv.symm (recoveredTail.1, output)
      (previous.1, previous.2 :: recoveredTail.2)

/-- Complete outputs and terminal memory determine the whole finite open execution. -/
theorem retrodictList_executeList {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (inputs : List (BitState portWidth)) :
    let execution := openMachine.executeList initialMemory inputs
    openMachine.retrodictList execution.1 execution.2 =
      (initialMemory, inputs) := by
  induction inputs generalizing initialMemory with
  | nil => rfl
  | cons input inputs ih =>
      simp only [executeList]
      rw [ih]
      simp only [retrodictList, tickEquiv_symm_apply_tick]

/--
An explicit reverse-list interface: reverse-ordered outputs and terminal memory
recover the initial memory and the inputs in reverse order.
-/
def retrodictListReverse {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (terminalMemory : BitState memoryWidth)
    (outputsReverse : List (BitState portWidth)) :
    BitState memoryWidth × List (BitState portWidth) :=
  let recovered := openMachine.retrodictList terminalMemory outputsReverse.reverse
  (recovered.1, recovered.2.reverse)

/-- Finite open-trace retrodiction, stated with both boundary lists reversed. -/
theorem retrodictListReverse_executeList {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (inputs : List (BitState portWidth)) :
    let execution := openMachine.executeList initialMemory inputs
    openMachine.retrodictListReverse execution.1 execution.2.reverse =
      (initialMemory, inputs.reverse) := by
  simp only [retrodictListReverse, List.reverse_reverse]
  rw [openMachine.retrodictList_executeList initialMemory inputs]

/-- Delayed closure treats the whole memory-and-loop-register boundary as state. -/
def closeFeedback {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    Conservative (memoryWidth + portWidth) :=
  openMachine.transition

/-- The complete delayed-closure step is reversible. -/
theorem closeFeedback_reversible {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) :
    IsReversible openMachine.closeFeedback :=
  openMachine.closeFeedback.isReversible

/-- The `time`-fold delayed-closure transition as an explicit equivalence. -/
def closedIterateEquiv {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) (time : Nat) :
    Reversible (memoryWidth + portWidth) :=
  openMachine.closeFeedback.toEquiv ^ time

/-- The finite equivalence power acts as ordinary function iteration. -/
theorem closedIterateEquiv_apply {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    openMachine.closedIterateEquiv time state =
      (openMachine.closeFeedback.toEquiv ^[time]) state := by
  simp only [closedIterateEquiv, Equiv.Perm.coe_pow]

/--
Closed execution with an explicit initial loop register.  The former output is
the loop-register value consumed at the following tick.
-/
def closedOrbit {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth) :
    Signal (memoryWidth + portWidth) :=
  fun time => (openMachine.closeFeedback.toEquiv ^[time])
    (BitState.append initialMemory initialLoop)

@[simp]
theorem closedOrbit_zero {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth) :
    openMachine.closedOrbit initialMemory initialLoop 0 =
      BitState.append initialMemory initialLoop := by
  rfl

/-- Each closed tick applies the complete memory-and-loop-register transition. -/
theorem closedOrbit_succ {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    openMachine.closedOrbit initialMemory initialLoop (time + 1) =
      openMachine.closeFeedback
        (openMachine.closedOrbit initialMemory initialLoop time) := by
  simp only [closedOrbit, Function.iterate_succ_apply']

/-- The complete state of a delayed closed orbit has invariant weight at every tick. -/
theorem closedOrbit_weight {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    hammingWeight (openMachine.closedOrbit initialMemory initialLoop time) =
      hammingWeight initialMemory + hammingWeight initialLoop := by
  induction time with
  | zero => simp [closedOrbit]
  | succ time ih =>
      rw [openMachine.closedOrbit_succ initialMemory initialLoop time]
      exact (openMachine.closeFeedback.weight_preserving _).trans ih

/-- Every finite delayed-closure iterate is a bijection of the complete state. -/
theorem closedIterate_reversible {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) (time : Nat) :
    IsReversible (openMachine.closeFeedback.toEquiv ^[time]) :=
  openMachine.closeFeedback.isReversible.iterate time

/-- The explicit inverse of a finite closed iterate cancels that iterate. -/
theorem closedIterate_inverse_cancel {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    (openMachine.closedIterateEquiv time).symm
        ((openMachine.closeFeedback.toEquiv ^[time]) state) = state := by
  rw [← openMachine.closedIterateEquiv_apply time state]
  exact (openMachine.closedIterateEquiv time).symm_apply_apply state

/-- Forward finite closed iteration cancels its explicit inverse. -/
theorem closedIterate_forward_cancel {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    (openMachine.closeFeedback.toEquiv ^[time])
        ((openMachine.closedIterateEquiv time).symm state) = state := by
  rw [← openMachine.closedIterateEquiv_apply time]
  exact (openMachine.closedIterateEquiv time).apply_symm_apply state

/-- Retrodicting a closed orbit at any finite time recovers its explicit start. -/
theorem closedOrbit_inverse_cancel {memoryWidth portWidth : Nat}
    (openMachine : ConservativeMachine memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    (openMachine.closedIterateEquiv time).symm
        (openMachine.closedOrbit initialMemory initialLoop time) =
      BitState.append initialMemory initialLoop := by
  exact openMachine.closedIterate_inverse_cancel time _

end ConservativeMachine

end ConservativeLogic.Sequential
