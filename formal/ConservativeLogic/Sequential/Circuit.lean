import ConservativeLogic.Circuit.Semantics
import ConservativeLogic.Circuit.Timed
import ConservativeLogic.Sequential.Conservative

/-!
# Zero-latency circuit-backed sequential networks

This module accepts an existing feed-forward `Circuit` as the body of one
sequential tick only when every grammar-induced boundary path has latency
zero.  Stored values live in the explicit memory block of the sequential
machine; positive-delay circuit syntax is intentionally excluded because
`Circuit.eval` is only a static value semantics.

The ordered complete boundary is

`memory ++ input <-> nextMemory ++ output`.

Closing the external port is the register-separated closure from
`Sequential.Conservative`: the previous output occupies the loop-register
input at the following tick.  No same-time fixed point is selected here.
-/

namespace ConservativeLogic.Sequential

/--
A balanced synchronous network whose within-tick circuit is instantaneous.
The first block is explicit stored memory and the second block is the
equal-width external input/output port.
-/
structure Network (memoryWidth portWidth : Nat) where
  core : Circuit (memoryWidth + portWidth)
  instantaneous : Circuit.HasLatency core 0

namespace Network

/-- The conservative complete-boundary semantics of an instantaneous core. -/
def semantics {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    ConservativeMachine memoryWidth portWidth :=
  ⟨Circuit.eval network.core⟩

/-- Split the complete conservative boundary into state and external port. -/
def machine {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    Machine memoryWidth portWidth portWidth :=
  network.semantics.machine

@[simp]
theorem machine_tick {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    network.machine.tick memory input =
      BitState.split memoryWidth portWidth
        (Circuit.eval network.core (BitState.append memory input)) :=
  rfl

/-- Rejoining next memory and output recovers the complete circuit result. -/
theorem tick_full {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    BitState.append (network.machine.tick memory input).1
        (network.machine.tick memory input).2 =
      Circuit.eval network.core (BitState.append memory input) :=
  network.semantics.tick_full memory input

/-- One tick conserves weight across the complete memory/port boundary. -/
theorem tick_weight_balance {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    hammingWeight (network.machine.tick memory input).1 +
        hammingWeight (network.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input :=
  network.semantics.tick_weight_balance memory input

/-- Finite-prefix flux balance for execution of a circuit-backed network. -/
theorem run_prefix_weight_balance {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (input : Signal portWidth)
    (ticks : Nat) :
    hammingWeight ((network.machine.run initialMemory input).state ticks) +
        Finset.sum (Finset.range ticks) (fun time =>
          hammingWeight ((network.machine.run initialMemory input).output time)) =
      hammingWeight initialMemory +
        Finset.sum (Finset.range ticks) (fun time => hammingWeight (input time)) :=
  network.semantics.run_prefix_weight_balance initialMemory input ticks

/-- Joint memory/input to next-memory/output execution is an equivalence. -/
def tickEquiv {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    (BitState memoryWidth × BitState portWidth) ≃
      (BitState memoryWidth × BitState portWidth) :=
  network.semantics.tickEquiv

@[simp]
theorem tickEquiv_apply {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (memory : BitState memoryWidth) (input : BitState portWidth) :
    network.tickEquiv (memory, input) = network.machine.tick memory input :=
  rfl

/-- Execute a finite chronological input list while retaining every output. -/
def executeList {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    BitState memoryWidth → List (BitState portWidth) →
      BitState memoryWidth × List (BitState portWidth) :=
  network.semantics.executeList

/-- Recover a finite execution from terminal memory and chronological outputs. -/
def retrodictList {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    BitState memoryWidth → List (BitState portWidth) →
      BitState memoryWidth × List (BitState portWidth) :=
  network.semantics.retrodictList

/-- Complete outputs and terminal memory recover a finite network execution. -/
theorem retrodictList_executeList {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (inputs : List (BitState portWidth)) :
    let execution := network.executeList initialMemory inputs
    network.retrodictList execution.1 execution.2 =
      (initialMemory, inputs) :=
  network.semantics.retrodictList_executeList initialMemory inputs

/--
Register-separated closure stores the external output as the next external
input.  The complete closed state is `memory ++ loopRegister`.
-/
def closeFeedback {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    Conservative (memoryWidth + portWidth) :=
  network.semantics.closeFeedback

/-- Splitting one closed step exposes the open tick's next memory and output. -/
@[simp]
theorem closeFeedback_step {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (memory : BitState memoryWidth) (loopRegister : BitState portWidth) :
    BitState.split memoryWidth portWidth
        (network.closeFeedback (BitState.append memory loopRegister)) =
      network.machine.tick memory loopRegister :=
  rfl

/-- The `time`-fold closed transition as an explicit equivalence. -/
def closedIterateEquiv {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) (time : Nat) :
    Reversible (memoryWidth + portWidth) :=
  network.semantics.closedIterateEquiv time

/-- The explicit closed equivalence agrees with ordinary function iteration. -/
theorem closedIterateEquiv_apply {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    network.closedIterateEquiv time state =
      (network.closeFeedback.toEquiv ^[time]) state :=
  network.semantics.closedIterateEquiv_apply time state

/-- The closed trajectory starts from an explicit memory and loop register. -/
def closedOrbit {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth) :
    Signal (memoryWidth + portWidth) :=
  network.semantics.closedOrbit initialMemory initialLoop

@[simp]
theorem closedOrbit_zero {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth) :
    network.closedOrbit initialMemory initialLoop 0 =
      BitState.append initialMemory initialLoop :=
  network.semantics.closedOrbit_zero initialMemory initialLoop

theorem closedOrbit_succ {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    network.closedOrbit initialMemory initialLoop (time + 1) =
      network.closeFeedback (network.closedOrbit initialMemory initialLoop time) :=
  network.semantics.closedOrbit_succ initialMemory initialLoop time

theorem closedOrbit_weight {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    hammingWeight (network.closedOrbit initialMemory initialLoop time) =
      hammingWeight initialMemory + hammingWeight initialLoop :=
  network.semantics.closedOrbit_weight initialMemory initialLoop time

/-- The register-separated closed transition is reversible. -/
theorem closeFeedback_reversible {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) :
    IsReversible network.closeFeedback :=
  network.closeFeedback.isReversible

/-- Every finite register-separated closed iterate is reversible. -/
theorem closedIterate_reversible {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) (time : Nat) :
    IsReversible (network.closeFeedback.toEquiv ^[time]) :=
  network.semantics.closedIterate_reversible time

/-- The explicit inverse of a finite closed iterate recovers its input. -/
theorem closedIterate_inverse_cancel {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    (network.closedIterateEquiv time).symm
        ((network.closeFeedback.toEquiv ^[time]) state) = state :=
  network.semantics.closedIterate_inverse_cancel time state

/-- A finite closed iterate cancels its explicit inverse. -/
theorem closedIterate_forward_cancel {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth) (time : Nat)
    (state : BitState (memoryWidth + portWidth)) :
    (network.closeFeedback.toEquiv ^[time])
        ((network.closedIterateEquiv time).symm state) = state :=
  network.semantics.closedIterate_forward_cancel time state

/-- Retrodicting any finite closed orbit recovers its explicit initial state. -/
theorem closedOrbit_inverse_cancel {memoryWidth portWidth : Nat}
    (network : Network memoryWidth portWidth)
    (initialMemory : BitState memoryWidth) (initialLoop : BitState portWidth)
    (time : Nat) :
    (network.closedIterateEquiv time).symm
        (network.closedOrbit initialMemory initialLoop time) =
      BitState.append initialMemory initialLoop :=
  network.semantics.closedOrbit_inverse_cancel initialMemory initialLoop time

end Network

namespace DelayCell

/-- Structural exchange of the one-bit memory and one-bit input blocks. -/
def wiring : WirePerm 2 := Equiv.swap (0 : Fin 2) (1 : Fin 2)

/--
An executable one-tick delay.  Its core is a zero-latency structural swap;
the delay comes from the explicit memory boundary, not from static evaluation
of `Circuit.unitWire`.
-/
def network : Network 1 1 where
  core := .permute wiring
  instantaneous := Circuit.hasLatency_permute wiring

/-- The complete tick is exactly `(memory,input) -> (input,memory)`. -/
@[simp]
theorem tick (memory input : BitState 1) :
    network.machine.tick memory input = (input, memory) := by
  apply Prod.ext <;> funext index
  · have index_zero : index = 0 := Fin.eq_zero index
    subst index
    change BitState.append memory input
        ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) 0) = input 0
    rw [Equiv.swap_apply_left]
    exact BitState.append_natAdd memory input 0
  · have index_zero : index = 0 := Fin.eq_zero index
    subst index
    change BitState.append memory input
        ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) 1) = memory 0
    rw [Equiv.swap_apply_right]
    exact BitState.append_castAdd memory input 0

/-- At every tick, the visible output is the current stored bit. -/
theorem output_eq_state (initial : BitState 1) (input : Signal 1)
    (time : Nat) :
    (network.machine.run initial input).output time =
      (network.machine.run initial input).state time := by
  have step := network.machine.run_tick initial input time
  rw [tick] at step
  exact (congrArg Prod.snd step).symm

/-- The next stored bit is exactly the input consumed at this tick. -/
theorem state_succ (initial : BitState 1) (input : Signal 1)
    (time : Nat) :
    (network.machine.run initial input).state (time + 1) = input time := by
  have step := network.machine.run_tick initial input time
  rw [tick] at step
  exact (congrArg Prod.fst step).symm

/-- Tick-zero output is the explicitly supplied initial memory bit. -/
@[simp]
theorem output_zero (initial : BitState 1) (input : Signal 1) :
    (network.machine.run initial input).output 0 = initial := by
  rw [output_eq_state]
  exact network.machine.run_state_zero initial input

/-- The output one tick later is the input from the preceding tick. -/
theorem output_succ (initial : BitState 1) (input : Signal 1) (time : Nat) :
    (network.machine.run initial input).output (time + 1) = input time := by
  rw [output_eq_state, state_succ]

/-- The positive-delay unit-wire syntax cannot be used as a network core. -/
theorem unitWire_not_instantaneous :
    ¬ Circuit.HasLatency (.unitWire : Circuit 1) 0 := by
  intro instantaneous
  exact Nat.one_ne_zero
    (instantaneous Circuit.PathDelay.unitWire_one)

end DelayCell

end ConservativeLogic.Sequential
