import ConservativeLogic.Sequential

/-!
# Adversarial audit of discrete sequential semantics

This diagnostic leaf checks the Stage 10 state-first tick convention at the
degenerate widths, deterministic trace uniqueness and causality, open-system
flux rather than memory-only conservation, explicit one-tick delay, and
register-separated feedback.  It also checks every reconstructed Figure 8 row
and keeps Figure 9's conventional recurrence outside the conservative type.
The initialized source slice and printed recurrence of the conservative
Figure 11 network are checked separately, including all three external outputs.

The same-time equations below are deliberately propositions, not constructors:
`x = !x` has no Boolean solution while `x = x` has multiple solutions.  The
contrast with a total delayed NOT machine prevents an accidental fixed-point
semantics from entering the executable API.
-/

namespace ConservativeLogic.Audit.Sequential

open ConservativeLogic
open ConservativeLogic.Sequential

private def noBits : BitState 0 := fun index => Fin.elim0 index

private def bit (value : Bool) : BitState 1 := fun _ => value

/-! ## Zero-width machine boundaries -/

private def machine00 : Machine 0 0 0 where
  tick state _ := (state, noBits)

private def machine01 : Machine 0 1 1 where
  tick state input := (state, input)

private def machine10 : Machine 1 0 0 where
  tick state _ := (state, noBits)

example : machine00.tick noBits noBits = (noBits, noBits) := rfl

example : machine01.tick noBits (bit true) = (noBits, bit true) := rfl

example : machine10.tick (bit true) noBits = (bit true, noBits) := rfl

private def conservative00 : ConservativeMachine 0 0 :=
  ⟨Conservative.identity 0⟩

private def conservative01 : ConservativeMachine 0 1 :=
  ⟨Conservative.identity 1⟩

private def conservative10 : ConservativeMachine 1 0 :=
  ⟨Conservative.identity 1⟩

example : conservative00.machine.tick noBits noBits = (noBits, noBits) := by
  decide

example : conservative01.machine.tick noBits (bit true) =
    (noBits, bit true) := by
  decide

example : conservative10.machine.tick (bit true) noBits =
    (bit true, noBits) := by
  decide

example (memory : BitState 0) (input : BitState 0) :
    hammingWeight (conservative00.machine.tick memory input).1 +
        hammingWeight (conservative00.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input :=
  conservative00.tick_weight_balance memory input

example (memory : BitState 0) (input : BitState 1) :
    hammingWeight (conservative01.machine.tick memory input).1 +
        hammingWeight (conservative01.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input :=
  conservative01.tick_weight_balance memory input

example (memory : BitState 1) (input : BitState 0) :
    hammingWeight (conservative10.machine.tick memory input).1 +
        hammingWeight (conservative10.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input :=
  conservative10.tick_weight_balance memory input

/-! ## Trace existence, uniqueness, initialization, and causality -/

example (initial : BitState 1) (input : Signal 1)
    (candidate : Run DelayCell.network.machine)
    (valid : DelayCell.network.machine.IsTrace initial input candidate) :
    candidate = DelayCell.network.machine.run initial input :=
  DelayCell.network.machine.trace_unique initial input candidate valid

example (initial : BitState 1) (input : Signal 1) :
    ∃! candidate : Run DelayCell.network.machine,
      DelayCell.network.machine.IsTrace initial input candidate :=
  DelayCell.network.machine.existsUnique_trace initial input

example (initial : BitState 1) (left right : Signal 1) (time : Nat)
    (agree : Signal.AgreeBefore time left right) :
    (DelayCell.network.machine.run initial left).state time =
      (DelayCell.network.machine.run initial right).state time :=
  DelayCell.network.machine.run_state_eq_of_input_eq_before
    initial left right time agree

example (initial : BitState 1) (left right : Signal 1) (time : Nat)
    (agree : Signal.AgreeThrough time left right) :
    (DelayCell.network.machine.run initial left).output time =
      (DelayCell.network.machine.run initial right).output time :=
  DelayCell.network.machine.run_output_eq_of_input_eq_through
    initial left right time agree

private def futureVariant (future : Bool) : Signal 1 :=
  fun time => bit (if time < 2 then false else future)

example :
    (DelayCell.network.machine.run (bit false) (futureVariant false)).state 2 =
      (DelayCell.network.machine.run (bit false) (futureVariant true)).state 2 := by
  apply DelayCell.network.machine.run_state_eq_of_input_eq_before
  intro time before
  simp [futureVariant, before]

example :
    (DelayCell.network.machine.run (bit false) (futureVariant false)).output 0 0 ≠
      (DelayCell.network.machine.run (bit true) (futureVariant false)).output 0 0 := by
  rw [DelayCell.output_zero, DelayCell.output_zero]
  decide

/-! ## Explicit one-tick delay and the complete-boundary flux law -/

example (initial : BitState 1) (input : Signal 1) :
    (DelayCell.network.machine.run initial input).output 0 = initial :=
  DelayCell.output_zero initial input

example (initial : BitState 1) (input : Signal 1) (time : Nat) :
    (DelayCell.network.machine.run initial input).output (time + 1) = input time :=
  DelayCell.output_succ initial input time

example (memory input : BitState 1) :
    hammingWeight (DelayCell.network.machine.tick memory input).1 +
        hammingWeight (DelayCell.network.machine.tick memory input).2 =
      hammingWeight memory + hammingWeight input :=
  DelayCell.network.tick_weight_balance memory input

/-- A conservative open tick may exchange weight with its external port. -/
theorem delay_memory_weight_changes :
    hammingWeight (DelayCell.network.machine.tick (bit false) (bit true)).1 ≠
      hammingWeight (bit false) := by
  rw [DelayCell.tick]
  decide

private def delayFixedFalseNext (memory : BitState 1) : BitState 1 :=
  (DelayCell.network.machine.tick memory (bit false)).1

/-- Fixing the input and discarding the output destroys the tick's injectivity. -/
theorem delay_fixed_input_state_not_injective :
    ¬ Function.Injective delayFixedFalseNext := by
  intro injective
  apply (by decide : bit false ≠ bit true)
  apply injective
  change
    (DelayCell.network.machine.tick (bit false) (bit false)).1 =
      (DelayCell.network.machine.tick (bit true) (bit false)).1
  rw [DelayCell.tick, DelayCell.tick]

example : ¬ Circuit.HasLatency (.unitWire : Circuit 1) 0 :=
  DelayCell.unitWire_not_instantaneous

/-! ## Same-time loops are not executable feedback -/

/-- The instantaneous Boolean equation `x = !x` has no solution. -/
theorem instantaneous_not_no_solution : ¬ ∃ x : Bool, x = !x := by
  decide

/-- The instantaneous equation `x = x` has at least two distinct solutions. -/
theorem instantaneous_identity_multiple_solutions :
    ∃ x y : Bool, x ≠ y ∧ x = x ∧ y = y := by
  exact ⟨false, true, by decide, rfl, rfl⟩

private def noInput : Signal 0 := fun _ => noBits

/-- A delayed NOT is a total transition because the prior bit is explicit state. -/
def delayedNot : Machine 1 0 1 where
  tick prior _ := (bit (!(prior 0)), prior)

@[simp]
theorem delayedNot_tick (prior : BitState 1) :
    delayedNot.tick prior noBits = (bit (!(prior 0)), prior) := rfl

theorem delayedNot_output_zero (initial : Bool) :
    (delayedNot.run (bit initial) noInput).output 0 0 = initial := by
  rfl

theorem delayedNot_output_succ (initial : Bool) (time : Nat) :
    (delayedNot.run (bit initial) noInput).output (time + 1) 0 =
      !((delayedNot.run (bit initial) noInput).output time 0) := by
  change (delayedNot.run (bit initial) noInput).state (time + 1) 0 =
    !((delayedNot.run (bit initial) noInput).state time 0)
  rfl

example (initial : Bool) :
    ∃! candidate : Run delayedNot,
      delayedNot.IsTrace (bit initial) noInput candidate :=
  delayedNot.existsUnique_trace (bit initial) noInput

/-! ## Register-separated closure and finite retrodiction -/

example : DelayCell.network.closedOrbit (bit false) (bit true) 0 =
    BitState.append (bit false) (bit true) := by
  rfl

example : DelayCell.network.closedOrbit (bit false) (bit true) 1 =
    BitState.append (bit true) (bit false) := by
  decide

example : DelayCell.network.closedOrbit (bit false) (bit true) 2 =
    BitState.append (bit false) (bit true) := by
  decide

example : DelayCell.network.closedOrbit (bit false) (bit true) 0 ≠
    DelayCell.network.closedOrbit (bit false) (bit true) 1 := by
  decide

example (initialMemory initialLoop : BitState 1) (time : Nat) :
    hammingWeight (DelayCell.network.closedOrbit initialMemory initialLoop time) =
      hammingWeight initialMemory + hammingWeight initialLoop :=
  DelayCell.network.closedOrbit_weight initialMemory initialLoop time

example (time : Nat) (state : BitState 2) :
    (DelayCell.network.closedIterateEquiv time).symm
        ((DelayCell.network.closeFeedback.toEquiv ^[time]) state) = state :=
  DelayCell.network.closedIterate_inverse_cancel time state

private def delayInputs : List (BitState 1) :=
  [bit true, bit false, bit true]

private def delayOutputs : List (BitState 1) :=
  [bit false, bit true, bit false]

example : DelayCell.network.executeList (bit false) delayInputs =
    (bit true, delayOutputs) := by
  decide

example : DelayCell.network.retrodictList (bit true) delayOutputs =
    (bit false, delayInputs) := by
  decide

example (initial : BitState 1) (inputs : List (BitState 1)) :
    let execution := DelayCell.network.executeList initial inputs
    DelayCell.network.retrodictList execution.1 execution.2 = (initial, inputs) :=
  DelayCell.network.retrodictList_executeList initial inputs

/-! ## Figure 8 complete transition and trace -/

example : Figure8.network.machine.tick (Figure8.bit false)
    (Figure8.pair false false) =
      (Figure8.bit false, Figure8.pair false false) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit false)
    (Figure8.pair false true) =
      (Figure8.bit true, Figure8.pair false false) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit false)
    (Figure8.pair true false) =
      (Figure8.bit false, Figure8.pair false true) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit false)
    (Figure8.pair true true) =
      (Figure8.bit true, Figure8.pair false true) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit true)
    (Figure8.pair false false) =
      (Figure8.bit false, Figure8.pair true false) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit true)
    (Figure8.pair false true) =
      (Figure8.bit false, Figure8.pair true true) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit true)
    (Figure8.pair true false) =
      (Figure8.bit true, Figure8.pair true false) := by
  decide

example : Figure8.network.machine.tick (Figure8.bit true)
    (Figure8.pair true true) =
      (Figure8.bit true, Figure8.pair true true) := by
  decide

example (q : Bool) :
    Figure8.network.machine.tick (Figure8.bit q) (Figure8.pair true false) =
      (Figure8.bit q, Figure8.pair q (!q)) :=
  Figure8.tick_hold q

example (q : Bool) :
    Figure8.network.machine.tick (Figure8.bit q) (Figure8.pair true true) =
      (Figure8.bit true, Figure8.pair q true) :=
  Figure8.tick_set q

example (q : Bool) :
    Figure8.network.machine.tick (Figure8.bit q) (Figure8.pair false false) =
      (Figure8.bit false, Figure8.pair q false) :=
  Figure8.tick_reset q

example (q : Bool) :
    Figure8.network.machine.tick (Figure8.bit q) (Figure8.pair false true) =
      (Figure8.bit (!q), Figure8.pair q q) :=
  Figure8.tick_toggle q

example (initial : Bool) (kbar j : Nat → Bool) :
    (Figure8.run initial kbar j).output 0 0 = initial :=
  Figure8.visibleQ_zero initial kbar j

example (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (Figure8.run initial kbar j).output time 1 =
      Figure8.garbage ((Figure8.run initial kbar j).state time 0)
        (kbar time) (j time) :=
  Figure8.visibleGarbage initial kbar j time

example (initial : Bool) (time : Nat) :
    (Figure8.run initial (fun _ => false) (fun _ => true)).output
        (time + 1) 0 =
      !((Figure8.run initial (fun _ => false) (fun _ => true)).output time 0) :=
  Figure8.toggle_visible_succ initial time

/-! ## Figure 9 recurrence and its complete nonconservative boundary -/

example (initial : BitState 1) (input : Signal 1) (time : Nat) :
    (SerialAdder.machine.run initial input).output (time + 1) 0 =
      Bool.xor (input time 0)
        ((SerialAdder.machine.run initial input).output time 0) :=
  SerialAdder.paper_recurrence initial input time

example :
    hammingWeight
          (SerialAdder.machine.tick (SerialAdder.bit true)
            (SerialAdder.bit false)).1 +
        hammingWeight
          (SerialAdder.machine.tick (SerialAdder.bit true)
            (SerialAdder.bit false)).2 ≠
      hammingWeight (SerialAdder.bit true) +
        hammingWeight (SerialAdder.bit false) :=
  SerialAdder.concrete_weight_balance_failure

example : Function.Bijective SerialAdder.completeTick :=
  SerialAdder.completeTick_bijective

example : ¬ ∃ conservative : ConservativeMachine 1 1,
    conservative.machine = SerialAdder.machine :=
  SerialAdder.no_conservative_machine

/-! ## Figure 11 initialized conservative recurrence -/

example (delayedX y : Bool) :
    Figure11.initializedMemory delayedX y =
      Figure11.triple (!delayedX) delayedX y := by
  rfl

example (delayedX y x : Bool) :
    Figure11.network.machine.tick (Figure11.initializedMemory delayedX y)
        (Figure11.sourceInput x) =
      (Figure11.initializedMemory x (Figure11.nextY delayedX y),
        Figure11.externalOutput x delayedX y) :=
  Figure11.tick_initialized delayedX y x

example (x : Nat → Bool) (time : Nat) :
    Figure11.sourceSignal x time = Figure11.triple (x time) false true := by
  rfl

example (x delayedX y : Bool) :
    Figure11.externalOutput x delayedX y =
      Figure11.triple x y (!(Figure11.nextY delayedX y)) := by
  rfl

example (initialDelayedX initialY : Bool) (x : Nat → Bool) (time : Nat) :
    (Figure11.run initialDelayedX initialY x).output time 0 = x time :=
  Figure11.fanoutGarbage initialDelayedX initialY x time

example (initialDelayedX initialY : Bool) (x : Nat → Bool) (time : Nat) :
    (Figure11.run initialDelayedX initialY x).output time 2 =
      !(Figure11.nextY (Figure11.delayedX initialDelayedX x time)
        (Figure11.yTrace initialDelayedX initialY x time)) :=
  Figure11.xorGarbage initialDelayedX initialY x time

example (initialDelayedX initialY : Bool) (x : Nat → Bool) (time : Nat) :
    (Figure11.run initialDelayedX initialY x).output (time + 2) 1 =
      Bool.xor
        ((Figure11.run initialDelayedX initialY x).output (time + 1) 1)
        (x time) :=
  Figure11.paper_recurrence initialDelayedX initialY x time

/-! ## Opt-in surface and axiom audit -/

#check Signal
#check Machine
#check Run
#check Machine.IsTrace
#check Machine.trace_unique
#check Machine.existsUnique_trace
#check Machine.run_state_eq_of_input_eq_before
#check Machine.run_output_eq_of_input_eq_through
#check ConservativeMachine
#check ConservativeMachine.tick_weight_balance
#check ConservativeMachine.run_prefix_weight_balance
#check ConservativeMachine.tickEquiv
#check ConservativeMachine.retrodictList_executeList
#check ConservativeMachine.closeFeedback
#check ConservativeMachine.closeFeedback_step
#check ConservativeMachine.closedOrbit_weight
#check ConservativeMachine.closedIterate_inverse_cancel
#check Network
#check Network.executeList
#check Network.retrodictList
#check DelayCell.output_succ
#check DelayCell.unitWire_not_instantaneous
#check Figure8.tick
#check Figure8.characteristic
#check Figure8.visibleGarbage
#check SerialAdder.paper_recurrence
#check SerialAdder.no_conservative_machine
#check Figure11.tick_initialized
#check Figure11.state_spec
#check Figure11.output_spec
#check Figure11.paper_recurrence

#print axioms Machine.trace_unique
#print axioms Machine.existsUnique_trace
#print axioms Machine.run_state_eq_of_input_eq_before
#print axioms Machine.run_output_eq_of_input_eq_through
#print axioms ConservativeMachine.tick_weight_balance
#print axioms ConservativeMachine.run_prefix_weight_balance
#print axioms ConservativeMachine.retrodictList_executeList
#print axioms ConservativeMachine.closeFeedback_step
#print axioms ConservativeMachine.closedOrbit_weight
#print axioms ConservativeMachine.closedIterate_inverse_cancel
#print axioms DelayCell.output_succ
#print axioms DelayCell.unitWire_not_instantaneous
#print axioms delay_memory_weight_changes
#print axioms delay_fixed_input_state_not_injective
#print axioms instantaneous_not_no_solution
#print axioms instantaneous_identity_multiple_solutions
#print axioms delayedNot_output_succ
#print axioms Figure8.tick
#print axioms Figure8.characteristic
#print axioms Figure8.visibleGarbage
#print axioms SerialAdder.paper_recurrence
#print axioms SerialAdder.no_conservative_machine
#print axioms Figure11.tick_initialized
#print axioms Figure11.state_spec
#print axioms Figure11.output_spec
#print axioms Figure11.paper_recurrence

end ConservativeLogic.Audit.Sequential
