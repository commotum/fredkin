import ConservativeLogic.Sequential.Conservative

/-!
# Figure 9: the conventional serial accumulator

Figure 9 specifies the ordinary recurrence

`y(t+1) = x(t) xor y(t)`.

The deterministic machine below checks that recurrence, its explicit initial
condition, and its prefix parity.  Its complete boundary tick is bijective but
fails Hamming-weight balance, so it is deliberately *not* presented as a
`ConservativeMachine`.  A conservative gate-level realization needs the
additional source and garbage streams discussed around Figures 10 and 11.
-/

namespace ConservativeLogic.Sequential.SerialAdder

/-- A canonical one-bit state. -/
def bit (value : Bool) : BitState 1 := fun _ => value

@[simp]
theorem bit_apply (value : Bool) (index : Fin 1) : bit value index = value := rfl

theorem bit_eta (value : BitState 1) : bit (value 0) = value := by
  funext index
  exact (congrArg value (Fin.eq_zero index)).symm

/-- Conventional, nonconservative one-bit accumulator transition. -/
def machine : Machine 1 1 1 where
  tick prior input :=
    (bit (Bool.xor (input 0) (prior 0)), prior)

@[simp]
theorem tick_state (prior input : BitState 1) :
    (machine.tick prior input).1 = bit (Bool.xor (input 0) (prior 0)) := rfl

@[simp]
theorem tick_output (prior input : BitState 1) :
    (machine.tick prior input).2 = prior := rfl

/-- The observed output at a tick is the pre-tick accumulator state. -/
theorem output_eq_state (initial : BitState 1) (input : Signal 1) (time : Nat) :
    (machine.run initial input).output time =
      (machine.run initial input).state time := by
  rfl

/-- Figure 9's recurrence, with the paper's one-tick indexing made explicit. -/
theorem paper_recurrence (initial : BitState 1) (input : Signal 1) (time : Nat) :
    (machine.run initial input).output (time + 1) 0 =
      Bool.xor (input time 0) ((machine.run initial input).output time 0) := by
  change (machine.run initial input).state (time + 1) 0 =
    Bool.xor (input time 0) ((machine.run initial input).state time 0)
  rfl

/-- Scalar prefix parity including an explicit time-zero accumulator value. -/
def prefixParity (initial : Bool) (input : Nat → Bool) : Nat → Bool
  | 0 => initial
  | time + 1 => Bool.xor (input time) (prefixParity initial input time)

@[simp]
theorem prefixParity_zero (initial : Bool) (input : Nat → Bool) :
    prefixParity initial input 0 = initial := rfl

@[simp]
theorem prefixParity_succ (initial : Bool) (input : Nat → Bool) (time : Nat) :
    prefixParity initial input (time + 1) =
      Bool.xor (input time) (prefixParity initial input time) := rfl

/-- The complete state trace is exactly the recursively defined prefix parity. -/
theorem state_eq_prefixParity (initial : BitState 1) (input : Signal 1)
    (time : Nat) :
    (machine.run initial input).state time 0 =
      prefixParity (initial 0) (fun tick => input tick 0) time := by
  induction time with
  | zero => rfl
  | succ time inductionHypothesis =>
      change Bool.xor (input time 0)
          ((machine.run initial input).state time 0) = _
      rw [inductionHypothesis]
      rfl

/-- The visible output has the same explicit prefix-parity description. -/
theorem output_eq_prefixParity (initial : BitState 1) (input : Signal 1)
    (time : Nat) :
    (machine.run initial input).output time 0 =
      prefixParity (initial 0) (fun tick => input tick 0) time := by
  rw [output_eq_state]
  exact state_eq_prefixParity initial input time

/-! ## Complete-boundary reversibility without conservation -/

/-- The joint `(prior,input) -> (next,output)` boundary map. -/
def completeTick (value : BitState 1 × BitState 1) : BitState 1 × BitState 1 :=
  machine.tick value.1 value.2

/-- Recover `(prior,input)` from `(next,output)`. -/
def inverseTick (value : BitState 1 × BitState 1) : BitState 1 × BitState 1 :=
  (value.2, bit (Bool.xor (value.1 0) (value.2 0)))

private theorem inverseTick_completeTick (value : BitState 1 × BitState 1) :
    inverseTick (completeTick value) = value := by
  rcases value with ⟨prior, input⟩
  rw [← bit_eta prior, ← bit_eta input]
  cases prior 0 <;> cases input 0 <;> decide

private theorem completeTick_inverseTick (value : BitState 1 × BitState 1) :
    completeTick (inverseTick value) = value := by
  rcases value with ⟨next, output⟩
  rw [← bit_eta next, ← bit_eta output]
  cases next 0 <;> cases output 0 <;> decide

/-- The conventional full tick is bijective when the complete output is retained. -/
def completeTickEquiv :
    (BitState 1 × BitState 1) ≃ (BitState 1 × BitState 1) where
  toFun := completeTick
  invFun := inverseTick
  left_inv := inverseTick_completeTick
  right_inv := completeTick_inverseTick

theorem completeTick_bijective : Function.Bijective completeTick :=
  completeTickEquiv.bijective

/-- A closed row where total output weight is two but total input weight is one. -/
theorem concrete_weight_balance_failure :
    hammingWeight (machine.tick (bit true) (bit false)).1 +
        hammingWeight (machine.tick (bit true) (bit false)).2 ≠
      hammingWeight (bit true) + hammingWeight (bit false) := by
  decide

/-- No conservative machine can have exactly this conventional transition. -/
theorem no_conservative_machine :
    ¬ ∃ conservative : ConservativeMachine 1 1,
      conservative.machine = machine := by
  rintro ⟨conservative, transition_eq⟩
  have balance := conservative.tick_weight_balance (bit true) (bit false)
  rw [transition_eq] at balance
  exact concrete_weight_balance_failure balance

end ConservativeLogic.Sequential.SerialAdder
