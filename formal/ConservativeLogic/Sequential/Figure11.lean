import ConservativeLogic.Sequential.Circuit

/-!
# Figure 11: direct conservative serial addition

The drawing contains two Fredkin gates.  The first consumes the source slice
`(x,0,1)` and produces a copy/complement pair; the second combines the delayed
pair with the feedback bit.  Here the three drawn unit wires are explicit
machine memory, so the within-tick core contains exactly the two instantaneous
Fredkins and structural routing.

The complete state-first boundary is

`(delayedX, delayedNotX, y ; x, 0, 1)`.

On the initialized slice `delayedNotX = !delayedX`, the next memory is
`(x,!x,y xor delayedX)`.  All three external outputs remain visible: the first
gate's `x` garbage, the current `y`, and the complement of the next `y`.
Supplying `(0,1)` is therefore an explicit per-tick source-stream assumption,
not a reusable one-time ancilla claim.
-/

namespace ConservativeLogic.Sequential.Figure11

/-- Canonical ordered three-bit state. -/
def triple (first second third : Bool) : BitState 3 :=
  PaperFredkin.state first second third

@[simp]
theorem triple_first (first second third : Bool) : triple first second third 0 = first := rfl

@[simp]
theorem triple_second (first second third : Bool) : triple first second third 1 = second := rfl

@[simp]
theorem triple_third (first second third : Bool) : triple first second third 2 = third := rfl

private def fin6Perm (forward inverse : Fin 6 → Fin 6)
    (leftInverse : Function.LeftInverse inverse forward)
    (rightInverse : Function.RightInverse inverse forward) : WirePerm 6 :=
  Equiv.mk forward inverse leftInverse rightInverse

/-- Route canonical input into physical gate blocks `(x,1,0 ; y,!dx,dx)`. -/
def inputWiring : WirePerm 6 :=
  fin6Perm ![5, 4, 3, 0, 2, 1] ![3, 5, 4, 2, 1, 0] (by decide) (by decide)

/-- Route physical outputs into `(x,!x,nextY ; x,y,!nextY)`. -/
def outputWiring : WirePerm 6 :=
  fin6Perm ![3, 0, 1, 4, 2, 5] ![1, 2, 4, 0, 3, 5] (by decide) (by decide)

/-- The actual six-wire, two-Fredkin instantaneous core of Figure 11. -/
def core : Circuit 6 :=
  .seq (.permute inputWiring)
    (.seq (.tensor .fredkin .fredkin) (.permute outputWiring))

/-- Figure 11 with three explicit state bits and three balanced external ports. -/
def network : Network 3 3 where
  core := core
  instantaneous := by
    intro input output actual path
    have gates : Circuit.HasLatency (.tensor .fredkin .fredkin) 0 :=
      Circuit.HasLatency.tensor Circuit.hasLatency_fredkin Circuit.hasLatency_fredkin
    have delay : actual = 0 + (0 + 0) :=
      (Circuit.HasLatency.seq (Circuit.hasLatency_permute inputWiring)
        (Circuit.HasLatency.seq gates (Circuit.hasLatency_permute outputWiring))) path
    simpa using delay

/-- The feedback update, written in the paper's `y xor x` order. -/
def nextY (delayedX y : Bool) : Bool := Bool.xor y delayedX

/-- Memory states satisfying the delayed copy/complement initialization. -/
def initializedMemory (delayedX y : Bool) : BitState 3 :=
  triple delayedX (!delayedX) y

/-- Fresh external Figure 11 source slice `(x,0,1)`. -/
def sourceInput (x : Bool) : BitState 3 := triple x false true

/-- Every external output, ordered `(fanout garbage, visible y, xor garbage)`. -/
def externalOutput (x delayedX y : Bool) : BitState 3 :=
  triple x y (!(nextY delayedX y))

/-- Complete initialized-slice transition through both Fredkin gates. -/
theorem tick_initialized (delayedX y x : Bool) :
    network.machine.tick (initializedMemory delayedX y) (sourceInput x) =
      (initializedMemory x (nextY delayedX y), externalOutput x delayedX y) := by
  cases delayedX <;> cases y <;> cases x <;> decide

/-- The required `(x,0,1)` source values supplied at every natural tick. -/
def sourceSignal (x : Nat → Bool) : Signal 3 :=
  fun time => sourceInput (x time)

/-- The first memory coordinate: the explicit one-tick delay of `x`. -/
def delayedX (initialDelayedX : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => initialDelayedX
  | time + 1 => x time

/-- The feedback trajectory, including both state bits required at time zero. -/
def yTrace (initialDelayedX initialY : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => initialY
  | time + 1 =>
      nextY (delayedX initialDelayedX x time)
        (yTrace initialDelayedX initialY x time)

/-- Canonical execution from an initialized complement pair and arbitrary `y(0)`. -/
def run (initialDelayedX initialY : Bool) (x : Nat → Bool) :=
  network.machine.run (initializedMemory initialDelayedX initialY) (sourceSignal x)

/-- All three memory coordinates retain their intended initialized-slice meaning. -/
theorem state_spec (initialDelayedX initialY : Bool) (x : Nat → Bool) (time : Nat) :
    (run initialDelayedX initialY x).state time =
      initializedMemory (delayedX initialDelayedX x time)
        (yTrace initialDelayedX initialY x time) := by
  induction time with
  | zero => rfl
  | succ time inductionHypothesis =>
      have step := network.machine.run_tick
        (initializedMemory initialDelayedX initialY) (sourceSignal x) time
      have stateAt := inductionHypothesis
      change
        (network.machine.run (initializedMemory initialDelayedX initialY)
          (sourceSignal x)).state time =
          initializedMemory (delayedX initialDelayedX x time)
            (yTrace initialDelayedX initialY x time) at stateAt
      rw [stateAt,
        show sourceSignal x time = sourceInput (x time) from rfl,
        tick_initialized] at step
      simpa [run, delayedX, yTrace] using (congrArg Prod.fst step).symm

/-- The three external coordinates are all retained in the trace. -/
theorem output_spec (initialDelayedX initialY : Bool) (x : Nat → Bool)
    (time : Nat) :
    (run initialDelayedX initialY x).output time =
      externalOutput (x time) (delayedX initialDelayedX x time)
        (yTrace initialDelayedX initialY x time) := by
  have step := network.machine.run_tick
    (initializedMemory initialDelayedX initialY) (sourceSignal x) time
  have stateAt := state_spec initialDelayedX initialY x time
  change
    (network.machine.run (initializedMemory initialDelayedX initialY)
      (sourceSignal x)).state time =
      initializedMemory (delayedX initialDelayedX x time)
        (yTrace initialDelayedX initialY x time) at stateAt
  rw [stateAt,
    show sourceSignal x time = sourceInput (x time) from rfl,
    tick_initialized] at step
  simpa [run] using (congrArg Prod.snd step).symm

/-- The middle external coordinate is the current feedback/output bit `y`. -/
theorem visibleY (initialDelayedX initialY : Bool) (x : Nat → Bool)
    (time : Nat) :
    (run initialDelayedX initialY x).output time 1 =
      yTrace initialDelayedX initialY x time := by
  simpa [externalOutput] using
    congrArg (fun value => value 1) (output_spec initialDelayedX initialY x time)

/-- The first external coordinate is the fan-out gate's visible `x` garbage. -/
theorem fanoutGarbage (initialDelayedX initialY : Bool) (x : Nat → Bool)
    (time : Nat) :
    (run initialDelayedX initialY x).output time 0 = x time := by
  simpa [externalOutput] using
    congrArg (fun value => value 0) (output_spec initialDelayedX initialY x time)

/-- The last external coordinate is the complement of the next feedback bit. -/
theorem xorGarbage (initialDelayedX initialY : Bool) (x : Nat → Bool)
    (time : Nat) :
    (run initialDelayedX initialY x).output time 2 =
      !(nextY (delayedX initialDelayedX x time)
        (yTrace initialDelayedX initialY x time)) := by
  simpa [externalOutput] using
    congrArg (fun value => value 2) (output_spec initialDelayedX initialY x time)

/-- Figure 11's printed two-tick-input recurrence. -/
theorem paper_recurrence (initialDelayedX initialY : Bool) (x : Nat → Bool)
    (time : Nat) :
    (run initialDelayedX initialY x).output (time + 2) 1 =
      Bool.xor ((run initialDelayedX initialY x).output (time + 1) 1) (x time) := by
  rw [visibleY, visibleY]
  rfl

end ConservativeLogic.Sequential.Figure11
