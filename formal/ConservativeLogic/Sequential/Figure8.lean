import ConservativeLogic.Sequential.Circuit

/-!
# Figure 8: the paper's J-Kbar element

This module reconstructs every wire of Figure 8.  The stored bit `q` is the
control of the paper-convention Fredkin gate, while `(Kbar, J)` are its data
inputs.  A structural output swap puts the complete transition in the
state-first order

`(q, Kbar, J) -> (nextQ, Q, garbage)`.

The swap is only zero-delay boundary routing.  The feedback unit wire in the
drawing is represented by the explicit one-bit machine state, not by static
evaluation of `Circuit.unitWire`.
-/

namespace ConservativeLogic.Sequential.Figure8

/-- A canonical one-bit state. -/
def bit (value : Bool) : BitState 1 := fun _ => value

/-- A canonical ordered pair of bits. -/
def pair (first second : Bool) : BitState 2 :=
  BitState.append (bit first) (bit second)

@[simp]
theorem bit_apply (value : Bool) (index : Fin 1) : bit value index = value := rfl

@[simp]
theorem pair_first (first second : Bool) : pair first second 0 = first := rfl

@[simp]
theorem pair_second (first second : Bool) : pair first second 1 = second := rfl

theorem bit_eta (value : BitState 1) : bit (value 0) = value := by
  funext index
  exact (congrArg value (Fin.eq_zero index)).symm

theorem pair_eta (value : BitState 2) : pair (value 0) (value 1) = value := by
  funext index
  refine Fin.cases rfl ?_ index
  intro tail
  refine Fin.cases rfl ?_ tail
  intro impossible
  exact Fin.elim0 impossible

/-- The data output returned through the unit feedback wire. -/
def nextQ (q kbar j : Bool) : Bool :=
  if q = true then kbar else j

/-- The other Fredkin data output, which Figure 8 marks with `?`. -/
def garbage (q kbar j : Bool) : Bool :=
  if q = true then j else kbar

/-- Exchange physical Fredkin outputs `(Q,nextQ,garbage)` into state-first order. -/
def outputSwap : WirePerm 3 := Equiv.swap (0 : Fin 3) 1

/-- The instantaneous within-tick core: one Fredkin and explicit output routing. -/
def core : Circuit 3 :=
  .seq .fredkin (.permute outputSwap)

/-- Figure 8 as a one-bit-memory, two-port conservative network. -/
def network : Network 1 2 where
  core := core
  instantaneous := by
    intro input output actual path
    have delay : actual = 0 + 0 :=
      (Circuit.HasLatency.seq Circuit.hasLatency_fredkin
        (Circuit.hasLatency_permute outputSwap)) path
    simpa using delay

/-- Complete parametric Figure 8 transition, including its visible garbage. -/
theorem tick_packed (q kbar j : Bool) :
    network.machine.tick (bit q) (pair kbar j) =
      (bit (nextQ q kbar j), pair q (garbage q kbar j)) := by
  cases q <;> cases kbar <;> cases j <;> decide

/-- Coordinate form of the complete transition for arbitrary packed states. -/
theorem tick (memory : BitState 1) (input : BitState 2) :
    network.machine.tick memory input =
      (bit (nextQ (memory 0) (input 0) (input 1)),
        pair (memory 0) (garbage (memory 0) (input 0) (input 1))) := by
  calc
    network.machine.tick memory input =
        network.machine.tick (bit (memory 0)) (pair (input 0) (input 1)) := by
      rw [bit_eta, pair_eta]
    _ = _ := tick_packed (memory 0) (input 0) (input 1)

/-- External Figure 8 controls as a width-two input stream `(Kbar,J)`. -/
def inputSignal (kbar j : Nat → Bool) : Signal 2 :=
  fun time => pair (kbar time) (j time)

@[simp]
theorem inputSignal_kbar (kbar j : Nat → Bool) (time : Nat) :
    inputSignal kbar j time 0 = kbar time := rfl

@[simp]
theorem inputSignal_j (kbar j : Nat → Bool) (time : Nat) :
    inputSignal kbar j time 1 = j time := rfl

/-- The canonical run, with the feedback bit's initial value kept explicit. -/
def run (initial : Bool) (kbar j : Nat → Bool) :=
  network.machine.run (bit initial) (inputSignal kbar j)

/-- The stored bit after a tick obeys the J-Kbar characteristic equation. -/
theorem state_succ (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (run initial kbar j).state (time + 1) =
      bit (nextQ ((run initial kbar j).state time 0) (kbar time) (j time)) := by
  have step := network.machine.run_tick (bit initial) (inputSignal kbar j) time
  rw [tick] at step
  simpa [run, inputSignal] using (congrArg Prod.fst step).symm

/-- Both external outputs are exposed: current `Q` and the unused data output. -/
theorem output_spec (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (run initial kbar j).output time =
      pair ((run initial kbar j).state time 0)
        (garbage ((run initial kbar j).state time 0) (kbar time) (j time)) := by
  have step := network.machine.run_tick (bit initial) (inputSignal kbar j) time
  rw [tick] at step
  simpa [run, inputSignal] using (congrArg Prod.snd step).symm

/-- The first external output is the pre-tick stored value `Q`. -/
theorem visibleQ_eq_state (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (run initial kbar j).output time 0 =
      (run initial kbar j).state time 0 := by
  simpa using congrArg (fun value => value 0) (output_spec initial kbar j time)

/-- The second external output is the complete, input-dependent garbage bit. -/
theorem visibleGarbage (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (run initial kbar j).output time 1 =
      garbage ((run initial kbar j).state time 0) (kbar time) (j time) := by
  simpa using congrArg (fun value => value 1) (output_spec initial kbar j time)

/-- Initialization is observable at `Q(0)` and is not inferred from the diagram. -/
@[simp]
theorem visibleQ_zero (initial : Bool) (kbar j : Nat → Bool) :
    (run initial kbar j).output 0 0 = initial := by
  rw [visibleQ_eq_state]
  rfl

/-- Paper characteristic equation in terms of the visible `Q` stream. -/
theorem characteristic (initial : Bool) (kbar j : Nat → Bool) (time : Nat) :
    (run initial kbar j).output (time + 1) 0 =
      nextQ ((run initial kbar j).output time 0) (kbar time) (j time) := by
  calc
    (run initial kbar j).output (time + 1) 0 =
        (run initial kbar j).state (time + 1) 0 :=
      visibleQ_eq_state initial kbar j (time + 1)
    _ = nextQ ((run initial kbar j).state time 0) (kbar time) (j time) := by
      rw [state_succ]
      rfl
    _ = nextQ ((run initial kbar j).output time 0) (kbar time) (j time) := by
      rw [visibleQ_eq_state]

/-! ## The four standard J-Kbar modes -/

theorem tick_hold (q : Bool) :
    network.machine.tick (bit q) (pair true false) =
      (bit q, pair q (!q)) := by
  cases q <;> decide

theorem tick_set (q : Bool) :
    network.machine.tick (bit q) (pair true true) =
      (bit true, pair q true) := by
  cases q <;> decide

theorem tick_reset (q : Bool) :
    network.machine.tick (bit q) (pair false false) =
      (bit false, pair q false) := by
  cases q <;> decide

theorem tick_toggle (q : Bool) :
    network.machine.tick (bit q) (pair false true) =
      (bit (!q), pair q q) := by
  cases q <;> decide

theorem hold_state_succ (initial : Bool) (time : Nat) :
    (run initial (fun _ => true) (fun _ => false)).state (time + 1) =
      (run initial (fun _ => true) (fun _ => false)).state time := by
  rw [state_succ]
  rw [← bit_eta ((run initial (fun _ => true) (fun _ => false)).state time)]
  cases (run initial (fun _ => true) (fun _ => false)).state time 0 <;> rfl

theorem set_state_succ (initial : Bool) (time : Nat) :
    (run initial (fun _ => true) (fun _ => true)).state (time + 1) = bit true := by
  rw [state_succ]
  cases (run initial (fun _ => true) (fun _ => true)).state time 0 <;> rfl

theorem reset_state_succ (initial : Bool) (time : Nat) :
    (run initial (fun _ => false) (fun _ => false)).state (time + 1) = bit false := by
  rw [state_succ]
  cases (run initial (fun _ => false) (fun _ => false)).state time 0 <;> rfl

theorem toggle_state_succ (initial : Bool) (time : Nat) :
    (run initial (fun _ => false) (fun _ => true)).state (time + 1) =
      bit (!((run initial (fun _ => false) (fun _ => true)).state time 0)) := by
  rw [state_succ]
  cases (run initial (fun _ => false) (fun _ => true)).state time 0 <;> rfl

/-- With `(Kbar,J)=(0,1)`, the visible output alternates every tick. -/
theorem toggle_visible_succ (initial : Bool) (time : Nat) :
    (run initial (fun _ => false) (fun _ => true)).output (time + 1) 0 =
      !((run initial (fun _ => false) (fun _ => true)).output time 0) := by
  calc
    (run initial (fun _ => false) (fun _ => true)).output (time + 1) 0 =
        (run initial (fun _ => false) (fun _ => true)).state (time + 1) 0 :=
      visibleQ_eq_state initial (fun _ => false) (fun _ => true) (time + 1)
    _ = !((run initial (fun _ => false) (fun _ => true)).state time 0) := by
      rw [toggle_state_succ]
      rfl
    _ = !((run initial (fun _ => false) (fun _ => true)).output time 0) := by
      rw [visibleQ_eq_state]

end ConservativeLogic.Sequential.Figure8
