import ConservativeLogic.API

/-!
# Stage 7 inverse-circuit audit

This diagnostic module checks that circuit inversion is structural, reverses
serial order and active wire permutations, preserves tensor block order, and
reverses grammar-induced paths without erasing unit-wire delay.  It also keeps
static semantic cancellation separate from syntactic identity and from any
claim about feedback, execution, or physical time reversal.  It is
intentionally not re-exported by the public API.
-/

namespace ConservativeLogic.Audit.Inverse

open ConservativeLogic.Simulation

private def noBits : BitState 0 := fun index => Fin.elim0 index

private def oneBit (value : Bool) : BitState 1 := fun _ => value

private def threeBits (first second third : Bool) : BitState 3 :=
  PaperFredkin.state first second third

/-! ## Guarded inverse-domain failures -/

/- The generally irreversible, unequal-width source FAN-OUT is not a balanced circuit. -/
#guard_msgs (drop info) in
#check_failure Circuit.inverse SourceCircuit.fanout

private def arbitrarySemanticFunction : BitState 1 → BitState 1 := id

/- An arbitrary state function cannot be passed to structural circuit inversion. -/
#guard_msgs (drop info) in
#check_failure Circuit.inverse arbitrarySemanticFunction

/-! ## Constructor reductions and zero width -/

example (width : Nat) :
    Circuit.inverse (Circuit.identity width) = Circuit.identity width :=
  Circuit.inverse_identity width

example : Circuit.inverse Circuit.unitWire = Circuit.unitWire :=
  Circuit.inverse_unitWire

example : Circuit.inverse Circuit.fredkin = Circuit.fredkin :=
  Circuit.inverse_fredkin

example {width : Nat} (wiring : WirePerm width) :
    Circuit.inverse (Circuit.permute wiring) = Circuit.permute wiring.symm :=
  Circuit.inverse_permute wiring

example {width : Nat} (first second : Circuit width) :
    Circuit.inverse (Circuit.seq first second) =
      Circuit.seq (Circuit.inverse second) (Circuit.inverse first) :=
  Circuit.inverse_seq first second

example {leftWidth rightWidth : Nat} (left : Circuit leftWidth)
    (right : Circuit rightWidth) :
    Circuit.inverse (Circuit.tensor left right) =
      Circuit.tensor (Circuit.inverse left) (Circuit.inverse right) :=
  Circuit.inverse_tensor left right

example : Circuit.inverse (Circuit.identity 0) = Circuit.identity 0 := by
  simp

example : Circuit.eval (Circuit.inverse (Circuit.identity 0)) noBits = noBits := by
  funext index
  exact Fin.elim0 index

/- Width-zero latency is vacuous and intentionally not unique. -/
example (latency : Nat) :
    Circuit.HasLatency (Circuit.inverse (Circuit.identity 0)) latency := by
  intro input
  exact Fin.elim0 input

private def emptyWiring : WirePerm 0 := Equiv.refl _

example : Circuit.inverse (Circuit.permute emptyWiring) =
    Circuit.permute emptyWiring.symm := by
  simp

example : Circuit.eval (Circuit.inverse (Circuit.permute emptyWiring)) noBits = noBits := by
  funext index
  exact Fin.elim0 index

private def emptyLeftUnit : Circuit 1 :=
  Circuit.tensor (Circuit.identity 0) Circuit.unitWire

example : Circuit.inverse emptyLeftUnit = emptyLeftUnit := by
  simp [emptyLeftUnit]

example (input : BitState 1) :
    Circuit.eval (Circuit.inverse emptyLeftUnit) input = input := by
  change BitState.append
      (BitState.split 0 1 input).1 (BitState.split 0 1 input).2 = input
  exact BitState.append_split (m := 0) (n := 1) input

example {width : Nat} (circuit : Circuit width) :
    Circuit.inverse (Circuit.inverse circuit) = circuit :=
  Circuit.inverse_inverse circuit

/-! ## Non-involutive active-permutation direction -/

private def cycleThree : WirePerm 3 :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

example : Circuit.eval (Circuit.permute cycleThree)
    (threeBits true false false) = threeBits false false true := by
  decide

/- This differs from the preceding forward action, so a missing `.symm` fails. -/
example : Circuit.eval (Circuit.inverse (Circuit.permute cycleThree))
    (threeBits true false false) = threeBits false true false := by
  decide

example : Circuit.eval (Circuit.inverse (Circuit.permute cycleThree))
    (Circuit.eval (Circuit.permute cycleThree) (threeBits true false false)) =
      threeBits true false false := by
  decide

private theorem cycleThree_forward_path :
    Circuit.PathDelay (Circuit.permute cycleThree) 0 2 0 := by
  change (2 : Fin 3) = cycleThree 0 ∧ (0 : Nat) = 0
  decide

example : Circuit.PathDelay (Circuit.inverse (Circuit.permute cycleThree)) 2 0 0 :=
  Circuit.PathDelay.inverse (Circuit.permute cycleThree)
    cycleThree_forward_path

/- A missing `.symm` would incorrectly retain this forward path direction. -/
example : ¬ Circuit.PathDelay
    (Circuit.inverse (Circuit.permute cycleThree)) 0 2 0 := by
  intro path
  change (2 : Fin 3) = cycleThree.symm 0 ∧ (0 : Nat) = 0 at path
  exact (by decide : (2 : Fin 3) ≠ cycleThree.symm 0) path.1

/-! ## Noncommuting serial reversal and semantic cancellation -/

private def swapControlData₁ : WirePerm 3 := Equiv.swap 0 1

private def orderSensitive : Circuit 3 :=
  Circuit.seq Circuit.fredkin (Circuit.permute swapControlData₁)

example : Circuit.eval orderSensitive (threeBits false false true) =
    threeBits true false false := by
  decide

/- Reusing the original serial order here would produce a different state. -/
example : Circuit.eval (Circuit.inverse orderSensitive) (threeBits true false false) =
    threeBits false false true := by
  decide

example (input : BitState 3) :
    Circuit.eval (Circuit.inverse orderSensitive)
        (Circuit.eval orderSensitive input) = input :=
  Circuit.eval_inverse_eval orderSensitive input

example (input : BitState 3) :
    Circuit.eval orderSensitive
        (Circuit.eval (Circuit.inverse orderSensitive) input) = input :=
  Circuit.eval_eval_inverse orderSensitive input

/-! ## Tensor order and disjointness -/

private def asymmetricTensor : Circuit 4 :=
  Circuit.tensor (Circuit.permute cycleThree) Circuit.unitWire

example : Circuit.eval (Circuit.inverse asymmetricTensor)
    (BitState.append (threeBits false false true) (oneBit true)) =
      BitState.append (threeBits true false false) (oneBit true) := by
  decide

private def equalWidthTensor : Circuit 6 :=
  Circuit.tensor (Circuit.permute cycleThree) Circuit.fredkin

/- Equal block widths ensure that exchanging tensor branches would type-check but fail this row. -/
example : Circuit.eval (Circuit.inverse equalWidthTensor)
    (BitState.append
      (threeBits false false true)
      (threeBits false false true)) =
    BitState.append
      (threeBits true false false)
      (threeBits false true false) := by
  decide

example (leftInput rightInput : BitState 3) :
    Circuit.eval (Circuit.inverse equalWidthTensor)
        (BitState.append leftInput rightInput) =
      BitState.append
        (Circuit.eval (Circuit.inverse (Circuit.permute cycleThree)) leftInput)
        (Circuit.eval (Circuit.inverse Circuit.fredkin) rightInput) := by
  simpa [equalWidthTensor] using
    Circuit.eval_tensor_append
      (Circuit.inverse (Circuit.permute cycleThree))
      (Circuit.inverse Circuit.fredkin) leftInput rightInput

/- Tensor inversion does not create a path between its disjoint blocks. -/
example : ¬ Circuit.PathDelay (Circuit.inverse asymmetricTensor) 0 3 0 := by
  intro path
  change Circuit.PathDelay
    (Circuit.tensor (Circuit.permute cycleThree.symm) Circuit.unitWire) 0 3 0 at path
  rcases path with
    ⟨leftInput, leftOutput, inputLeft, outputLeft, leftPath⟩ |
    ⟨rightInput, rightOutput, inputRight, outputRight, rightPath⟩
  · have impossible := congrArg Fin.val outputLeft
    simp at impossible
    omega
  · have impossible := congrArg Fin.val inputRight
    simp at impossible

/-! ## Primitive inverse value and timing checks -/

example (input : BitState 1) :
    Circuit.eval (Circuit.inverse Circuit.unitWire) input = input := by
  simp

example : Circuit.HasLatency (Circuit.inverse Circuit.unitWire) 1 := by
  exact Circuit.HasLatency.inverse (circuit := Circuit.unitWire)
    Circuit.hasLatency_unitWire_one

example : Circuit.eval (Circuit.inverse Circuit.fredkin)
    (threeBits false false true) = threeBits false true false := by
  decide

example : Circuit.HasLatency (Circuit.inverse Circuit.fredkin) 0 := by
  exact Circuit.HasLatency.inverse (circuit := Circuit.fredkin)
    Circuit.hasLatency_fredkin

/-! ## Exact delayed-path endpoint reversal -/

private def delayedCycle : Circuit 3 :=
  Circuit.seq
    (Circuit.tensor Circuit.unitWire (Circuit.identity 2))
    (Circuit.permute cycleThree)

private theorem delayedCycle_forward :
    Circuit.PathDelay delayedCycle 0 2 1 := by
  change Circuit.PathDelay delayedCycle
    (Fin.castAdd 2 (0 : Fin 1))
    (cycleThree (Fin.castAdd 2 (0 : Fin 1))) (1 + 0)
  exact Circuit.PathDelay.seq
    (Circuit.PathDelay.tensorLeft Circuit.PathDelay.unitWire_one)
    (Circuit.PathDelay.permute cycleThree (Fin.castAdd 2 (0 : Fin 1)))

example : Circuit.PathDelay (Circuit.inverse delayedCycle) 2 0 1 :=
  Circuit.PathDelay.inverse delayedCycle delayedCycle_forward

example :
    Circuit.PathDelay (Circuit.inverse delayedCycle) 2 0 1 ↔
      Circuit.PathDelay delayedCycle 0 2 1 :=
  Circuit.pathDelay_inverse_iff delayedCycle

/-! ## Uniform and nonuniform timing -/

private def compensatedParallel : Circuit 2 :=
  Circuit.seq
    (Circuit.tensor Circuit.unitWire (Circuit.identity 1))
    (Circuit.tensor (Circuit.identity 1) Circuit.unitWire)

private theorem compensatedParallel_hasLatency :
    Circuit.HasLatency compensatedParallel 1 := by
  exact Circuit.HasLatency.compensatedTensorSeq
    Circuit.hasLatency_unitWire_one (Circuit.hasLatency_identity 1)
    (Circuit.hasLatency_identity 1) Circuit.hasLatency_unitWire_one rfl rfl

example : Circuit.HasLatency (Circuit.inverse compensatedParallel) 1 :=
  Circuit.HasLatency.inverse compensatedParallel_hasLatency

example :
    Circuit.MeetsPaperCombinationalTiming (Circuit.inverse compensatedParallel) :=
  Circuit.MeetsPaperCombinationalTiming.inverse
    (Circuit.HasLatency.meetsPaperCombinationalTiming compensatedParallel_hasLatency)

private def unequalParallel : Circuit 2 :=
  Circuit.tensor Circuit.unitWire (Circuit.identity 1)

private theorem unequalParallel_not_meetsPaperCombinationalTiming :
    ¬ Circuit.MeetsPaperCombinationalTiming unequalParallel := by
  rintro ⟨latency, uniform⟩
  have delayedPath : Circuit.PathDelay unequalParallel
      (Fin.castAdd 1 (0 : Fin 1)) (Fin.castAdd 1 (0 : Fin 1)) 1 :=
    Circuit.PathDelay.tensorLeft Circuit.PathDelay.unitWire_one
  have immediatePath : Circuit.PathDelay unequalParallel
      (Fin.natAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1)) 0 :=
    Circuit.PathDelay.tensorRight (Circuit.PathDelay.identity (0 : Fin 1))
  have delayedLatency : 1 = latency := uniform delayedPath
  have immediateLatency : 0 = latency := uniform immediatePath
  exact Nat.zero_ne_one (immediateLatency.trans delayedLatency.symm)

theorem inverse_unequalParallel_not_meetsPaperCombinationalTiming :
    ¬ Circuit.MeetsPaperCombinationalTiming (Circuit.inverse unequalParallel) := by
  intro inverseUniform
  exact unequalParallel_not_meetsPaperCombinationalTiming
    ((Circuit.meetsPaperCombinationalTiming_inverse_iff unequalParallel).mp inverseUniform)

/-! ## Semantic identity is not syntactic or zero-delay identity -/

def unitWireRoundTrip : Circuit 1 :=
  Circuit.seq Circuit.unitWire (Circuit.inverse Circuit.unitWire)

theorem unitWireRoundTrip_eval_identity (input : BitState 1) :
    Circuit.eval unitWireRoundTrip input = input := by
  change Circuit.eval (Circuit.inverse Circuit.unitWire)
      (Circuit.eval Circuit.unitWire input) = input
  exact Circuit.eval_inverse_eval Circuit.unitWire input

theorem unitWireRoundTrip_ne_identity :
    unitWireRoundTrip ≠ Circuit.identity 1 := by
  intro equality
  cases equality

theorem unitWireRoundTrip_hasLatency :
    Circuit.HasLatency unitWireRoundTrip 2 := by
  change Circuit.HasLatency
    (Circuit.seq Circuit.unitWire (Circuit.inverse Circuit.unitWire)) (1 + 1)
  exact Circuit.HasLatency.seq_inverse (circuit := Circuit.unitWire)
    Circuit.hasLatency_unitWire_one

theorem unitWireRoundTrip_not_hasLatency_zero :
    ¬ Circuit.HasLatency unitWireRoundTrip 0 := by
  intro zeroLatency
  have twoStepPath : Circuit.PathDelay unitWireRoundTrip 0 0 2 := by
    change Circuit.PathDelay
      (Circuit.seq Circuit.unitWire Circuit.unitWire) 0 0 (1 + 1)
    exact Circuit.PathDelay.seq
      Circuit.PathDelay.unitWire_one Circuit.PathDelay.unitWire_one
  exact (by decide : (2 : Nat) ≠ 0) (zeroLatency twoStepPath)

/-! ## Public surface and axiom footprints -/

#check Circuit.inverse
#check Circuit.inverse_identity
#check Circuit.inverse_unitWire
#check Circuit.inverse_fredkin
#check Circuit.inverse_permute
#check Circuit.inverse_seq
#check Circuit.inverse_tensor
#check Circuit.inverse_inverse
#check Circuit.inverse_involutive
#check Circuit.inverse_eval
#check Circuit.eval_inverse_eval
#check Circuit.eval_eval_inverse
#check Circuit.PathDelay.inverse
#check Circuit.pathDelay_inverse_iff
#check Circuit.HasLatency.inverse
#check Circuit.hasLatency_inverse_iff
#check Circuit.MeetsPaperCombinationalTiming.inverse
#check Circuit.meetsPaperCombinationalTiming_inverse_iff
#check Circuit.HasLatency.seq_inverse
#check Circuit.HasLatency.inverse_seq
#check Circuit.UniformLatencyCircuit.inverse

#print Circuit
#print Circuit.inverse

#print axioms Circuit.inverse_identity
#print axioms Circuit.inverse_unitWire
#print axioms Circuit.inverse_fredkin
#print axioms Circuit.inverse_permute
#print axioms Circuit.inverse_seq
#print axioms Circuit.inverse_tensor
#print axioms Circuit.inverse_inverse
#print axioms Circuit.inverse_involutive
#print axioms Circuit.inverse_eval
#print axioms Circuit.eval_inverse_eval
#print axioms Circuit.eval_eval_inverse
#print axioms Circuit.PathDelay.inverse
#print axioms Circuit.pathDelay_inverse_iff
#print axioms Circuit.HasLatency.inverse
#print axioms Circuit.hasLatency_inverse_iff
#print axioms Circuit.MeetsPaperCombinationalTiming.inverse
#print axioms Circuit.meetsPaperCombinationalTiming_inverse_iff
#print axioms Circuit.HasLatency.seq_inverse
#print axioms Circuit.HasLatency.inverse_seq
#print axioms Circuit.UniformLatencyCircuit.inverse
#print axioms inverse_unequalParallel_not_meetsPaperCombinationalTiming
#print axioms unitWireRoundTrip_eval_identity
#print axioms unitWireRoundTrip_ne_identity
#print axioms unitWireRoundTrip_hasLatency
#print axioms unitWireRoundTrip_not_hasLatency_zero

end ConservativeLogic.Audit.Inverse
