import ConservativeLogic.API

/-!
# Stage 6 finite simulation audit

This diagnostic module checks the closed finite source grammar, explicit
source/garbage resource recurrences, complete structural compilation, exact
Fredkin counts, qualified zero-unit-wire timing, and the complete Figure 7
boundary. It is intentionally not re-exported by the public API.
-/

namespace ConservativeLogic.Audit.Simulation

open ConservativeLogic.Simulation

private def noBits : BitState 0 := fun index => Fin.elim0 index

private def oneBit (value : Bool) : BitState 1 := fun _ => value

private def twoBits (left right : Bool) : BitState 2 :=
  BitState.append (oneBit left) (oneBit right)

private def threeBits (first second third : Bool) : BitState 3 :=
  BitState.append (twoBits first second) (oneBit third)

private def fourBits (first second third fourth : Bool) : BitState 4 :=
  BitState.append (twoBits first second) (twoBits third fourth)

private def fiveBits (first second third fourth fifth : Bool) : BitState 5 :=
  BitState.append (threeBits first second third) (twoBits fourth fifth)

private def sevenBits (first second third fourth fifth sixth seventh : Bool) : BitState 7 :=
  BitState.append (threeBits first second third) (fourBits fourth fifth sixth seventh)

/-! ## Guarded source-language failures -/

/- Tensor has disjoint input blocks; it cannot implicitly feed one input to both branches. -/
#guard_msgs (drop info) in
#check_failure show SourceCircuit 1 2 from
  SourceCircuit.tensor (SourceCircuit.identity 1) (SourceCircuit.identity 1)

/- FAN-OUT's two outputs cannot be sent directly into a one-input gate by serial composition. -/
#guard_msgs (drop info) in
#check_failure SourceCircuit.seq SourceCircuit.fanout SourceCircuit.notGate

private def nonBijectiveReindex : Fin 2 → Fin 2 := fun _ => 0

/- Structural rewiring requires an equivalence, not an arbitrary index map. -/
#guard_msgs (drop info) in
#check_failure SourceCircuit.permute nonBijectiveReindex

private def arbitrarySemanticFunction : BitState 1 → BitState 1 := id

/- An ordinary Boolean function is not a source term. -/
#guard_msgs (drop info) in
#check_failure show SourceCircuit 1 1 from arbitrarySemanticFunction

private def argumentDependentConstant : BitState 1 → BitState 1 := id

/- Constants contain a fixed state, not an argument-dependent state function. -/
#guard_msgs (drop info) in
#check_failure SourceCircuit.constant argumentDependentConstant

/- The finite feed-forward grammar has no delay, state, feedback, or trace nodes. -/
#guard_msgs (drop info) in
#check_failure SourceCircuit.delay

#guard_msgs (drop info) in
#check_failure SourceCircuit.state

#guard_msgs (drop info) in
#check_failure SourceCircuit.feedback

#guard_msgs (drop info) in
#check_failure SourceCircuit.trace

/-! ## Zero-width semantics -/

example : SourceCircuit.eval (SourceCircuit.identity 0) noBits = noBits := by
  funext index
  exact Fin.elim0 index

example :
    SourceCircuit.eval (SourceCircuit.constant noBits : SourceCircuit 0 0) noBits = noBits := by
  funext index
  exact Fin.elim0 index

example : SourceCircuit.eval (SourceCircuit.discard 0) noBits = noBits := by
  funext index
  exact Fin.elim0 index

example :
    SourceCircuit.eval
        (SourceCircuit.seq (SourceCircuit.constant noBits) (SourceCircuit.identity 0)) noBits =
      noBits := by
  funext index
  exact Fin.elim0 index

example (input : BitState 1) :
    SourceCircuit.eval
        (SourceCircuit.tensor (SourceCircuit.identity 0) SourceCircuit.notGate)
        (BitState.append noBits input) = oneBit (!input 0) := by
  funext index
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  rfl

/-! ## Primitive semantics -/

example : SourceCircuit.eval SourceCircuit.andGate (twoBits false false) = oneBit false := by
  decide

example : SourceCircuit.eval SourceCircuit.andGate (twoBits false true) = oneBit false := by
  decide

example : SourceCircuit.eval SourceCircuit.andGate (twoBits true false) = oneBit false := by
  decide

example : SourceCircuit.eval SourceCircuit.andGate (twoBits true true) = oneBit true := by
  decide

example : SourceCircuit.eval SourceCircuit.orGate (twoBits false false) = oneBit false := by
  decide

example : SourceCircuit.eval SourceCircuit.orGate (twoBits false true) = oneBit true := by
  decide

example : SourceCircuit.eval SourceCircuit.orGate (twoBits true false) = oneBit true := by
  decide

example : SourceCircuit.eval SourceCircuit.orGate (twoBits true true) = oneBit true := by
  decide

example : SourceCircuit.eval SourceCircuit.notGate (oneBit false) = oneBit true := by
  decide

example : SourceCircuit.eval SourceCircuit.notGate (oneBit true) = oneBit false := by
  decide

example : SourceCircuit.eval SourceCircuit.fanout (oneBit false) = twoBits false false := by
  decide

example : SourceCircuit.eval SourceCircuit.fanout (oneBit true) = twoBits true true := by
  decide

example (input : BitState 2) :
    SourceCircuit.eval SourceCircuit.andGate input =
      Realization.Primitive.andTarget input := by
  rfl

example (input : BitState 2) :
    SourceCircuit.eval SourceCircuit.orGate input =
      Realization.Primitive.orTarget input := by
  rfl

example (input : BitState 1) :
    SourceCircuit.eval SourceCircuit.notGate input =
      Realization.Primitive.notTarget input := by
  rfl

example (input : BitState 1) :
    SourceCircuit.eval SourceCircuit.fanout input =
      Realization.Primitive.fanoutTarget input := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro tail
    refine Fin.cases ?_ ?_ tail
    · rfl
    · intro impossible
      exact Fin.elim0 impossible

/-! ## Explicit FAN-OUT, serial direction, tensor order, and active rewiring -/

private def fanoutThenAnd : SourceCircuit 1 1 :=
  SourceCircuit.seq SourceCircuit.fanout SourceCircuit.andGate

example (input : BitState 1) :
    SourceCircuit.eval fanoutThenAnd input = input := by
  funext index
  have index_eq : index = 0 := Fin.eq_zero index
  subst index
  simp [fanoutThenAnd, SourceCircuit.eval]

private def andBesideNot : SourceCircuit 3 2 :=
  SourceCircuit.tensor SourceCircuit.andGate SourceCircuit.notGate

example (a b c : Bool) :
    SourceCircuit.eval andBesideNot (threeBits a b c) = twoBits (a && b) (!c) := by
  cases a <;> cases b <;> cases c <;> decide

private def cycleThree : WirePerm 3 :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

example :
    SourceCircuit.eval (SourceCircuit.permute cycleThree) (threeBits true false false) =
      threeBits false false true := by
  decide

/-! ## Exact resource recurrences and block order -/

example : SourceCircuit.sourceWidth (SourceCircuit.identity 0) = 0 := rfl

example : SourceCircuit.garbageWidth (SourceCircuit.identity 0) = 0 := rfl

example : SourceCircuit.logicGateCount (SourceCircuit.identity 0) = 0 := rfl

example :
    SourceCircuit.sourceWidth (SourceCircuit.constant (threeBits true false true)) = 3 := rfl

example :
    SourceCircuit.sourceState (SourceCircuit.constant (threeBits true false true)) =
      threeBits true false true := rfl

example : SourceCircuit.garbageWidth (SourceCircuit.discard 3) = 3 := rfl

example (input : BitState 3) : SourceCircuit.garbage (SourceCircuit.discard 3) input = input :=
  rfl

example : SourceCircuit.sourceWidth SourceCircuit.andGate = 1 := rfl
example : SourceCircuit.garbageWidth SourceCircuit.andGate = 2 := rfl
example : SourceCircuit.sourceWidth SourceCircuit.orGate = 1 := rfl
example : SourceCircuit.garbageWidth SourceCircuit.orGate = 2 := rfl
example : SourceCircuit.sourceWidth SourceCircuit.notGate = 2 := rfl
example : SourceCircuit.garbageWidth SourceCircuit.notGate = 2 := rfl
example : SourceCircuit.sourceWidth SourceCircuit.fanout = 2 := rfl
example : SourceCircuit.garbageWidth SourceCircuit.fanout = 1 := rfl

example : SourceCircuit.sourceWidth fanoutThenAnd = 3 := rfl
example : SourceCircuit.garbageWidth fanoutThenAnd = 3 := rfl
example : SourceCircuit.logicGateCount fanoutThenAnd = 2 := rfl

/- Serial source order is downstream before upstream. -/
example : SourceCircuit.sourceState fanoutThenAnd = threeBits false false true := by
  decide

/- Serial garbage order is downstream garbage before retained upstream garbage. -/
example : SourceCircuit.garbage fanoutThenAnd (oneBit false) =
    threeBits false false true := by
  decide

example : SourceCircuit.garbage fanoutThenAnd (oneBit true) =
    threeBits true false false := by
  decide

example : SourceCircuit.sourceWidth andBesideNot = 3 := rfl
example : SourceCircuit.garbageWidth andBesideNot = 4 := rfl
example : SourceCircuit.logicGateCount andBesideNot = 2 := rfl

/- Tensor source and garbage blocks remain left-before-right. -/
example : SourceCircuit.sourceState andBesideNot = threeBits false false true := by
  decide

example : SourceCircuit.garbage andBesideNot (threeBits true true false) =
    fourBits true false false false := by
  decide

example : SourceCircuit.garbage andBesideNot (threeBits false true true) =
    fourBits false true true true := by
  decide

private def constantThenDiscard : SourceCircuit 0 0 :=
  SourceCircuit.seq
    (SourceCircuit.constant (twoBits true false))
    (SourceCircuit.discard 2)

/- A constant/discard pair still exposes both initialized inputs and final garbage. -/
example : SourceCircuit.sourceWidth constantThenDiscard = 2 := rfl
example : SourceCircuit.garbageWidth constantThenDiscard = 2 := rfl
example : SourceCircuit.logicGateCount constantThenDiscard = 0 := rfl
example : SourceCircuit.sourceState constantThenDiscard = twoBits true false := by decide
example : SourceCircuit.garbage constantThenDiscard noBits = twoBits true false := by decide

private def nestedSerial : SourceCircuit 1 1 :=
  SourceCircuit.seq
    (SourceCircuit.seq SourceCircuit.fanout
      (SourceCircuit.tensor SourceCircuit.notGate SourceCircuit.notGate))
    SourceCircuit.andGate

example : SourceCircuit.sourceWidth nestedSerial = 7 := rfl
example : SourceCircuit.garbageWidth nestedSerial = 7 := rfl
example : SourceCircuit.logicGateCount nestedSerial = 4 := rfl
example : SourceCircuit.sourceState nestedSerial =
    sevenBits false false true false true false true := by decide

private def nestedTensor : SourceCircuit 4 4 :=
  SourceCircuit.tensor
    (SourceCircuit.tensor (SourceCircuit.identity 0) SourceCircuit.andGate)
    (SourceCircuit.tensor SourceCircuit.notGate SourceCircuit.fanout)

example : SourceCircuit.sourceWidth nestedTensor = 5 := rfl
example : SourceCircuit.garbageWidth nestedTensor = 5 := rfl
example : SourceCircuit.logicGateCount nestedTensor = 3 := rfl
example : SourceCircuit.sourceState nestedTensor =
    fiveBits false false true false true := by decide

example : (SourceCircuit.simulationLayout constantThenDiscard).scratchWidth = 0 := rfl
example : (SourceCircuit.simulationLayout constantThenDiscard).argumentWidth = 0 := rfl
example : (SourceCircuit.simulationLayout constantThenDiscard).resultWidth = 0 := rfl
example : (SourceCircuit.simulationLayout constantThenDiscard).sourceWidth = 2 := rfl
example : (SourceCircuit.simulationLayout constantThenDiscard).garbageWidth = 2 := rfl

/- The general middle-block route sends `[A,B,C,D]` to `[A,C,B,D]`. -/
example :
    WirePerm.onState (middleSwapWiring 1 1 1 1) (fourBits true false false true) =
      fourBits true false false true := by
  decide

example :
    WirePerm.onState (middleSwapWiring 1 1 1 1) (fourBits true false true false) =
      fourBits true true false false := by
  decide

/-! ## Compiler realization, exact count, and qualified timing -/

/- The unequal-width source FAN-OUT compiles at its complete width three, not width one. -/
#guard_msgs (drop info) in
#check_failure show Circuit 1 from SourceCircuit.compile SourceCircuit.fanout

/- The compiler accepts source syntax, never an arbitrary semantic function. -/
#guard_msgs (drop info) in
#check_failure SourceCircuit.compile arbitrarySemanticFunction

example :
    Realization.Realizes (SourceCircuit.simulationLayout fanoutThenAnd)
      (SourceCircuit.compile fanoutThenAnd) noBits
      (SourceCircuit.sourceState fanoutThenAnd)
      (SourceCircuit.eval fanoutThenAnd)
      (SourceCircuit.garbage fanoutThenAnd) :=
  SourceCircuit.compile_realizes fanoutThenAnd

example : Circuit.fredkinCount (SourceCircuit.compile (SourceCircuit.identity 0)) = 0 :=
  SourceCircuit.compile_fredkinCount (SourceCircuit.identity 0)

example : Circuit.fredkinCount (SourceCircuit.compile SourceCircuit.andGate) = 1 :=
  SourceCircuit.compile_fredkinCount SourceCircuit.andGate

example : Circuit.fredkinCount (SourceCircuit.compile SourceCircuit.fanout) = 1 :=
  SourceCircuit.compile_fredkinCount SourceCircuit.fanout

example : Circuit.fredkinCount (SourceCircuit.compile fanoutThenAnd) = 2 :=
  SourceCircuit.compile_fredkinCount fanoutThenAnd

example : Circuit.fredkinCount (SourceCircuit.compile andBesideNot) = 2 :=
  SourceCircuit.compile_fredkinCount andBesideNot

example : Circuit.fredkinCount (SourceCircuit.compile constantThenDiscard) = 0 :=
  SourceCircuit.compile_fredkinCount constantThenDiscard

example : Circuit.fredkinCount (SourceCircuit.compile nestedSerial) = 4 :=
  SourceCircuit.compile_fredkinCount nestedSerial

example : Circuit.fredkinCount (SourceCircuit.compile nestedTensor) = 3 :=
  SourceCircuit.compile_fredkinCount nestedTensor

example : Circuit.HasLatency (SourceCircuit.compile (SourceCircuit.identity 0)) 0 :=
  SourceCircuit.compile_hasLatency_zero (SourceCircuit.identity 0)

example : Circuit.HasLatency (SourceCircuit.compile nestedSerial) 0 :=
  SourceCircuit.compile_hasLatency_zero nestedSerial

/- Complete concrete output catches serial garbage order in the actual target term. -/
example :
    Circuit.eval (SourceCircuit.compile fanoutThenAnd)
        ((SourceCircuit.simulationLayout fanoutThenAnd).packInput noBits
          (threeBits false false true) (oneBit true)) =
      (SourceCircuit.simulationLayout fanoutThenAnd).packOutput noBits
        (oneBit true) (threeBits true false false) := by
  decide

/- Complete concrete output catches tensor result and garbage block order. -/
example :
    Circuit.eval (SourceCircuit.compile andBesideNot)
        ((SourceCircuit.simulationLayout andBesideNot).packInput noBits
          (threeBits false false true) (threeBits true true false)) =
      (SourceCircuit.simulationLayout andBesideNot).packOutput noBits
        (twoBits true true) (fourBits true false false false) := by
  decide

/- Constant introduction followed by discard remains an explicit source-to-garbage identity. -/
example :
    Circuit.eval (SourceCircuit.compile constantThenDiscard)
        ((SourceCircuit.simulationLayout constantThenDiscard).packInput noBits
          (twoBits true false) noBits) =
      (SourceCircuit.simulationLayout constantThenDiscard).packOutput noBits
        noBits (twoBits true false) := by
  decide

/-! ## Complete Figure 7 reconstruction -/

open ConservativeLogic.Simulation.Demultiplexer

example : demuxLayout.sourceWidth = 3 := rfl
example : demuxLayout.scratchWidth = 0 := rfl
example : demuxLayout.argumentWidth = 3 := rfl
example : demuxLayout.resultWidth = 4 := rfl
example : demuxLayout.garbageWidth = 2 := rfl
example : demuxSource = threeBits false false false := by decide

private def demuxPackedInput (a0 a1 x : Bool) : BitState 6 :=
  demuxLayout.packInput noBits demuxSource (threeBits a0 a1 x)

private def demuxPackedOutput (y0 y1 y2 y3 a1 a0 : Bool) : BitState 6 :=
  demuxLayout.packOutput noBits (fourBits y0 y1 y2 y3) (twoBits a1 a0)

/- All eight argument rows include the four results and both address-echo sinks. -/
example : Circuit.eval demuxCircuit (demuxPackedInput false false false) =
    demuxPackedOutput false false false false false false := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput false false true) =
    demuxPackedOutput true false false false false false := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput false true false) =
    demuxPackedOutput false false false false true false := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput false true true) =
    demuxPackedOutput false false true false true false := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput true false false) =
    demuxPackedOutput false false false false false true := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput true false true) =
    demuxPackedOutput false true false false false true := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput true true false) =
    demuxPackedOutput false false false false true true := by decide

example : Circuit.eval demuxCircuit (demuxPackedInput true true true) =
    demuxPackedOutput false false false true true true := by decide

example : Circuit.fredkinCount demuxCircuit = 3 := demux_fredkinCount

example : unitWireCount demuxCircuit = 7 := demuxCircuit_unitWireCount

example (input : Fin 3) (output : Fin 4) :
    Circuit.PathDelay demuxCircuit (argumentPort input) (resultPort output) 2 :=
  argument_to_result_path input output

example : Circuit.PathDelay demuxCircuit (2 : Fin 6) (0 : Fin 6) 0 :=
  zero_source_to_y0_path

example : ¬ Circuit.MeetsPaperCombinationalTiming demuxCircuit :=
  demuxCircuit_not_meetsPaperCombinationalTiming

/-! ## Public surfaces and axiom footprints -/

#check SourceCircuit
#check SourceCircuit.identity
#check SourceCircuit.permute
#check SourceCircuit.constant
#check SourceCircuit.discard
#check SourceCircuit.andGate
#check SourceCircuit.orGate
#check SourceCircuit.notGate
#check SourceCircuit.fanout
#check SourceCircuit.seq
#check SourceCircuit.tensor
#check SourceCircuit.eval
#check SourceCircuit.logicGateCount
#check SourceCircuit.sourceWidth
#check SourceCircuit.garbageWidth
#check SourceCircuit.sourceState
#check SourceCircuit.garbage
#check SourceCircuit.simulationLayout
#check SourceCircuit.source_garbage_balance
#check castCircuit
#check eval_castCircuit
#check middleSwapWiring
#check middleSwapWiring_on_append
#check SourceCircuit.compile
#check SourceCircuit.compile_realizes
#check Circuit.fredkinCount
#check SourceCircuit.compile_fredkinCount
#check SourceCircuit.compile_hasLatency_zero
#check demuxCircuit
#check demuxLayout
#check demuxSource
#check demuxTarget
#check demuxGarbage
#check demux_complete
#check demux_realizes
#check demux_fredkinCount
#check unitWireCount
#check demuxCircuit_unitWireCount
#check argumentPort
#check resultPort
#check argument_to_result_path
#check zero_source_to_y0_path
#check demuxCircuit_not_meetsPaperCombinationalTiming

#print SourceCircuit
#print SourceCircuit.compile

#print axioms SourceCircuit.eval
#print axioms SourceCircuit.logicGateCount
#print axioms SourceCircuit.source_garbage_balance
#print axioms eval_castCircuit
#print axioms middleSwapWiring_on_append
#print axioms SourceCircuit.compile_realizes
#print axioms SourceCircuit.compile_fredkinCount
#print axioms SourceCircuit.compile_hasLatency_zero
#print axioms demux_complete
#print axioms demux_realizes
#print axioms demux_fredkinCount
#print axioms demuxCircuit_unitWireCount
#print axioms argument_to_result_path
#print axioms zero_source_to_y0_path
#print axioms demuxCircuit_not_meetsPaperCombinationalTiming

end ConservativeLogic.Audit.Simulation
