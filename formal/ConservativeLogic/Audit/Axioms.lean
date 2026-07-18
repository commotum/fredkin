import ConservativeLogic
import ConservativeLogic.Sequential
import ConservativeLogic.Billiard

/-!
# Aggregate main-result axiom audit

This non-public leaf selects representative stable results from every major
finite, sequential, and sampled-billiard theorem family.  Exhaustive rows,
edge cases, counterexamples, and guarded failures remain in the stage-specific
`ConservativeLogic.Audit.*` modules; they are intentionally not copied here.

The sequential and billiard imports make this an explicit opt-in diagnostic
target.  This file must not be imported by `ConservativeLogic`,
`ConservativeLogic.API`, `ConservativeLogic.Sequential`, or
`ConservativeLogic.Billiard`.
-/

/-! ## Finite foundations and primitive Fredkin semantics -/

#print axioms ConservativeLogic.hammingWeight_append
#print axioms ConservativeLogic.WeightPreserving.zeroCount
#print axioms ConservativeLogic.Conservative.comp
#print axioms ConservativeLogic.Independence.reversible_not_weightPreserving
#print axioms ConservativeLogic.Independence.weightPreserving_not_reversible
#print axioms ConservativeLogic.PaperFredkin.conservative_apply
#print axioms ConservativeLogic.PaperFredkin.map_not_xorLinear

/-! ## Balanced circuits, realization, and finite simulation -/

#print axioms ConservativeLogic.Circuit.eval_weightPreserving
#print axioms ConservativeLogic.Circuit.eval_wireOfLength
#print axioms ConservativeLogic.Circuit.wireOfLength_hasLatency
#print axioms ConservativeLogic.Circuit.HasLatency.compensatedTensorSeq
#print axioms ConservativeLogic.Realization.Realizes.weight_balance
#print axioms ConservativeLogic.Realization.Primitive.fredkin_realizes_fanout
#print axioms ConservativeLogic.Simulation.SourceCircuit.compile_realizes
#print axioms ConservativeLogic.Simulation.SourceCircuit.compile_fredkinCount
#print axioms ConservativeLogic.Simulation.Demultiplexer.demux_realizes
#print axioms
  ConservativeLogic.Simulation.Demultiplexer.demuxCircuit_not_meetsPaperCombinationalTiming

/-! ## Structural inversion and compute-copy-uncompute -/

#print axioms ConservativeLogic.Circuit.inverse_eval
#print axioms ConservativeLogic.Circuit.meetsPaperCombinationalTiming_inverse_iff
#print axioms ConservativeLogic.Ancilla.compute_copy_uncompute_spec
#print axioms ConservativeLogic.Ancilla.computeCopyUncompute_fredkinCount
#print axioms ConservativeLogic.Ancilla.computeCopyUncompute_hasLatency_zero

/-! ## Finite clean completeness and its no-ancilla boundary -/

#print axioms ConservativeLogic.fredkin_complete_conservative
#print axioms ConservativeLogic.figure25_fredkin_complete
#print axioms ConservativeLogic.middleLayerSwap_not_circuit

/-! ## Opt-in registered semantics -/

#print axioms ConservativeLogic.Sequential.Machine.trace_unique
#print axioms ConservativeLogic.Sequential.ConservativeMachine.run_prefix_weight_balance
#print axioms ConservativeLogic.Sequential.ConservativeMachine.retrodictList_executeList
#print axioms ConservativeLogic.Sequential.ConservativeMachine.closedOrbit_weight
#print axioms ConservativeLogic.Sequential.DelayCell.unitWire_not_instantaneous
#print axioms ConservativeLogic.Sequential.Figure8.characteristic
#print axioms ConservativeLogic.Sequential.SerialAdder.no_conservative_machine
#print axioms ConservativeLogic.Sequential.Figure11.paper_recurrence

/-! ## Opt-in constrained billiard abstraction -/

#print axioms ConservativeLogic.Billiard.Interaction.equiv
#print axioms ConservativeLogic.Billiard.Switch.equiv
#print axioms ConservativeLogic.Billiard.Collision.allowedEquiv
#print axioms ConservativeLogic.Billiard.ScatteringLayer.Configuration.step_involutive
#print axioms ConservativeLogic.Billiard.ScatteringLayer.Configuration.totalBallCount_step
#print axioms ConservativeLogic.Billiard.Grid.fourTickDetour_boundaryDirections
#print axioms ConservativeLogic.Billiard.Grid.simultaneous_crossing_conflict
#print axioms ConservativeLogic.Billiard.Grid.oneTickStagger_not_sampleClearance
#print axioms ConservativeLogic.Billiard.Grid.twoTickStagger_sampleClearance
#print axioms ConservativeLogic.Billiard.Figure14.output_refines_collision
#print axioms ConservativeLogic.Billiard.Figure14.exact_latency
#print axioms ConservativeLogic.Billiard.Figure14.sampled_clearance
#print axioms ConservativeLogic.Billiard.Figure14.contact_sample_iff
#print axioms ConservativeLogic.Billiard.Figure14.rightAngleTurn_iff
