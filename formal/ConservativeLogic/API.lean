import ConservativeLogic.State.Core
import ConservativeLogic.Reversible.Core
import ConservativeLogic.Reversible.Independence
import ConservativeLogic.Gate.UnitWire
import ConservativeLogic.Gate.Fredkin
import ConservativeLogic.Gate.Fredkin.Nonlinear
import ConservativeLogic.Circuit.Syntax
import ConservativeLogic.Circuit.Semantics
import ConservativeLogic.Circuit.Timed
import ConservativeLogic.Circuit.Inverse
import ConservativeLogic.Realization.Core
import ConservativeLogic.Realization.Primitive
import ConservativeLogic.Simulation.Source
import ConservativeLogic.Simulation.Fredkin
import ConservativeLogic.Simulation.Demultiplexer
import ConservativeLogic.Ancilla.Uncompute

set_option linter.style.header false

/-!
# Public conservative-logic API

This module is the stable public import for the finite-state foundations and
primitive value semantics. It re-exports Boolean states, static reversibility
and conservation predicates, their bundled forms, wire permutations, the
semantic independence witnesses, the unit-wire value/delay distinction, and
the paper-convention Fredkin gate with its selected XOR-nonlinearity result.
It also exports the balanced feed-forward circuit grammar with a fixed
value-processing basis plus explicit structural reindexing, static conservative
evaluation, and uniform-path-latency certificates. The certificate surface
does not define ticks, traces, feedback, or sequential execution. The API also
exports exhaustive source/clean-scratch/argument/result/garbage layouts,
full-state realization constraints, and the exact one-Fredkin AND, OR, NOT,
and constrained FAN-OUT realizations. Finally, it exports an explicitly
generated finite feed-forward source language and a constructive compiler to
Fredkin circuits plus structural reindexing. The compiler has zero scratch,
states its complete fixed source and argument-dependent garbage, and proves
the full initialized-slice equation with exact Fredkin count. The separate
Figure 7 reconstruction includes all three zero sources, address-echo garbage,
seven unit wires, existence and exact delay two for every distinguished
argument/result path, and a proof that the complete boundary does not have one
global latency. The API additionally exports structural inversion of the
balanced feed-forward grammar, equality of inverse evaluation with the inverse
conservative equivalence, exact endpoint-reversing path correspondence,
common-latency preservation, and latency-additive forward/inverse composition.
It does not define a feedback-graph inverse, oriented wire execution, ticks,
traces, sequential simulation, garbage recycling, or physical time reversal.
-/

namespace ConservativeLogic

end ConservativeLogic
