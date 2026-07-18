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
import ConservativeLogic.Completeness.Semantic
import ConservativeLogic.Completeness.Fredkin
import ConservativeLogic.Completeness.Johnson
import ConservativeLogic.Completeness.Adjacent
import ConservativeLogic.Completeness.Synthesis
import ConservativeLogic.Completeness.NoAncilla

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
Finally, it exports explicit zero/one result registers, a routed paper-Fredkin
spy bank, result-block copying, and complete compute-copy-uncompute.  The final
initialized-slice theorem restores the exact scratch/source/argument state and
returns the selected result with its complement; separate theorems expose
global reversibility, Hamming-weight preservation, exact Fredkin count, and the
qualified zero-latency case.  The finite completeness layer separately
characterizes conservative maps by their Hamming-layer permutations, supplies
the noncanonical total extension suppressed by Figure 25, and proves that
every finite conservative permutation has a clean realization by the paper
Fredkin gate plus explicit structural reindexing.  Its witness exposes the
selected finite ancillary width, exact, possibly mixed initialization, exact
restoration, a no-unit-wire syntax certificate, and zero latency.  A width-four
odd weight-layer transposition disproves universal same-width/no-ancilla
completeness for this circuit grammar.  No all-zero-scratch conversion,
global linear workspace bound, delay padding, feedback-graph inverse, oriented
wire execution, ticks, traces, sequential simulation, physical routing, or
physical time reversal is claimed.
-/

namespace ConservativeLogic

end ConservativeLogic
