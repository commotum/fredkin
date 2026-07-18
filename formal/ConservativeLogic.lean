import ConservativeLogic.API

/-!
# Conservative Logic

Public root for the verified finite conservative-logic library.

The current API provides finite Boolean states, Hamming weight, reversible and
conservative maps, wire permutations, the unit-wire value/delay distinction,
the paper-convention Fredkin gate, and checked static independence and
XOR-nonlinearity witnesses. It additionally provides a balanced feed-forward
circuit grammar, static conservative evaluation, and path-latency predicates.
It also provides explicit full-state realization interfaces and the paper's
four one-Fredkin source/sink examples, including constrained FAN-OUT with its
initialized source and complement garbage. It additionally exports an explicit
unequal-arity feed-forward source language with visible constants, discard,
and FAN-OUT, and a structural compiler whose complete source, garbage, zero
scratch, Fredkin count, and static realization are proved recursively. This is
a finite acyclic theorem using explicit structural wire reindexing, not an
arbitrary-function completeness or sequential-network result. The Figure 7
leaf checks its complete six-wire initialized slice and its narrower timing
facts. It also exports the structural feed-forward circuit inverse, complete
static inverse semantics, semantic cancellation in both directions, exact
reversed-path timing, and preservation of uniform-latency certificates.
Cancellation is not syntactic zero-delay identity: round-trip latencies add.
It also exports the explicit result-register spy bank and complete
compute-copy-uncompute construction.  From a supplied full-state realization,
the exact original scratch/source/argument register is restored and the
separate initialized register becomes `(target, bitwiseNot target)`.  This is a
static finite theorem with exact Fredkin accounting and a zero-latency-only
timing corollary.  The public root now also exports finite Hamming-layer
completion, Figure 25's noncanonical semantic extension, and a fixed-basis
theorem: every finite conservative permutation has a paper-Fredkin circuit
with explicit structural reindexing and an exactly returned clean ancillary
prefix.  The witness records its concrete finite width and exact Boolean
initialization, which need not be all zero, excludes unit wires syntactically,
and has zero path latency.
A proved odd width-four conservative transposition rules out a no-ancilla
interpretation.  No all-zero-scratch conversion, global linear scratch bound,
delay padding, graph/feedback inversion, oriented time-reversal semantics,
traces, sequential execution, physical routing, or thermodynamic conclusion
is claimed.
-/

namespace ConservativeLogic

end ConservativeLogic
