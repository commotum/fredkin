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
No graph/feedback inversion or oriented time-reversal semantics is claimed;
garbage recycling, feedback, traces, and sequential execution remain absent.
-/

namespace ConservativeLogic

end ConservativeLogic
