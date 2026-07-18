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
initialized source and complement garbage. It does not yet expose inverse
circuits or garbage recycling. It additionally exports an explicit
unequal-arity feed-forward source language with visible constants, discard,
and FAN-OUT, and a structural compiler whose complete source, garbage, zero
scratch, Fredkin count, and static realization are proved recursively. This is
a finite acyclic theorem using explicit structural wire reindexing, not an
arbitrary-function completeness or sequential-network result. The Figure 7
leaf checks its complete six-wire initialized slice and its narrower timing
facts. Feedback, traces, and sequential execution semantics remain absent.
-/

namespace ConservativeLogic

end ConservativeLogic
