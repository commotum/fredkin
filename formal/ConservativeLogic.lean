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
circuits, garbage recycling, feedback, or sequential execution semantics.
-/

namespace ConservativeLogic

end ConservativeLogic
