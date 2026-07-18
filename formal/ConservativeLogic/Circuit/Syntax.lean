import ConservativeLogic.Reversible.Core

/-!
# Balanced feed-forward circuit syntax

`Circuit n` is a corrected feed-forward term language whose one width index is
both its input and output arity. Its constructors compose ports one-to-one:
serial composition requires an identical boundary width, tensor uses disjoint
adjacent blocks, and structural rewiring requires a bijection.

This is not the paper's literal directed-graph model, which also permits
feedback and state. In particular, there is no contraction, weakening,
fan-out, arbitrary semantic-gate, feedback, or unequal-arity constructor.
`permute` is explicit zero-delay *structural port reindexing*; it is not a claim
that a physical routed permutation circuit is freely available or synthesized
from Fredkin gates.
-/

namespace ConservativeLogic

/--
A balanced feed-forward conservative-circuit expression on `n` boundary wires.

The only value-processing gate in this fixed basis is the paper
Fredkin gate. `unitWire` and `identity` remain distinct syntax because the
former carries one unit of path delay while the latter is structural and
instantaneous.
-/
inductive Circuit : Nat → Type where
  /-- Structural identity on `n` ports; assigned zero delay by the path-counting layer. -/
  | identity (n : Nat) : Circuit n
  /-- The paper's one-bit unit wire, carrying one unit of delay. -/
  | unitWire : Circuit 1
  /-- The instantaneous paper-convention Fredkin gate. -/
  | fredkin : Circuit 3
  /-- Explicit bijective structural boundary reindexing. -/
  | permute {n : Nat} (wiring : WirePerm n) : Circuit n
  /-- Serial composition, applying `first` before `second`. -/
  | seq {n : Nat} (first second : Circuit n) : Circuit n
  /-- Parallel composition on ordered, disjoint left and right wire blocks. -/
  | tensor {m n : Nat} (left : Circuit m) (right : Circuit n) : Circuit (m + n)

/-- Transport a circuit along an equality of widths without changing its syntax. -/
def Circuit.cast {leftWidth rightWidth : Nat} (width : leftWidth = rightWidth)
    (circuit : Circuit leftWidth) : Circuit rightWidth :=
  width ▸ circuit

/--
A one-bit wire of any discrete length, built by serially composing exactly that
many unit-wire constructors.  Length zero is the structural identity.
-/
def Circuit.wireOfLength : Nat → Circuit 1
  | 0 => .identity 1
  | length + 1 => .seq (wireOfLength length) .unitWire

end ConservativeLogic
