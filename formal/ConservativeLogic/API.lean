import ConservativeLogic.State.Core
import ConservativeLogic.Reversible.Core
import ConservativeLogic.Reversible.Independence
import ConservativeLogic.Gate.UnitWire
import ConservativeLogic.Gate.Fredkin
import ConservativeLogic.Gate.Fredkin.Nonlinear
import ConservativeLogic.Circuit.Syntax
import ConservativeLogic.Circuit.Semantics
import ConservativeLogic.Circuit.Timed

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
does not define ticks, traces, feedback, or sequential execution.
-/

namespace ConservativeLogic

end ConservativeLogic
