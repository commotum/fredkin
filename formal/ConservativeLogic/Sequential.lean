import ConservativeLogic.Sequential.Core
import ConservativeLogic.Sequential.Conservative
import ConservativeLogic.Sequential.Circuit
import ConservativeLogic.Sequential.Figure8
import ConservativeLogic.Sequential.SerialAdder

/-!
# Opt-in discrete sequential semantics

This umbrella exports deterministic synchronous machines, explicit initial
states and causal traces, complete-boundary conservative ticks, registered
feedback and closed iteration, the zero-latency circuit bridge, the one-tick
delay cell, and the checked Figure 8 and Figure 9 specifications.

It is intentionally separate from `ConservativeLogic` and
`ConservativeLogic.API`.  Importing the finite combinational library therefore
does not add feedback or trace semantics, and importing this module does not
turn arbitrary positive-delay `Circuit.eval` terms into tick bodies.
-/

namespace ConservativeLogic.Sequential

end ConservativeLogic.Sequential
