# Stage 10: Discrete Sequential Semantics

## Status

In progress on 2026-07-18 from clean synchronized baseline `29723da`.
This report fixes the semantic contract before implementation.  No Stage 11
work is in scope.

## Re-Audited Paper Claims

The authoritative paper text and the original images of Figures 3, 8--11,
and 19 were read together before choosing the formal interface.

- Section 2.5 describes a circuit as a directed gate-and-wire graph.  Unit
  wires are one-step storage elements, all feedback therefore crosses a
  discrete-time delay, and the gates collectively define a transition.  Open
  circuits are stateful transducers with balanced external input/output ports;
  closed circuits have no external source or sink.
- Figure 8 gives only the label `J-Kbar` and a drawing, not equations or an
  initialization.  The diagram is nevertheless reconstructable: stored `q`
  is the Fredkin control, `(Kbar,J)` are the data inputs, the control output is
  visible `Q`, one data output returns through the unit wire as next `q`, and
  the other data output is the visible `?` garbage.  Thus

  `(q,Kbar,J) -> (if q then Kbar else J, q, if q then J else Kbar)`.

  This reading accounts for every wire and preserves the paper's
  zero-controlled Fredkin convention.  Its initialization must remain an
  explicit parameter rather than being inferred from the drawing.
- Figure 9 prints the conventional recurrence
  `y(t) = x(t-1) xor y(t-1)`.  Taken as a one-bit state/input/output transition,
  this conventional recurrence is deterministic and bijective on the complete
  `(state,input)` boundary, but it is not Hamming-weight preserving.  It is a
  source-machine specification, not by itself a conservative implementation.
- Figures 10 and 11 motivate a conservative serial-adder simulation.  Figure
  11 is readable as two Fredkins and three unit-wire state bits and prints
  `y(t) = y(t-1) xor x(t-2)`.  The paper still gives no formal schedule or
  simulation relation for Figure 10's factor-five slowdown and time
  multiplexing claims.
- Section 4's general sequential translation is informal.  Constants and
  garbage used once per combinational invocation become source and drain
  streams in an unbounded execution; a one-time finite ancilla theorem cannot
  silently supply them forever.
- Figure 19 contains feedback, so Stage 7's feed-forward graph reversal theorem
  does not cover it.  Section 7.3's closed-computer and NAND-comparable
  complexity claims also lack the schedule and resource model needed for a
  theorem here.

## Baseline Boundary

At commit `29723da`, `Circuit` is an acyclic serial/tensor/permutation syntax.
`Circuit.eval` is deliberately static: in particular, it evaluates
`Circuit.unitWire` as identity on values.  `PathDelay` counts explicit unit
wires along feed-forward boundary paths but defines no clock, stored value,
trace, or feedback execution.  Consequently an arbitrary `Circuit.eval` may
not be reused as a tick body: doing so would erase the state carried by every
positive-delay unit wire.

The finite public import `ConservativeLogic` must remain independent of the
optional sequential layer.  Sequential declarations will have their own
opt-in umbrella and explicit focused build.

## Corrected Formal Contract

### Deterministic source machines and traces

`Signal w` is a natural-number-indexed stream of `BitState w`.  A
`Machine stateWidth inputWidth outputWidth` has one total deterministic tick.
The time convention is fixed as follows:

- `state t` is the complete stored state immediately before tick `t`;
- `input t` is consumed and `output t` is observed at tick `t`;
- the tick returns `state (t+1)`.

Initialization is always explicit.  Recursive execution supplies a canonical
run; a relational `IsTrace` characterization and uniqueness theorem will show
that the equations determine the whole trace.  Prefix-agreement theorems will
state causality directly: state at time `t` depends only on inputs before `t`,
and output at `t` depends only on inputs through `t`.

### Conservative open machines

A `ConservativeMachine memoryWidth portWidth` is one conservative permutation
on the complete ordered boundary

`memory ++ input <-> nextMemory ++ output`.

The input and output port widths are therefore equal.  Splitting this map gives
a `Machine memoryWidth portWidth portWidth`.  The valid one-tick conservation
law is the flux equation

`weight(nextMemory) + weight(output)
  = weight(memory) + weight(input)`.

Internal memory weight alone need not be invariant.  The full tick is
reversible only when both `nextMemory` and the complete output are retained;
fixing an external input need not leave an injective state update.
Summing the tick law over a finite prefix must telescope to

`weight(finalMemory) + sum(weight(outputs))
  = weight(initialMemory) + sum(weight(inputs))`.

This is the corrected open-system reading of Section 2.5's `N1` discussion.
It must not be weakened to a claim that the state of an open transducer is
independently invariant.

### Accepted feedback and closed execution

Only register-separated feedback is accepted.  Closing a port does not solve a
same-time equation.  Instead, the former output is stored in a loop register
and becomes the former input on the following tick.  Thus delayed closure
reinterprets the whole `memory ++ loopRegister` boundary as the state of a
closed conservative transition.

Closed trajectories are finite iterates of that total equivalence.  Their
complete state has invariant Hamming weight at every natural time, and every
finite iterate is reversible.  These are discrete permutation facts, not
oriented `t -> -t` execution, graph reversal, physical time-reversal symmetry,
or a thermodynamic conclusion.

No instantaneous-loop constructor or fixed-point selection is admitted.
The equations `x = not x` (no Boolean solution) and `x = x` (two solutions)
are regression witnesses showing why such a constructor would not provide a
total deterministic semantics.

### Circuit-backed networks

A `Network memoryWidth portWidth` may use an existing feed-forward `Circuit`
as its within-tick core only with a proof `Circuit.HasLatency core 0`.
Positive-delay syntax is rejected at this boundary.  All stored values are
instead explicit in the machine's memory or loop-register state.

A one-bit delay cell will use an instantaneous structural swap on
`memory ++ input`; its trace theorem will prove output at tick zero is the
explicit initial bit and `output (t+1) = input t`.  This supplies the missing
execution meaning of a one-tick wire without pretending that static
`Circuit.eval .unitWire` remembers a value.

## Paper Examples Selected for Checking

Figure 8 is the primary full conservative paper example.  After an explicit
output-coordinate swap, its canonical complete tick is

```text
000 -> 000    001 -> 100    010 -> 001    011 -> 101
100 -> 010    101 -> 011    110 -> 110    111 -> 111
```

where triples are respectively `(q,Kbar,J)` and
`(nextQ,Q,garbage)`.  The trace API must expose arbitrary initial `q`, visible
`Q(t) = q(t)`, the next-state equation, all eight complete rows, and a toggle
trace for constant `(Kbar,J) = (0,1)`.

Figure 9 will be checked separately as the conventional accumulator recurrence
with explicit initialization.  A concrete failed flux equation will prevent
it from being mislabeled a conservative implementation.  Figure 10's
factor-five/time-multiplexing result and the general Section 4 compiler remain
unresolved unless a schedule, stream-level simulation relation, and resource
measure are actually supplied.

## Planned Module Boundary

```text
Sequential/Core.lean          deterministic machines, runs, causality, delay
Sequential/Conservative.lean  full-boundary conservation and delayed closure
Sequential/Circuit.lean       zero-latency circuit-backed networks
Sequential/Figure8.lean       complete J-Kbar reconstruction and trace
Sequential/SerialAdder.lean   conventional Figure 9 recurrence and boundary
Sequential.lean               opt-in sequential umbrella
Audit/Sequential.lean         non-public edge cases and axiom audit
```

None of these modules will be imported by `ConservativeLogic/API.lean` or the
finite public root.

## Adversarial Matrix

The implementation and audit must cover:

- zero-width combinations `(state,port) = (0,0), (0,1), (1,0)`;
- explicit initialization and distinguishable runs from different initial
  states;
- trace existence, uniqueness, successor equations, and input-prefix
  causality;
- a delay-cell swap whose full tick is conservative/reversible although its
  memory weight changes and its fixed-input state update is noninjective;
- rejection of `Circuit.unitWire` as a zero-latency core;
- delayed NOT feedback as a total oscillator, contrasted with no-solution and
  multiple-solution same-time loop equations;
- delayed closure with a nontrivial cycle, all-iterate total-state weight, and
  inverse cancellation;
- Figure 8's eight complete rows, hold/set/reset/toggle behavior, explicit
  initial state, and visible garbage;
- Figure 9's recurrence together with a concrete conservation failure;
- absence of hidden source streams, garbage drains, same-time fixed-point
  choice, factor-five scheduling, NAND-comparability, graph inversion, or
  physical time-reversal conclusions.

## Verification Results

Pending implementation.  Completion requires focused builds of every
sequential leaf and audit, a default finite build, a post-`lake clean` rebuild
of both the finite root and the opt-in sequential/audit targets, proof-hole and
project-axiom scans, `#print axioms` for the central results, adversarial claim
boundary scans, and `git diff --check`.
