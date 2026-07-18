# Conservative Logic Lean Library — CLLEAN

## Big-Picture Objective

Turn Fredkin and Toffoli's 1982 paper, *Conservative Logic*, into a correct,
reusable Lean 4 library for finite reversible and conservative Boolean
computation. The library must reconstruct and independently verify the paper's
discrete mathematics, correct or qualify ambiguous claims, and keep physical
interpretations outside the theorem surface unless an explicit physical model
has been defined.

The tentative development order is finite Boolean vectors and
Hamming-weight-preserving equivalences; the unit wire and the paper's exact
Fredkin convention; arity-safe circuits with one-to-one wiring; realization
using constants and garbage; inverse circuits and compute-copy-uncompute;
Fredkin universality; and only then sequential or billiard-ball models.

This file is the authoritative strategy, paper map, dependency note, proposed
theorem outline, and correction/audit register. It must be updated from checked
Lean results as the work proceeds.

## Non-Negotiable Constraints and No-Cheating Rules

- Do not treat the paper as a formal specification or import its claims as
  axioms. Reconstruct every theorem with explicit hypotheses.
- Completed modules contain no `sorry`, `admit`, or unexplained
  project-specific `axiom`. Temporary theorem stubs are not completed work.
- Keep reversibility (bijectivity) and conservation (Hamming-weight
  preservation) as distinct predicates and prove each separately.
- Circuit composition is one-to-one: every output occurrence is consumed at
  most once. Fan-out must be an explicit reversible construction with stated
  constant/ancilla preconditions.
- Keep combinational acyclic semantics separate from sequential transition
  semantics and feedback. Equal-path-delay claims must be represented and
  checked, not inferred from a diagram.
- Keep semantic realizability separate from gate count, depth, delay, ancilla,
  constant, scratch, and garbage claims. An existential circuit theorem does
  not imply an efficient synthesis theorem.
- Keep constants, arguments, results, garbage, and scratch space explicitly
  indexed or partitioned. Do not hide ancillas in wiring isomorphisms.
- Keep direct computation distinct from reversible realization through an
  embedding. Projection of a result is not equality of the whole reversible
  map with the target function.
- Use the Fredkin truth table printed in the paper unless a declaration is
  explicitly named as the alternate convention: control `0` swaps the data
  wires and control `1` leaves them in order.
- Never duplicate a wire in Lean by reusing a variable where the circuit model
  requires a physical copy. Prove copy constructions only on their constrained
  interfaces.
- Static inverse correctness must require a structurally reversible circuit
  representation; any claim matching the paper's *combinational inverse* must
  additionally preserve its equal-path timing certificate.
- Physical claims about energy, entropy, heat, dissipation, noise, microscopic
  reversibility, or actual hard-ball mechanics are documentation only unless a
  corresponding formal physical model is introduced.
- Do not silently narrow the original objective. If a claim cannot be proved,
  record a counterexample, missing assumption, or precise open obligation.
- Do not use exhaustive evaluation as the sole proof of a general theorem.
  Finite decision procedures may verify fixed gates and bounded examples.
- Pin Lean and mathlib before substantive code and keep the project build
  reproducible. Do not claim setup validation until `lake build` succeeds.

## Current Facts

### Checked Repository Facts

- The source is available as `fredkin-1982/fredkin-1982.pdf` and the extracted
  `fredkin-1982/fredkin-1982.md`, with 26 extracted figures.
- `fredkin-1982/BUILD-PLAN.md` supplies generic Lean module and verification
  guidance; it is not a proof or paper-specific plan.
- The unrelated placeholder Python project (`pyproject.toml`, `main.py`) remains
  untouched. Stage 1 added the isolated `formal/` Lake project and private
  representation probe. Stage 2 replaced the empty public root with finite
  state, reversible-map, independence-witness, and thin API modules. Stage 3
  added separate unit-wire value/delay declarations, the exact paper Fredkin
  gate, its selected XOR-nonlinearity theorem, and a non-public Fredkin audit.
  `formal/lake-manifest.json` locks mathlib `v4.32.0` to commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Direct invocation under `formal/` selects Lean `v4.32.0` at commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. On 2026-07-17, every stable leaf
  through Stage 5 and the guardrail, finite, Fredkin, circuit, and realization
  audit targets succeeded against the locked dependency tree. The Stage 5
  uncontended clean default build completed all 781 jobs; its post-clean
  realization audit completed all 772 jobs.
- The in-project private probe compile-checks `Fin n → Bool`, filtered
  `Finset.univ` cardinality, `Equiv.Perm` identity/inverse/serial composition,
  serial application order, `Fin.addCases`, and the candidate `Vector` and
  `BitVec` surfaces. Guarded negative checks confirm that root `Vector Bool 3`
  and `BitVec 3` do not supply the required local `Fintype` instances under the
  pinned narrow imports.
- `BitState n := Fin n → Bool` and project-owned `hammingWeight` now form the
  stable state representation. `BitState.append`/`split` are mutually inverse,
  and `hammingWeight_append` proves arbitrary-width block additivity, including
  width zero.
- `IsReversible` and `WeightPreserving` are independent predicates.
  `Reversible` bundles an `Equiv.Perm`; `Conservative` bundles an equivalence
  with a separate preservation proof. Identity, serial composition, inverse,
  and active bijective wire-reindexing closure laws are checked.
- `Independence.flipOne` is reversible but not weight-preserving, while
  `Independence.sortTwo` is weight-preserving but noninjective. The latter is
  explicitly only a semantic endomap; it is not a circuit or fan-out claim.
- `UnitWire.value : Conservative 1` is the identity-on-values map, while
  `UnitWire.delay = 1` is separate metadata measured in the paper's abstract
  discrete time steps. No Stage 3 declaration turns that metadata into a trace,
  path, feedback, oriented-inverse, or time-reversal semantics.
- `PaperFredkin.state` fixes coordinates `(u,x₁,x₂)`, and
  `PaperFredkin.map` implements Table (2)'s zero-controlled swap.
  `PaperFredkin.map_involutive`, `equiv`, `map_isReversible`,
  `map_weightPreserving`, and `conservative` prove its static inverse and
  conservation properties independently. `XorLinear` makes one precise
  coordinatewise-XOR interpretation of linearity, and
  `PaperFredkin.map_not_xorLinear` proves failure by a named concrete
  additivity counterexample.
- Stage 4 began from clean synchronized commit `50c1269`. It adds the exact
  six-constructor balanced grammar `Circuit n`: structural identity, unit wire,
  paper Fredkin, active bijective structural permutation, exact-width serial
  composition, and ordered disjoint tensor. There is no arbitrary semantic
  injection, contraction, weakening, implicit fan-out, feedback, or unequal
  boundary constructor.
- `Circuit.eval : Circuit n → Conservative n` reuses the Stage 3 unit-wire and
  Fredkin bundles. General equations cover all six constructors, including
  arbitrary appended tensor blocks, while `eval_isReversible` and
  `eval_weightPreserving` expose the two semantic properties separately.
- `PathDelay` is a structurally recursive relation on feed-forward terms:
  identity, Fredkin, and structural permutation contribute zero delay; the unit
  wire contributes `UnitWire.delay = 1`; serial paths add; tensor paths remain
  inside their left or right block. `HasLatency` and
  `MeetsPaperCombinationalTiming` express the global common-latency condition.
- `UniformLatencyCircuit n latency` is only a circuit-plus-proof certificate.
  Its serial and equal-latency tensor constructors are complemented by
  `HasLatency.compensatedTensorSeq`, which accepts global compensation such as
  `(unit ⊗ id); (id ⊗ unit)` even though the intermediate tensors are not
  uniform.
- `ConservativeLogic.Audit.Circuit` guards mismatched serial widths and
  nonbijective reindexing, checks zero width, ordering and active permutation
  direction, rejects an unrestricted same-width copy map, distinguishes static
  value equality from delay, and proves both unequal-path rejection and
  compensated-path acceptance. It is not imported by the public root.
- Stage 5 began from clean synchronized commit `16562ab`. `Realization.Layout`
  now names source, returned-clean scratch, argument, result, and garbage
  widths, with canonical boundaries `(scratch,source,argument)` and
  `(scratch,result,garbage)`. Its balance proof accounts for every non-scratch
  wire; `Layout.packInput` and `Layout.packOutput` construct the complete
  boundary states.
- `Realization.Realizes` universally quantifies the argument while keeping
  source and scratch fixed and equates `Circuit.eval` with the entire packed
  output. Its proved consequences include injectivity of `(target,garbage)`,
  collision separation, injectivity and a `2^garbageWidth` bound within each
  target fiber, the total result/garbage capacity bound, target injectivity
  when results determine garbage, and exact scratch-cancelled Hamming-weight
  balance.
- `Realization.Primitive` supplies actual routed `Circuit 3` terms and complete
  equations for AND, OR, NOT, and constrained FAN-OUT. FAN-OUT consumes fixed
  canonical source `(0,1)`, returns selected result `(a,a)`, and exposes
  complement `¬a` as garbage; its full circuit is globally reversible and
  Hamming-weight preserving.
- `ConservativeLogic.Audit.Realization` checks the full signatures and axiom
  footprints, parametric port routing, every primitive row, zero-width and
  arbitrary restored-scratch cases, and negative capacity/conservation
  boundaries. It is not imported by the public root.
- Stage 6 begins from clean synchronized commit `e65f939`. The cached default
  build succeeds with 773 jobs. There is no `Simulation` module, conventional
  source-circuit datatype, structural translation, demultiplexer
  reconstruction, or simulation audit at this baseline.
- Stage 6 is complete at clean synchronized commit `011b189`. The cached
  default build succeeds with 777 jobs. The public root exports the closed
  source grammar, exact-resource Fredkin-plus-reindexing compiler, and complete
  Figure 7 reconstruction; its non-public simulation audit and clean-build
  evidence are recorded in `goal-1/6-SIMULATION.md`.
- No `Circuit/Inverse.lean`, syntactic circuit inverse, inverse-path theorem,
  or `Audit/Inverse.lean` exists at the Stage 7 baseline. `Conservative.inverse`
  and `WirePerm.onState_inverse` already provide the semantic equivalence
  operations needed to state correctness without adding an arbitrary gate.
- Stage 7 is complete from baseline `011b189`. The public root now exports the
  total structural inverse, complete static inverse semantics, exact
  endpoint-reversed path correspondence, common-latency preservation, and
  latency-additive round trips. The uncontended clean default build succeeds
  with 778 jobs; the non-public inverse audit succeeds with 777 jobs, with full
  completion evidence recorded in `goal-1/7-INVERSE.md`.
- Stage 8 begins from clean synchronized commit `ccab07c`. The cached default
  build succeeds with 778 jobs. There is no `Ancilla/Uncompute.lean`,
  `Audit/Uncompute.lean`, multi-bit spy layer, or complete
  compute-copy-uncompute theorem at this baseline.
- Stage 8 now adds `Ancilla.Uncompute` and its API-only non-public audit. The
  public construction uses one explicitly routed paper Fredkin per result bit,
  proves the complete compute-copy-uncompute boundary from a supplied
  `Realizes` witness, restores the exact scratch/source/argument state, exposes
  `(target,bitwiseNot target)`, and proves global reversibility, conservation,
  exact Fredkin count, and the qualified zero-latency case. The audit retains a
  positive-unit-wire counterexample with delay-two and delay-zero paths.

### Checked Paper Facts

- The paper's unit-wire table relates input `xᵗ` to equal-valued output
  `yᵗ⁺¹`; Figure 1 equivalently writes `yᵗ = xᵗ⁻¹`. Its aligned port-value map
  is identity, but the timed primitive has delay one, two forward unit wires
  have delay two, and the paper does not call that timed primitive an
  involution. Its separate `t ↦ -t` inverse claim needs oriented time semantics.
- Its Fredkin table maps `(u, x1, x2)` to `(u, x2, x1)` when `u = 0` and to
  `(u, x1, x2)` when `u = 1`. Thus the printed control convention is
  zero-controlled swapping.
- The paper's Fredkin ports are ordered `(u,x₁,x₂) → (v,y₁,y₂)`, with `v=u`;
  its eight rows are `000→000`, `001→010`, `010→001`, `011→011`,
  `100→100`, `101→101`, `110→110`, and `111→111`. Section 2.5 treats gates as
  instantaneous combinational elements and wires as delay elements.
- Section 2.4 calls Fredkin nonlinear but supplies no algebraic definition.
  Stage 3 therefore labels its coordinatewise-XOR/`F₂` interpretation as a
  precise reconstruction rather than a quoted definition or physical
  conclusion.
- A conservative gate is described as an invertible Boolean function that
  preserves the number of ones. The paper explicitly notes that reversibility
  and conservation are independent.
- P7 motivates at least one unspecified additive conserved quantity; only the
  later Boolean circuit model in §2.5 specializes this to `N₁`, the number of
  one-valued wires. Its `N₀ = N - N₁` is derived and explicitly not independent.
- Footnote 3 defines reversibility as backward determinism/retrodictability and
  explicitly says it does not imply invariance under time reversal. A Lean
  equivalence, an involution, and a time-reversal theorem are therefore distinct
  claims.
- Composition forbids implicit fan-out. Source constants and discarded sink
  outputs are used to realize noninvertible Boolean functions.
- When discussing realizability from a set of conservative primitives, §2.5
  tacitly includes the unit wire and identity gate. Later fixed-basis theorems
  must either retain or explicitly replace that convention.
- The paper's circuit model is time-discrete. Wires carry delay; feedback gives
  sequential behavior. Its definition of a combinational network additionally
  requires no feedback and equal unit-wire path lengths from inputs to outputs.
- Section 2.5's literal circuit is a directed gate/wire graph that permits
  feedback and memory. A serial/tensor expression language is therefore only a
  corrected feed-forward fragment unless a graph correspondence theorem is
  separately proved.
- Section 7.1 calls a network combinational only when it has no feedback and
  every existing path from any external input to any external output traverses
  the same number of unit wires. Figure 7 states only the narrower fact that
  distinguished argument-to-result paths have equal length and explicitly
  calls that diagram formally sequential.
- The paper treats gates and the identity gate as instantaneous while each
  unit wire contributes one delay step. It does not name arbitrary wire
  permutations as free primitives; structural boundary reindexing must remain
  distinct from physically routed, delay-bearing wire circuits.
- The interaction gate in the billiard model has constrained four-rail outputs:
  only four of the sixteen Boolean states are valid. Its inverse therefore has
  a partial/constrained input interface.
- The garbageless construction runs a realization, copies each result bit using
  constants `0` and `1`, and runs the inverse. It returns the argument and
  scratch constants and produces both `y` and `not y`.
- Under Table (2)'s port order, the copy gadget obtains ordered data outputs
  `(a, not a)` from data inputs `(1, 0)`. Figures 6(c) and 22 route one `0` and
  one `1` graphically without making this port ordering locally obvious, so the
  later circuit must state the wiring permutation explicitly.
- Figure 22 draws its side inputs top-to-bottom as `(0,1)` and its side outputs
  as `(a,not a)`. Read literally as Table (2)'s `(x₁,x₂)` and `(y₁,y₂)`
  ports, that row is reversed: zero-controlled Fredkin sends
  `(a,0,1)` to `(a,not a,a)`. The Stage 8 reconstruction must therefore route
  the canonical result-register pair `(0,1)` to physical data ports `(1,0)`
  before claiming output order `(a,a,not a)`.
- Direct inspection of PDF pp. 229–230 and Figures 4–6 fixes the complete
  primitive slices. AND uses `(a,b,0) ↦ (a,a∧b,¬a∧b)` and selects `y₁`;
  OR uses `(a,1,b) ↦ (a,a∨b,¬a∨b)` and selects `y₁`; NOT and FAN-OUT both use
  `(a,1,0) ↦ (a,a,¬a)`, with NOT selecting `y₂` and FAN-OUT selecting
  `(v,y₁)`. Every remaining port is sink/garbage, not discarded.
- Figure 5's `(c,x) ↦ (y,g)` is a schematic partition, not a claim that those
  blocks are contiguous physical Fredkin ports. In Figures 4 and 6 the source
  constant and selected result occupy different gate coordinates, so a formal
  canonical block order requires explicit structural input/output reindexing.
- Section 3 source constants are prescribed inputs that may be consumed; its
  sink values generally depend on the argument and are not reusable constants.
  A returned-clean scratch register appears only in the later inverse/uncompute
  construction and must be distinguished from both source and garbage.
- The strongest fixed-basis claim says every finite invertible conservative
  function is realizable without garbage using Fredkin gates. The paper
  attributes this to B. Silver but does not give the proof or state the ancilla
  convention with enough precision in the immediate claim.
- Section 4's construction replaces conventional AND, OR, NOT, and FAN-OUT
  elements one-for-one by the Section 3 realizations while supplying constants
  and accepting garbage. It explicitly calls this an existence proof and
  disclaims optimization in gate count, delay stages, and source/sink lines.
- Section 4 states the construction for arbitrary conventional *sequential*
  networks and discusses delay elements, slowdown, time multiplexing, streams,
  and external constant/garbage reservoirs only informally. A finite
  feed-forward translation cannot establish those stateful or resource claims;
  Stage 10 now supplies explicit registered semantics and exact Figures 9 and
  11, but the general compiler, schedule, multiplexing, and resource claims
  remain unresolved.
- Figure 7 is a six-wire initialized-slice network with three zero sources and
  arguments `(A₀,A₁,X)`. Its gates are
  `F(A₁,X,0)`, `F(A₀,0,A₁∧X)`, and
  `F(A₀,0,¬A₁∧X)`, yielding
  `(Y₀,Y₁,Y₂,Y₃)` selected by the binary address `A₁A₀` and
  sink `(A₁,A₀)`. The seven closed-triangle unit wires give latency two
  from every argument to every result, but other complete-boundary paths have
  delays zero, one, or two. Thus the formally sequential drawing does not meet
  the later global every-input/every-output combinational criterion.
- `Simulation.SourceCircuit` is now an indexed finite feed-forward grammar with
  explicit fixed block constants, block discard, AND, OR, NOT, FAN-OUT,
  bijective structural permutation, exact-width serial composition, and
  disjoint tensor. It has no arbitrary-function, delay, state, feedback, or
  trace constructor; tensor evaluation splits its input rather than copying it.
- `SourceCircuit.compile` is total on that grammar. Its exact recursive source
  and garbage widths satisfy `source_garbage_balance`; `sourceState` is fixed
  independently of the argument, `garbage` retains every branch and earlier
  serial garbage block, and `simulationLayout` has scratch width zero.
  `compile_realizes` proves the complete initialized-slice equation by
  structural induction using the Stage 5 primitive witnesses and proved
  four-block reindexings.
- `SourceCircuit.compile_fredkinCount` proves one target Fredkin per named
  source logic node, and `compile_hasLatency_zero` proves only the abstract
  Stage 4 zero-unit-wire path metric. Neither theorem assigns physical routing
  cost to `WirePerm` or establishes graph, sequential, optimization, or
  arbitrary-function completeness.
- Section 7.1 defines the inverse first for the paper's directed network model
  by reversing every unit-wire direction and replacing each gate by its
  inverse. Figure 19 includes a return/feedback arc; the later undoing
  construction in Figures 20–21 instead assumes a combinational network with
  no feedback and one common number of unit wires on every boundary path.
- Horizontal mirroring in Figures 19–21 exchanges the input and output sides
  without reversing the vertical port order. For the checked expression
  grammar this requires reversed serial order, unchanged tensor block order,
  inverse active `WirePerm`, and self-inverse Fredkin syntax.
- The paper says the forward/inverse composite looks like parallel wires only
  in input-output behavior. If the forward term has unit-wire latency `L`, the
  static grammar should assign the round trip latency `L + L`, not zero. The
  inverse path retains the same nonnegative unit-wire count while exchanging
  its endpoints; this is not a `t ↦ -t` execution theorem or physical
  time-reversal invariance.
- Adding an unpadded result register and zero-delay spy layer does not generally
  preserve the paper's global equal-path criterion when the forward circuit has
  positive latency: main-register and result-register routes traverse different
  numbers of unit wires. Stage 8 may prove the complete static initialized-slice
  equation unconditionally, but any timing theorem needs zero latency or an
  explicit delay-balancing construction; the figures do not supply one.
- `Circuit.inverse` now covers all six balanced feed-forward constructors. It
  keeps identity, unit wire, and paper Fredkin syntax; uses `wiring.symm` for an
  active structural permutation; reverses serial order; and retains tensor
  block order. `inverse_inverse` is a structural theorem, not a synthesized
  semantic circuit.
- `Circuit.inverse_eval` identifies evaluation of that term with
  `Conservative.inverse (Circuit.eval circuit)` for every `Circuit n`.
  `eval_inverse_eval` and `eval_eval_inverse` prove both complete-state static
  cancellation directions without projecting or discarding a port.
- `Circuit.PathDelay.inverse` and `pathDelay_inverse_iff` prove exact endpoint
  reversal with unchanged delay. The latency/timing preservation theorems are
  biconditionals, while `Circuit.HasLatency.seq_inverse` and
  `Circuit.HasLatency.inverse_seq` prove the honest `L + L` round-trip latency.
  `UniformLatencyCircuit.inverse` remains a certificate constructor only.
- `WeightLayer`, `Conservative.onWeightLayer`, and
  `Conservative.ofWeightLayers` identify a finite conservative permutation
  with independent permutations of its exact Hamming-weight layers.
- `exists_conservative_extending_pair` classically and noncanonically extends
  injective equal-weight pairs.  `exists_figure25_conservative` applies it to
  Figure 25's initialized slice, including noninjective selected functions and
  result width zero.
- `DirectlyRealizable` and `direct_realization_iff` characterize the separate
  monolithic same-register semantic reading as exactly bijectivity plus weight
  preservation; they do not mention `Circuit`.
- `CleanFredkinRealization` records one exact possibly mixed ancillary prefix,
  a complete circuit and initialized-state equation, exact prefix restoration,
  exclusion of `unitWire`, and zero path latency.
- `patternMatch` and `adjacentTranspositionCircuit` construct a clean
  Johnson-graph edge transposition.  The local ancillary width is at most
  `3*m + 3`, complete width at most `4*m + 5`, and the exact paper-Fredkin
  syntax count is `4*logicGateCount + 3`.
- `singleExchangeClean`, Hamming-layer connectivity, and finite
  permutation-group closure prove `fredkin_complete_conservative` for every
  finite conservative permutation using paper Fredkin plus free structural
  reindexing.  The proof is classical existential and installs no executable
  synthesis algorithm or global closed-form workspace bound.
- `figure25_fredkin_complete` keeps the visible `m + 2n` result-register block
  separate from the additional returned completeness workspace.
- `circuit_four_even` and `middleLayerSwap_not_circuit` formally refute
  universal same-width/no-ancilla completeness at width four.  A separate
  dependency-free exact closure audit checks the generated group is full at
  widths one through three and has index two at width four.
- Stage 10 begins from clean synchronized commit `29723da`.  The clean Stage 9
  default build passed 1,003 jobs and the post-clean completeness audit passed
  with only standard Lean classical/quotient axioms.  There is no
  `Sequential` module, tick/state-machine semantics, stream/trace definition,
  explicit delayed-feedback constructor, closed trajectory, or sequential
  audit at this baseline.
- Stage 10 adds the separate opt-in `ConservativeLogic.Sequential` umbrella,
  deterministic causal traces, complete-boundary conservative ticks, open
  prefix flux, finite retrodiction, register-separated delayed closure,
  all-time closed weight, reversible finite iterates, a zero-latency circuit
  bridge and delay cell, and exact Figures 8, 9, and 11.  The finite API/root
  does not import this layer.  The post-clean default build again passes 1,003
  jobs; the explicitly requested sequential umbrella and audit then pass 722
  jobs with only standard Lean/mathlib axioms.
- Stage 11 is complete from baseline `898bfe5`.  It adds the separate opt-in
  `ConservativeLogic.Billiard` umbrella with exact constrained interaction and
  switch interfaces, a selected admitted collision-site involution,
  independent-site scattering, directed sampled routes, and a four-tick
  Figure 14 trace.  The finite and sequential APIs do not import it.  The
  uncontended clean default build passed 995 jobs and the explicit post-clean
  billiard/sequential umbrellas and audits passed 730 jobs.  Continuous global
  hard-ball mechanics, arbitrary mirror delay, the bridge, Figures 17--18, and
  compositional physical layout remain unresolved.
- Stage 12 begins from clean synchronized commit `1047322`.  The finite root,
  sequential umbrella, billiard umbrella, and eleven audit leaves (the
  guardrail probe plus Stages 2--11) build separately.  There is not yet a
  final public-consumer examples leaf, an aggregate main-result axiom audit, or
  a Stage 12 evidence report.

### Remaining Assumptions and Open Obligations

- The paper's claim that an all-zero scratchpad loses no generality and its
  stated linear lower/upper scratch bounds require reconstruction from other
  sources or fresh proofs.
- A general sequential compiler still requires a literal source semantics,
  delay normalization, a schedule/simulation relation, and per-tick resource
  accounting; the checked examples do not imply that construction.
- Stage 11 established that a narrow sampled billiard abstraction is practical
  while also checking why occupancy alone is not global dynamics.  A stronger
  physical refinement still requires continuous event rules, directed
  hardware, between-sample clearance, and compositional routing data absent
  from the paper.

## Success Metrics and Verification Requirements

The eventual goal is complete only when all of the following hold:

- A pinned Lean 4/mathlib project builds from a clean checkout.
- Public APIs cover finite Boolean functions, reversible equivalences,
  Hamming-weight preservation, Fredkin, one-to-one circuit composition,
  realization interfaces, inverse circuits, and ancilla restoration.
- The paper's core discrete claims have named Lean declarations or documented
  corrected replacements, with hypotheses matching what the proofs use.
- Fredkin ordering and control convention are checked against all eight rows of
  the printed truth table.
- Explicit examples distinguish reversible/nonconservative and
  conservative/nonreversible functions.
- Every fan-out/copy theorem states the initialized target-wire precondition and
  accounts for the complement or other outputs demanded by conservation.
- Circuit evaluation agrees with primitive semantics; composition preserves
  arity, reversibility, and conservation where applicable.
- Ordinary Boolean realization explicitly accounts for constants and garbage.
- Inversion is proved semantically correct for the supported circuit class.
- Compute-copy-uncompute restores argument and scratch space and exposes the
  promised result encoding, with all wire partitions and constants explicit.
- Any claimed Fredkin universality theorem states whether it uses wire
  permutations, constants, garbage, clean ancillas, and returned ancillas.
- Resource theorems are separate from existence theorems and are proved only
  when the syntax supports the measured resource.
- Completed Lean sources pass focused builds, full `lake build`, proof-hole and
  project-axiom scans, `#print axioms` audits for main results, and
  `git diff --check`.
- `README`/paper-map documentation links each central paper claim to a Lean
  declaration, correction entry, or explicitly unresolved issue.
- No physical conclusion is presented as a mathematical corollary of the
  finite circuit library.

## Paper Claim Map

| Paper location | Reconstructed formal target | Planned stage | Current disposition |
|---|---|---:|---|
| §2.2, P4–P6 | Separate delayed identity, reversible maps, and one-to-one composition | 2–5, 10 | Stages 2–4 separate static equivalences, unit-wire delay metadata, and an indexed grammar whose serial/tensor constructors consume ports one-to-one. The paper's physical motivations are not consequences of these definitions |
| §2.2, P7 | The abstract model should have at least one additive conserved quantity | — | Generic physical/mathematical motivation only; P7 itself does not select Hamming weight |
| §§2.3–2.5 | In the Boolean model, `N₁`/Hamming weight is additive across wire portions and preserved by unit wires, gates, and closed transitions | 2–4, 10 | Stages 2–4 prove static block/primitive/circuit preservation. Stage 10 corrects open execution to `ConservativeLogic.Sequential.ConservativeMachine.tick_weight_balance` and telescoping `ConservativeLogic.Sequential.ConservativeMachine.run_prefix_weight_balance`, while `ConservativeLogic.Sequential.ConservativeMachine.closedOrbit_weight` proves the complete delayed-closure `memory ++ loopRegister` state has invariant Hamming weight at every natural time |
| §2.5 | `N₀ = N - N₁`, so zero count is conserved on a fixed-width closed circuit but is not an independent invariant | 2 | Documented derived consequence, not a separate observable in the Lean API: `BitState n` fixes `N=n` and `hammingWeight` is `N₁`, so the remaining-coordinate count is definitionally `n - hammingWeight state`. No independent `N₀` theorem or physical quantity is claimed |
| §2.2, P8 | Local-Euclidean/layout constraint on circuit connectivity | — | Out-of-model for this library. The paper explicitly does not develop P8, and Stage 11 proves no packing/connectivity bound; the sampled route examples are not a P8 geometry theorem |
| §2.3 | Unit wire is delayed identity, reversible, and conservative | 3, 4, 7, 10 | Stages 3–7 separate aligned static identity, conservation, and one-step path metadata. Stage 10's structural-swap delay cell proves tick-zero output is explicit initialization and `output(t+1)=input(t)` by `ConservativeLogic.Sequential.DelayCell.output_succ`; `ConservativeLogic.Sequential.DelayCell.unitWire_not_instantaneous` prevents static positive-delay syntax from entering a zero-latency tick core. Physical time reversal remains unproved |
| §2.3 | Unit wires compose to wires of every fixed positive integral length, with delays adding | 4 | Built composition rule rather than a separately named iterator: each explicit finite chain uses the `Circuit.seq` constructor, and `ConservativeLogic.Circuit.HasLatency.seq` proves that its component delays add. No generic `wireOfLength` declaration or spatial-layout theorem is installed |
| §2.4, Table (2) | Paper-convention Fredkin semantics, involution, bijection, weight preservation | 3 | `ConservativeLogic.PaperFredkin.table` fixes the port order and convention; all eight rows are independently audited; `ConservativeLogic.PaperFredkin.map_involutive`, `ConservativeLogic.PaperFredkin.equiv`, `ConservativeLogic.PaperFredkin.map_isReversible`, `ConservativeLogic.PaperFredkin.map_weightPreserving`, and `ConservativeLogic.PaperFredkin.conservative` prove the separate static properties |
| §2.4 | Fredkin is nonlinear under an explicitly selected coordinatewise-XOR/`F₂` notion | 3 | `ConservativeLogic.XorLinear` states the selected reconstruction; `ConservativeLogic.PaperFredkin.map_xor_counterexample` and `ConservativeLogic.PaperFredkin.map_not_xorLinear` prove a concrete failure of additivity, without attributing that definition to the paper |
| §2.5, Fig. 3 | Literal directed-graph open/closed transition semantics, feedback, memory, balanced external ports, and closed-system weight conservation | 10 | Implemented for the corrected register-separated semantic fragment: `ConservativeLogic.Sequential.ConservativeMachine` is a total `memory ++ input ↔ nextMemory ++ output` tick, and `ConservativeLogic.Sequential.ConservativeMachine.closeFeedback_step` shows the output block becomes next-tick loop state. Trace uniqueness, causality, open flux, closed conservation, and finite reversibility are proved. This is not a literal graph elaborator |
| §§2.5, 7.1 | Acyclic/equal-latency combinational fragment and one-to-one composition | 4, 7 | `Circuit` is a corrected one-to-one feed-forward grammar; `PathDelay`, `HasLatency`, and `MeetsPaperCombinationalTiming` formalize the equal-unit-wire-path clause. `Circuit.pathDelay_inverse_iff` and `meetsPaperCombinationalTiming_inverse_iff` prove exact reversal/preservation for that grammar only. No graph correspondence, feedback semantics, or physical routing result is claimed |
| §2.5 | Reversibility and conservation are independent | 2 | Proved semantically for ordinary Boolean endomaps by `Independence.reversible_not_weightPreserving` and `Independence.weightPreserving_not_reversible`; this does not assert a literal circuit realization |
| §3, Fig. 5 | Realization partitions source/argument and result/sink, fixes constants independently of the argument, and permits argument-dependent garbage | 5 | `Layout` and `Realizes` give a stronger explicit five-block specialization: fixed source and returned-clean scratch, universal argument, selected result, explicit argument-indexed garbage, and equality of the complete boundary state |
| §3, Figs. 4–6 | Fredkin realizes AND, OR, NOT, and fan-out with constants/garbage | 5 | `fredkin_realizes_and`, `fredkin_realizes_or`, `fredkin_realizes_not`, and `fredkin_realizes_fanout` prove the exact complete tuples using named active port permutations; FAN-OUT is constrained by source `(0,1)` and retains `¬a` as garbage |
| §3, Fig. 7 | Demultiplexer semantics include the complete output and address-echo garbage; distinguished argument-to-result routes have delay two | 4, 6 | `ConservativeLogic.Simulation.Demultiplexer.demux_realizes` checks the full six-wire initialized slice with source `000`, four binary-addressed outputs, and garbage `(A₁,A₀)`; the term has three Fredkins and seven unit wires. `ConservativeLogic.Simulation.Demultiplexer.argument_to_result_path` constructs a delay-two path for every named argument/result pair, while `ConservativeLogic.Simulation.Demultiplexer.argument_to_result_path_delay_two` proves every such grammar-induced path has delay two. `ConservativeLogic.Simulation.Demultiplexer.zero_source_to_y0_path` and `ConservativeLogic.Simulation.Demultiplexer.demuxCircuit_not_meetsPaperCombinationalTiming` prove that the full boundary is not globally equal-latency |
| §3, Fig. 8 | Reconstruct a transition/trace specification for the asserted `J-K̄` flip-flop realization | 10 | Resolved by an actual Fredkin-plus-output-routing `Network 1 2`. `Figure8.tick` proves `(q,K̄,J) ↦ (if q then K̄ else J,q,if q then J else K̄)` with next state, visible `Q`, and explicit `?` garbage; initialization, characteristic trace, all eight rows, and hold/set/reset/toggle behavior are checked |
| §4 | Conventional finite combinational networks can be translated to conservative networks using constants and garbage | 6 | Proved constructively for the explicit indexed `SourceCircuit` grammar by `compile_realizes`, with exact fixed sources, complete garbage, zero scratch, exact Fredkin count, and abstract latency zero. The target basis is Fredkin plus explicit structural reindexing. This is not a graph-encoding, arbitrary-function-completeness, delay-normalization, or sequential theorem |
| §4 | Arbitrary conventional sequential networks can be simulated by conservative sequential networks | 10 | Partially resolved only at the semantic/example level. Stage 10 supplies explicit initialization, causal traces, and Figures 9/11, but installs no general compiler. Constant sources and garbage are per-tick streams; delay normalization, scheduling, time multiplexing, and a general stream simulation relation remain unresolved |
| §4, Figs. 9–11 | Serial-adder simulation includes initialization and stream semantics | 10 | `ConservativeLogic.Sequential.SerialAdder.paper_recurrence` checks Figure 9 with explicit initial accumulator, while `ConservativeLogic.Sequential.SerialAdder.completeTickEquiv` and `ConservativeLogic.Sequential.SerialAdder.no_conservative_machine` separate bijectivity from conservation. Figure 11 is an exact two-Fredkin `Network 3 3` on the literal `(x,0,1)` source slice; `ConservativeLogic.Sequential.Figure11.tick_initialized`, `ConservativeLogic.Sequential.Figure11.state_spec`, `ConservativeLogic.Sequential.Figure11.output_spec`, and `ConservativeLogic.Sequential.Figure11.paper_recurrence` prove all stored/output wires and `Y(t+2)=Y(t+1) xor X(t)`. Figure 10's dense routing, factor-five schedule, multiplexing, and source/sink counts remain unresolved |
| §4 | Turing-machine/cellular-automaton universality | — | Out-of-model for this finite library. No indefinitely extendible tape/environment, universal machine, cellular automaton, or infinite constant/garbage reservoir is formalized |
| §6.1 | Integral-time samples of the hard-ball setup use a unit grid, radius `1/√2`, unit velocity, and a restriction to right-angle collisions | 11 | Corrected discrete abstraction implemented. `Grid.Route` retains four directed unit moves, `Collision.AllowedState` restricts local masks, and independent `ScatteringLayer.Configuration` has an involutive count-preserving step. `illegalThreeBallMask_not_allowed`, support-overlap, and sampled-clearance audits record why this is not the paper's missing continuous global mechanics |
| §6.2 | `(p,q) ↦ (pq, ¬p q, p ¬q, pq)` is an equivalence onto four valid rail states and preserves ball count | 11 | Resolved exactly by `Interaction.equiv`, `decode`, `encode_weightPreserving`, `card_validOutput`, and `no_raw_equiv`. `Collision.map_embed` realizes the complete initialized four-channel slice, and `Figure14.output_refines_collision` supplies the selected four-tick coordinate trace |
| §6.3 | Interaction-gate AND/NOT realization plus universality with constants and valid routing/timing | 11 | `Interaction.encode_a` and `not_with_true_source` check the named logic slices with the occupied constant explicit. `Grid.mirrorTurn_reflects`, `fourTickDetour_reflects`, and the crossing theorems check selected sampled routing obligations. Arbitrary mirror delay, the bridge, routing composition, and physical universality remain unresolved |
| §6 introduction and §6.4 | Any conservative-logic circuit has a billiard-ball realization | 11 | Not theoremized. `collision_not_unionPreserving` and `no_wirePerm_collision` show that collision cannot be replaced by independent union/routing, while equal-endpoint short/detour routes show endpoint algebra does not fix timing. A whole-circuit result still needs directed global dynamics, schedules, continuous clearance, the bridge, and a compositional layout compiler |
| §6.4, Figs. 16–18 | The switch `(c,x) ↦ (c,cx,¬c x)` is an equivalence onto four valid three-rail states, and collision layouts refine switch/Fredkin semantics | 11 | The logical switch is resolved by `Switch.equiv`, `encode_weightPreserving`, `card_validOutput`, and `no_raw_equiv`. Figures 17–18 remain unresolved physical layouts: the caption says steering/timing mirrors and unit wires are not explicitly indicated, and no coordinates, common latency, bridge trace, trivial-crossover schedule, or clearance proof is available |
| §7.1 | Reversing gates and wires yields a semantic inverse for combinational networks | 7, 10 | Stage 7 proves exact feed-forward static inversion. Stage 10 proves complete tick inversion, finite open-run retrodiction from terminal memory and complete outputs, and reversible closed finite iterates. These are semantic backward-determinism results, not a literal Figure 19 graph-reversal compiler, infinite-stream inverse without terminal state, oriented `t ↦ -t` execution, or physical time reversal |
| §7.1, Figs. 22–24 | Compute-copy-uncompute returns argument and scratch and emits `(y, not y)` | 8 | `copyPair_spec` explicitly routes canonical `(a,0,1)` to physical `(a,1,0)`, `copyRegister_spec` proves `(y,0ⁿ,1ⁿ) ↦ (y,y,¬y)`, and `compute_copy_uncompute_spec` restores the complete packed scratch/source/argument state from any supplied `Realizes` witness. The result register is exactly `2n` wires and no transient midpoint garbage remains |
| §7 introduction, §§7.1–7.2 | Garbage can be reduced to a returned copy of the argument, with claimed line-count and circuit-complexity consequences | 8, 9 | Stage 8 proves the exact finite restoration transformation and Fredkin count `2·count(circuit)+resultWidth`. Stage 9 proves finite clean Fredkin-plus-structural-reindexing existence with an exactly returned, possibly mixed ancillary prefix, but deliberately installs no global closed-form workspace, line-count, or time bound. The paper's asymptotic endpoints remain unresolved without a cost model |
| §7.1, Fig. 24(b) | The paper's restored `c` source/workspace can start all zero without loss of generality | 9 | Stage 9 re-audits this as an unresolved Margolus attribution with no precise proof or source. In the library layout, paper `c` is the consumed `source` later restored by compute-copy-uncompute; the separate already-returned `scratch` field is a stronger interface. No all-zero conversion theorem is claimed |
| §7.2, Fig. 25 | For any `f`, the initialized-slice map `(x,0ⁿ,1ⁿ) ↦ (x,f x,¬f x)` extends to a total conservative permutation | 5, 9 | Resolved semantically by the classical noncanonical Hamming-layer theorem `exists_figure25_conservative`; `figure25_fredkin_complete` then supplies a separate returned clean workspace and a paper-Fredkin-plus-structural-reindexing realization. The drawing itself still specifies only the initialized slice and no small canonical circuit |
| §7.2 | Worst-case synthesis of arbitrary `f` from a fixed bounded primitive basis may require scratch; claimed endpoint size/time tradeoffs | 9 | Stage 9 proves only finite existential clean synthesis and a linear local bound for one Johnson-graph edge macro. The asserted `exp(m)` sufficient and proportional-to-`m` least-usable endpoints remain unresolved because they omit family quantifiers, constants, output-width dependence, initialization/return conventions, and a formal cost model |
| §7.3, Fig. 26 | A direct same-register map `f : BitState m → BitState m` is semantically realizable by one arbitrary conservative primitive iff it is invertible and conservative | 9 | Resolved at exactly that monolithic same-width scope by `direct_realization_iff`. It is kept separate from the fixed-basis theorem and does not cover unequal-width maps |
| §§2.5, 7.3 | Every invertible conservative finite function, and each fixed finite iterate, is Fredkin-realizable without visible garbage | 9, 10 | Stage 9 supplies corrected finite clean synthesis and refutes the no-ancilla reading. Stage 10 adds explicit registered execution: `closedIterateEquiv` and its inverse-cancellation theorems package each finite delayed-closure iterate as a reversible finite state map. This does not add physical routing, all-zero ancillas, a global resource bound, or a literal distributed-delay implementation |
| §7.3 | Closed general-purpose computers have NAND-comparable gate complexity | 10 | Explicitly deferred: the paper supplies neither the scheduling theorem nor the gate/throughput/resource model required to compare complexity |
| Abstract and physical passages in §§1–2, 5–10 | Zero dissipation, entropy, energy, noise, topology, and physical-realizability conclusions | — | Documentation only absent explicit physical state, dynamics, and thermodynamic models |

## Correction and Uncertainty Log

Entries remain open until a stage records checked evidence and a final
disposition.

| ID | Issue | Required disposition |
|---|---|---|
| CL-001 | The paper uses zero-controlled swapping, opposite to the common modern Fredkin convention. | Resolved for the Stage 3 default by the explicit `PaperFredkin` namespace, public coordinate laws, `PaperFredkin.table`, and all eight audited rows. Stage 9 adds the separately named `oneControlledFredkin`: paper Fredkin followed by an explicit data-wire swap, with its own truth-table, structural-basis, and zero-latency theorems. The paper convention remains the primitive default. |
| CL-002 | “Inverse wire” mixes identity-on-values with reversal of time/orientation, while footnote 3 separately warns that invertibility does not imply time-reversal invariance. | Advanced through Stage 10. Natural-time causal traces are forward-only; `tickEquiv_symm_apply_tick`, finite `retrodictList_executeList`, and closed-iterate cancellation recover complete retained boundaries. No theorem turns this into literal graph reversal, negative-time execution, infinite-stream inversion without a terminal state, or physical time-reversal symmetry. |
| CL-003 | Reversibility and bit conservation are asserted independent, with external citations but no small witness or proof in the paper. | Resolved for the semantic predicate claim in Stage 2 by one-bit negation and two-bit Boolean sorting. The latter is documented only as an ordinary endomap, not a conservative-logic gate or literal circuit realization. |
| CL-004 | FAN-OUT is shown diagrammatically although arbitrary copying is not reversible. | Resolved for the one-bit Stage 5 example: `fredkin_realizes_fanout` is a width-three circuit with fixed source `(0,1)`, selected result `(a,a)`, and explicit garbage `¬a`; `fredkinFanoutCircuit_isReversible` and `fredkinFanoutCircuit_weightPreserving` concern the complete map. Guarded failures reject a source-free unequal-width copier and an equal-width reversible interpretation of the selected target. |
| CL-005 | Figure 7 states equal delay only from argument to result, whereas §7.1 defines a combinational network using equal delay from any input to any output. | Resolved at the precise Stage 6 scope. The checked reconstruction has seven unit wires; `argument_to_result_path` supplies a delay-two route for each distinguished argument/result pair and `argument_to_result_path_delay_two` proves uniqueness of that delay for every such path. A third-source-to-`Y₀` path has delay zero, so `demuxCircuit_not_meetsPaperCombinationalTiming` proves the full term fails the later global criterion. |
| CL-006 | The §4 universality argument translates ordinary sequential circuits informally and handwaves delay normalization. A combinational translation cannot establish its stateful or resource claims. | Partially resolved. Stage 6 proves only the finite feed-forward compiler; Stage 10 supplies explicit traces plus exact Figures 9 and 11. Figure 11 names fresh `(0,1)` at every tick and retains all garbage. No general sequential compiler, rescaling relation, factor-five schedule, delay normalization, source/drain bound, or time-multiplexing theorem is inferred. |
| CL-007 | The interaction and switch gates use constrained, unequal-width rail encodings. They preserve balls/ones but not the number of zero-valued physical rails and are exceptions to the ordinary balanced-port gate type. | Resolved at the Stage 11 logical interface. `Interaction.equiv` and `Switch.equiv` target exact four-state subtypes; both encoders are heterogeneously `WeightPreserving`, while `encode_vacancies` proves respectively two and one additional vacant rails. `card_validOutput` and `no_raw_equiv` prevent raw `Bool² ≃ Bool⁴`/`Bool² ≃ Bool³` readings. Only the separate ambient four-channel `Collision.conservative` is an equal-width conservative map. |
| CL-008 | Figure 18 says steering/timing mirrors and unit wires are not explicitly indicated, but identifies bridge crossovers and calls the others trivial; clearance and simultaneous collision scheduling are additional formalization obligations rather than quoted omissions. | Partially resolved and deliberately open after Stage 11. Sampled routes now certify mirror turns at distinct fixed sites, a same-position-endpoint detour whose boundary directions differ, and a simultaneous naked-crossing conflict. A one-tick stagger avoids equal centers but fails threshold-two sampled clearance; a two-tick stagger meets that sampled threshold. Figure 14 has a complete four-tick trace. Continuous clearance, a drop-in directed delay, the Figure 15 bridge, Figure 17, both Figure 18 layouts, and arbitrary layout composition remain unresolved until fixed coordinates/hardware, event-disjoint schedules, and all-input crossover/clearance proofs are supplied. |
| CL-009 | The spy/copy gadget needs one `0` and one `1` per copied result bit and emits both value and complement; Figure 22's drawn top-to-bottom `(0,1) → (a,not a)` data order conflicts with Table (2)'s zero-controlled swap. | Resolved for the Stage 8 reconstruction: `copyPairInputWiring = PaperFredkin.dataSwap`, `copyPair_physical_spec` checks `(a,1,0)`, and `copyPair_spec` checks canonical `(a,0,1) ↦ (a,a,¬a)`. `copyRegister_spec` lifts the corrected order to disjoint all-width spies, including width zero. |
| CL-010 | “Garbageless” still returns the original argument and uses/restores scratch. | Resolved for a supplied finite `Realizes` witness by `compute_copy_uncompute_spec`: the exact packed scratch, source, and argument are returned, the named transient garbage is uncomputed, and the separate ancillary register contains `(target,bitwiseNot target)`. This does not mean absence of ancillary or argument-dependent output wires. |
| CL-011 | All-zero workspace sufficiency is attributed to Margolus without proof. The paper's Figure 24 scratchpad is the `c` source consumed into `g` and later restored, not the library's separate already-returned `scratch` block. | Unresolved after Stage 9. The corrected completeness theorem exposes an exact, possibly mixed clean initialization and does not imply an all-zero conversion. Any future conversion must cite or prove the construction and state its effects on width, count, and delay. |
| CL-012 | Scratchpad size claims use informal proportionality and an unstated cost model: `exp(m)` sufficiency at a least-time extreme and least usable Fredkin scratch proportional to `m`. | Unresolved after Stage 9. The local adjacent-transposition macro has proved linear bounds and an exact gate count, but the final classical group-closure witness has no installed global closed form. A stronger theorem still needs circuit families, scratch/line and time measures, constants, output-width dependence, basis, initialization, and restoration. |
| CL-013 | “Any invertible conservative function” is Fredkin-realizable, attributed to B. Silver in §7.3 but D. Silver in the acknowledgments, with no proof or bibliography entry. Ancilla and routing conventions are unclear; Figure 26 explicitly omits scratch for clarity, and §2.5 tacitly includes unit wires and identity. | Resolved in corrected form by `fredkin_complete_conservative`, whose witness records exact clean initialization/restoration, excludes `unitWire`, and permits explicit structural `WirePerm` routing. `middleLayerSwap_not_circuit` refutes the no-ancilla reading, while a dependency-free exact group audit establishes width-four minimality through widths one to four. Structural reindexing is not called physical Fredkin synthesis, and the B./D. attribution discrepancy remains unresolved from the paper. |
| CL-014 | Figure 25 specifies `F0` only on initialized inputs `(x,0ⁿ,1ⁿ)`; total invertibility and conservation do not follow “by definition,” and arbitrary-gate existence would not imply fixed-basis synthesis. | Resolved by `exists_conservative_extending_pair` and `exists_figure25_conservative`, which perform a classical noncanonical extension inside each finite Hamming layer. `figure25_fredkin_complete` separately applies corrected fixed-basis synthesis and exposes the additional returned clean workspace. |
| CL-015 | Claims about infinite blank tape/environment supplying constants and garbage space are not finite-circuit theorems. | Exclude or formalize in a separately scoped infinite model. |
| CL-016 | Physical reversibility, entropy, and zero-dissipation conclusions do not follow from finite bijections alone. | Keep them non-theorem commentary unless physical state and dynamics are formalized. |
| CL-017 | A serial/tensor/permutation syntax is not literally the paper's directed-graph circuit model, which includes feedback and open transducers with memory; structural wire renaming is also not automatically a physical wire/permutation circuit with delay. | Stages 4, 6, 7, and 9 use a corrected feed-forward grammar. Stage 10's `Network` accepts only a `HasLatency 0` acyclic core and puts every stored wire in explicit state; feedback is register-separated. Figure 8 and Figure 11 are manually reconstructed examples. There is still no general literal-graph elaboration or physical routing theorem. |
| CL-018 | The paper calls Fredkin nonlinear without naming the algebraic structure. | Resolved for one explicit reconstruction by `BitState.xor`, `BitState.falseState`, `XorLinear`, the named `PaperFredkin.map_xor_counterexample_*` equations, and `PaperFredkin.map_not_xorLinear`. This is not presented as the paper's missing definition or as physical nonlinearity. |
| CL-019 | Figure 8 is asserted to realize a `J-K̄` flip-flop, but the paper gives no transition equation, initialization condition, or trace specification. | Resolved for the diagram-qualified reconstruction by `Figure8.tick` and `Figure8.characteristic`: `(q,K̄,J) ↦ (if q then K̄ else J,q,if q then J else K̄)`. The initial bit is explicit, the first output is `Q`, the second is the paper's `?` garbage, and all eight rows plus hold/set/reset/toggle traces are audited. |
| CL-020 | Figures 20–23 assume a combinational forward network but do not specify delay balancing for the enlarged boundary after adding result-register constants and spy outputs. | Resolved with a corrected split result: `compute_copy_uncompute_spec` is unconditional and static, while `computeCopyUncompute_hasLatency_zero` requires a zero-latency supplied circuit. The non-public `unitWireUncompute_not_meetsPaperCombinationalTiming` exhibits delay-two and delay-zero paths through the actual unpadded builder. No positive-latency or padding theorem is claimed. |
| CL-021 | Section 2.5's `N₁` trajectory-invariant wording is sound for a closed circuit's complete stored state, but an open transducer can exchange true bits with its environment. | Resolved by `tick_weight_balance`, telescoping `run_prefix_weight_balance`, and `closedOrbit_weight`. The delay-cell audit concretely changes memory weight while preserving complete boundary flux. Only the delayed closed `memory ++ loopRegister` state has the all-time invariant. |
| CL-022 | Integral grid occupancy is not a deterministic billiard state: velocity/directed channel and fixed hardware are required, and the paper supplies no total rule for shared-ball, multi-contact, mirror-collision, or target conflicts. | Stage 11 installs only a selected four-channel scattering rule on `Collision.AllowedState` and finite products of independent owned sites. `illegalThreeBallMask_not_allowed` and `tripleCandidates_conflict` reject two concrete missing-event cases. Directed sampled routes are a stated abstraction; no theorem claims a global continuous hard-ball update or legal-orbit closure under arbitrary routing. |
| CL-023 | The switch branch pair `(c x, ¬c x)` is one-hot-or-empty, not a general dual-rail pair `(b,¬b)`; mirrors also redirect balls but do not supply occupied Boolean constants. | Stage 11 keeps all three switch rails and the exact valid-output subtype. The only NOT slice is `Interaction.not_with_true_source`, whose documentation names the occupied `q=true` source. No dual-rail attribution, free constant, reservoir, or repeated source-stream theorem is inferred from a mirror. |

## Dependency Notes and Module Direction

Stage 1 selected matching stable Lean/mathlib release tags `v4.32.0` (published
2026-07-13). `formal/lean-toolchain` pins Lean, `formal/lakefile.toml` pins
mathlib by tag, and `formal/lake-manifest.json` locks mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. The private probe uses narrow
imports `Mathlib.Data.Fintype.Pi`,
`Mathlib.Logic.Equiv.Basic`, `Mathlib.Logic.Equiv.Fin.Basic`, plus
`Mathlib.Data.BitVec` solely to audit the rejected packed alternative.

Checked low-to-high layout through Stage 11:

```text
ConservativeLogic/
  State/Core.lean           -- `Fin n → Bool` states and Hamming weight
  Reversible/Core.lean      -- finite reversible and conservative maps
  Gate/UnitWire.lean        -- aligned identity value map and delay metadata
  Gate/Fredkin.lean         -- exact paper primitive semantics and properties
  Gate/Fredkin/Nonlinear.lean -- selected XOR interpretation and counterexample
  Circuit/Syntax.lean       -- arity-safe linear wiring and composition
  Circuit/Semantics.lean    -- evaluation and preservation theorems
  Circuit/Timed.lean        -- delays/equal-latency feed-forward networks
  Audit/Circuit.lean        -- non-public Stage 4 regressions and axiom audit
  Circuit/Inverse.lean      -- structural inverse, static correctness, reversed paths
  Audit/Inverse.lean        -- non-public Stage 7 regressions and axiom audit
  Realization/Core.lean     -- exhaustive source/clean-scratch/result/garbage interface
  Realization/Primitive.lean -- exact routed Section 3 Fredkin realizations
  Audit/Realization.lean    -- non-public Stage 5 boundary and axiom audit
  Simulation/Source.lean    -- explicit unequal-arity finite source grammar
  Simulation/Fredkin.lean   -- exact-resource constructive target compiler
  Simulation/Demultiplexer.lean -- checked Figure 7 value/timing reconstruction
  Audit/Simulation.lean     -- non-public Stage 6 boundary and axiom audit
  Ancilla/Uncompute.lean    -- explicit spy registers and compute-copy-uncompute
  Audit/Uncompute.lean      -- non-public Stage 8 boundaries, timing, and axiom audit
  Completeness/Semantic.lean -- Hamming layers and noncanonical semantic completion
  Completeness/Fredkin.lean -- clean witness, basis certificate, and composition
  Completeness/Johnson.lean -- equal-weight exchange connectivity
  Completeness/Adjacent.lean -- explicit clean local transposition and routing
  Completeness/Synthesis.lean -- finite group-closure completeness theorem
  Completeness/NoAncilla.lean -- width-four parity obstruction
  Audit/Completeness.lean   -- Stage 9 boundaries and axiom audit
  Audit/completeness_groups.py -- exact dependency-free widths 1--4 group audit
  Sequential/Core.lean      -- deterministic machines, runs, and causality
  Sequential/Conservative.lean -- full-boundary flux and delayed closure
  Sequential/Circuit.lean   -- zero-latency circuit bridge and delay cell
  Sequential/Figure8.lean   -- complete J-Kbar flip-flop reconstruction
  Sequential/SerialAdder.lean -- conventional Figure 9 recurrence boundary
  Sequential/Figure11.lean  -- exact full conservative adder trace
  Sequential.lean           -- opt-in sequential umbrella, outside finite API
  Audit/Sequential.lean     -- non-public Stage 10 regressions and axiom audit
  Billiard/Interface.lean   -- constrained interaction/switch rail equivalences
  Billiard/Collision.lean   -- selected local collision and admitted subtype
  Billiard/Discrete.lean    -- independent simultaneous scattering layers
  Billiard/Geometry.lean    -- directed sampled routes, mirrors, timing conflicts
  Billiard/Figure14.lean    -- exact four-tick sampled interaction trace
  Billiard.lean             -- opt-in billiard umbrella, outside finite API
  Audit/Billiard.lean       -- Stage 11 rows, obstructions, and axiom audit
  API.lean                  -- thin public re-export
```

Keep core definitions below proof-heavy universality and audit leaves. The
optional sequential and billiard modules must not become dependencies of the
finite combinational API. Continue using `fredkin-1982/BUILD-PLAN.md` for
incremental build discipline.

## Proposed Theorem Outline

Names from completed stages are exact declarations; later-stage names remain
placeholders to refine during stage work.

- `hammingWeight_append`: weight is additive across explicit wire blocks.
- `Reversible.injective` / `Reversible.surjective`: finite reversible maps have
  the expected function properties.
- `Conservative.comp` and `Conservative.inverse`: conservation is closed under
  composition and inversion of an equivalence.
- `Independence.reversible_not_weightPreserving` and
  `Independence.weightPreserving_not_reversible`: concrete semantic
  independence witnesses for the two standalone predicates.
- `UnitWire.value_apply`, `UnitWire.value_isReversible`, and
  `UnitWire.value_weightPreserving`: static identity, reversibility, and
  conservation of the unit-wire value map; `UnitWire.delay_eq_one` records its
  separate one-step metadata.
- `PaperFredkin.map_state_false` and `PaperFredkin.map_state_true`: exact
  zero-controlled behavior in the paper's ordered ports.
- `PaperFredkin.table`: parametric form of all eight rows in Table (2), whose
  literal rows are also checked independently by the Fredkin audit.
- `PaperFredkin.map_involutive`, `PaperFredkin.equiv`,
  `PaperFredkin.map_isReversible`, `PaperFredkin.map_weightPreserving`, and
  `PaperFredkin.conservative`: separate inverse, bijection, and conservation
  results for the primitive.
- `PaperFredkin.map_xor_counterexample` and
  `PaperFredkin.map_not_xorLinear`: concrete failure of the selected
  `XorLinear` predicate.
- `Reversible.tensor`, `Conservative.tensor`, and their arbitrary-append
  application laws: disjoint ordered parallel closure.
- `Circuit.eval_identity`, `Circuit.eval_unitWire`, `Circuit.eval_fredkin`,
  `Circuit.eval_permute`, `Circuit.eval_seq`, `Circuit.eval_tensor`, and
  `Circuit.eval_tensor_append`: exact compositional static semantics.
- `Circuit.eval_isReversible` and `Circuit.eval_weightPreserving`: the two
  general circuit properties remain separately exposed.
- `Circuit.PathDelay`, `Circuit.HasLatency`, and
  `Circuit.MeetsPaperCombinationalTiming`: static boundary-path delay and the
  global equal-unit-wire-latency criterion.
- `Circuit.HasLatency.seq`, `Circuit.HasLatency.tensor`, and
  `Circuit.HasLatency.compensatedTensorSeq`: uniform serial/equal-latency tensor
  closure plus blockwise compensation across nonuniform intermediate tensors.
- `Circuit.UniformLatencyCircuit`: a certificate-only wrapper with checked
  identity, unit-wire, Fredkin, permutation, serial, and tensor constructors.
- `Realization.Layout`, `Layout.width`, `Layout.packInput`, and
  `Layout.packOutput`: the exhaustive source/returned-scratch/argument and
  returned-scratch/result/garbage boundaries.
- `Layout.packInput_argument_injective`,
  `Layout.packOutput_resultGarbage_injective`,
  `Layout.hammingWeight_packInput`, and `Layout.hammingWeight_packOutput`:
  packing loses no named data and preserves exact block-weight accounting.
- `Realizes.targetGarbage_injective`,
  `Realizes.garbage_separates_collisions`,
  `Realizes.garbage_injectiveOn_fiber`, `Realizes.fiber_card_le`,
  `Realizes.card_argument_le_resultGarbage`,
  `Realizes.target_injective_of_resultDeterminesGarbage`,
  `Realizes.target_injective_of_argumentIndependentGarbage`,
  `Realizes.target_injective_of_noGarbage`, and `Realizes.weight_balance`:
  necessary information and conservation constraints on a full-state
  initialized-slice realization.
- `fredkin_and_complete`, `fredkin_or_complete`, `fredkin_not_complete`, and
  `fredkin_fanout_complete`: exact complete Section 3 boundary equations.
- `fredkin_realizes_and`, `fredkin_realizes_or`, `fredkin_realizes_not`, and
  `fredkin_realizes_fanout`: primitive embeddings with exact sources, routing,
  selected results, and garbage; the last is additionally backed by
  `fredkinFanoutCircuit_isReversible` and
  `fredkinFanoutCircuit_weightPreserving` for the complete width-three map.
- `Simulation.SourceCircuit`, `SourceCircuit.eval`, and
  `SourceCircuit.logicGateCount`: the closed finite feed-forward source syntax,
  with visible constants, discard, nonlinear gates, FAN-OUT, permutation,
  serial composition, and disjoint tensor.
- `SourceCircuit.source_garbage_balance`, `sourceState`, `garbage`, and
  `simulationLayout`: exact recursively computed zero-scratch resources and
  complete boundary data.
- `SourceCircuit.compile` and `SourceCircuit.compile_realizes`: total
  Fredkin-plus-structural-reindexing compilation and its general complete-state
  simulation theorem.
- `Circuit.fredkinCount`, `SourceCircuit.compile_fredkinCount`, and
  `SourceCircuit.compile_hasLatency_zero`: exact gate accounting and the
  compiler's qualified zero-unit-wire path theorem.
- `Demultiplexer.demux_realizes`, `demux_fredkinCount`,
  `demuxCircuit_unitWireCount`, and `argument_to_result_path`: complete Figure
  7 values/resources and selected delay-two path witnesses;
  `argument_to_result_path_delay_two` proves every path between those named
  interfaces has that delay, while
  `demuxCircuit_not_meetsPaperCombinationalTiming` records the stronger global
  timing failure.
- `Circuit.inverse`, its six constructor reduction laws, `inverse_inverse`, and
  `inverse_involutive`: total width-preserving structural inversion of the
  balanced feed-forward grammar.
- `Circuit.inverse_eval`, `eval_inverse_eval`, and `eval_eval_inverse`:
  equality with the inverse complete conservative equivalence plus both static
  cancellation directions.
- `Circuit.PathDelay.inverse` and `pathDelay_inverse_iff`: exact route endpoint
  reversal with the same nonnegative unit-wire count.
- `Circuit.HasLatency.inverse`, `hasLatency_inverse_iff`,
  `MeetsPaperCombinationalTiming.inverse`, and
  `meetsPaperCombinationalTiming_inverse_iff`: common-latency preservation in
  both directions.
- `Circuit.HasLatency.seq_inverse` and `Circuit.HasLatency.inverse_seq`:
  forward/inverse static cancellation retains round-trip latency `L + L`; it
  is not a zero-delay syntactic identity.
- `Circuit.UniformLatencyCircuit.inverse`: a proof-certificate constructor,
  not backward execution semantics.
- `copyPair_physical_spec` and `copyPair_spec`: physical `(a,1,0)` and
  explicitly routed canonical `(a,0,1)` both yield `(a,a,not a)` in the
  documented output order.
- `copyRegister_spec`, `hammingWeight_resultRegisterInput`, and
  `hammingWeight_resultRegisterOutput`: disjoint all-width spying maps
  `(x,0ⁿ,1ⁿ)` to `(x,x,¬x)` and keeps the two-half register weight exactly `n`.
- `copyResult_spec` and `compute_copy_uncompute_spec`: the selected midpoint
  result is copied without losing scratch or garbage, then structural inversion
  restores the exact packed scratch/source/argument block and removes the
  transient midpoint garbage.
- `compute_copy_uncompute_isReversible` and
  `compute_copy_uncompute_conservative`: the complete circuit is globally
  reversible and Hamming-weight preserving, separately from its initialized
  functional slice.
- `copyRegisterCircuit_fredkinCount`, `copyResultCircuit_fredkinCount`, and
  `computeCopyUncompute_fredkinCount`: exact one-spy-per-result-bit and
  forward-plus-inverse syntax accounting.
- `computeCopyUncompute_hasLatency_zero`: the unpadded builder preserves a
  proved zero-latency certificate only; the audit's
  `unitWireUncompute_not_meetsPaperCombinationalTiming` refutes an unsupported
  positive-latency generalization.
- `WeightLayer`, `Conservative.onWeightLayer`,
  `Conservative.ofWeightLayers`, and their round-trip laws: exact semantic
  decomposition by Hamming weight.
- `exists_conservative_extending_pair` and
  `exists_figure25_conservative`: classical noncanonical layer completion and
  Figure 25's total semantic extension.
- `direct_realization_iff`: direct monolithic same-register realizability is
  exactly bijectivity plus weight preservation, separately from fixed-basis
  synthesis.
- `Circuit.FredkinStructural`, `CleanFredkinRealization`, and
  `CleanFredkinRealizable`: one exact possibly mixed returned ancillary prefix,
  a full initialized-state equation, a no-`unitWire` basis certificate, and
  zero path latency.
- `oneControlledFredkin_spec`: the separately named common convention is built
  from paper Fredkin followed by an explicit structural data-wire swap.
- `patternMatch_spec`, `edgeClean_width_le`, `edgeWidth_le`,
  `adjacentTranspositionCircuit_spec`,
  `adjacentTranspositionCircuit_fredkinCount`, and
  `adjacentTranspositionClean`: exact local Johnson-edge semantics,
  restoration, and resource bounds.
- `Conservative.weightLayer_exchange_connected`,
  `Conservative.weightLayer_hammingTwo_connected`, and
  `singleExchangeClean`: layer connectivity and clean routed state exchanges.
- `fredkin_complete_conservative` and `clean_fredkin_realizable_iff`: classical
  existential paper-Fredkin-plus-structural-reindexing completeness, with no
  executable synthesis algorithm or global closed-form cost claim.
- `figure25_fredkin_complete`: fixed-basis synthesis of the noncanonical total
  Figure 25 completion with its additional returned workspace exposed.
- `circuit_four_even`, `middleLayerSwap_odd`, and
  `middleLayerSwap_not_circuit`: the formal width-four no-ancilla parity
  obstruction, paired with the exact small-width group audit for minimality.
- `Machine.run`, `Machine.IsTrace`, `Machine.existsUnique_trace`,
  `run_state_eq_of_input_eq_before`, and
  `run_output_eq_of_input_eq_through`: explicit synchronous initialization,
  unique traces, and input-prefix causality.
- `ConservativeMachine.tick_full`, `tick_weight_balance`, and
  `run_prefix_weight_balance`: the complete balanced open boundary plus exact
  one-tick and telescoping finite-prefix flux.
- `ConservativeMachine.tickEquiv`, `retrodictList_executeList`, and
  `retrodictListReverse_executeList`: full-tick inversion and finite open-trace
  retrodiction with every output retained.
- `ConservativeMachine.closeFeedback_step`, `closedOrbit_weight`,
  `closedIterate_reversible`, and the finite-iterate cancellation theorems:
  register-separated feedback, all-time total-state conservation, and semantic
  backward determinism for finite closed execution.
- `Network`, `DelayCell.output_succ`, and
  `DelayCell.unitWire_not_instantaneous`: the zero-latency circuit-backed
  bridge and explicit one-tick state boundary.
- `Figure8.tick`, `Figure8.characteristic`, and the hold/set/reset/toggle
  theorems: complete diagram-qualified J-Kbar semantics with visible garbage.
- `SerialAdder.paper_recurrence`, `completeTickEquiv`, and
  `no_conservative_machine`: Figure 9's conventional initialized recurrence,
  complete bijectivity, and checked failure of conservation.
- `Figure11.tick_initialized`, `state_spec`, `output_spec`, and
  `paper_recurrence`: the literal two-Fredkin `(x,0,1)` source slice, explicit
  three-bit state/output boundary, and printed delayed accumulator equation.
- `Interaction.equiv`, `Switch.equiv`, their `encode_weightPreserving`,
  `card_validOutput`, `encode_vacancies`, and `no_raw_equiv` theorems: exact
  unequal-width constrained rail interfaces with their resource distinction.
- `Collision.conservative`, `AllowedState`, `allowedEquiv`, and `map_embed`:
  the selected local `0110 <-> 1001` scattering permutation, admitted event
  subset, and exact initialized interaction slice.  The raw-map fallback is
  algebraic only.
- `ScatteringLayer.Configuration.stepEquiv`, `stepAt_commute`, and
  `totalBallCount_step`: deterministic simultaneous scattering for independent
  owned sites, not routed global mechanics.
- `Grid.fourTickDetour_reflects`, `fourTickDetour_turnPoints_injective`,
  `simultaneous_crossing_conflict`, `oneTickStagger_not_sampleClearance`, and
  `twoTickStagger_sampleClearance`: explicit sampled mirror/timing obligations.
- `Figure14.output_refines_collision`, `frame_ballCount`,
  `sampled_clearance`, and `rightAngleTurn_iff`: the complete four-tick sampled
  reconstruction, without a continuous elastic-mechanics claim.

## Indexed Stages

### 1-GUARDRAILS

**Status:** Complete (2026-07-17). The exact dependency lock, strengthened
private representation probe, focused/default builds, corrected paper map,
boundary scans, and clean rebuild evidence are recorded in
`goal-1/1-GUARDRAILS.md`.

#### Big Picture Objective

Establish a reproducible Lean environment and freeze the formal boundaries,
source map, naming conventions, and representation decisions needed by all
later stages.

#### Detailed Implementation Plan

- Inspect available Lean/mathlib versions and relevant existing APIs.
- Add pinned `lean-toolchain`, `lakefile.toml`, and the smallest compiling
  namespace/module skeleton only when this stage is explicitly started.
- Decide the Boolean-vector, Hamming-weight, reversible-map, and conservative
  map representations using small compile-checked probes.
- Convert the correction log above into durable project documentation and give
  every in-scope paper claim an intended declaration or open issue.
- Define module layering, naming, import, proof-hole, forbidden-axiom, and axiom
  audit policies. Do not add substantive definitions or proofs in setup files.

#### Completion Requirements

- Exact Lean and mathlib pins are committed and a clean `lake build` succeeds.
- A minimal test module confirms the chosen vector/`Equiv` imports compile.
- Representation decisions and rejected alternatives are recorded with checked
  reasons.
- Every core paper claim is mapped to a stage, correction, or explicit
  out-of-scope entry.
- `rg -n "sorry|admit|axiom"` has no unexplained Lean hits, and
  `git diff --check` passes.

### 2-FINITE

**Status:** Complete (2026-07-17). The finite-state API, independent semantic
predicates, closure laws, wire action, exhaustive small witnesses, focused and
clean builds, boundary scans, and axiom audit are recorded in
`goal-1/2-FINITE.md`.

#### Big Picture Objective

Build the reusable finite Boolean and conservative-equivalence foundation while
formally separating reversibility from conservation.

#### Detailed Implementation Plan

- Define fixed-width Boolean words and Hamming weight with additive lemmas for
  wire partitions.
- Bundle or predicate reversible maps and weight-preserving maps with coercions
  that do not erase their distinct obligations.
- Prove closure under identity, composition, inverse, and explicit wire
  permutations where valid.
- Give checked examples of reversible but nonconservative and conservative but
  nonreversible functions.

#### Completion Requirements

- APIs work uniformly for arbitrary finite widths, including width zero.
- Weight additivity and all closure theorems have proof terms and focused tests.
- Both independence examples are executable on their finite domains and proved
  to have exactly the claimed properties.
- Focused module builds, full build, proof-hole/axiom scan, and diff check pass.

### 3-FREDKIN

**Status:** Complete (2026-07-17). The separate unit-wire value/delay surface,
paper-ordered zero-controlled Fredkin map, structural inverse and conservation
proofs, eight-row regression audit, selected XOR-nonlinearity reconstruction,
focused/full clean builds, source scans, and axiom audits are recorded in
`goal-1/3-FREDKIN.md`.

#### Big Picture Objective

Formalize the unit wire and the paper's exact Fredkin gate and settle its truth
table, ordering, reversibility, and conservation without convention drift.

#### Detailed Implementation Plan

- Define the one-step unit-wire value semantics separately from delay metadata.
- Define Fredkin on an explicitly ordered triple `(u, x1, x2)` using the
  paper's zero-controlled swap.
- Check all eight table rows and prove control equations, involutivity,
  bijectivity, and weight preservation.
- Define coordinatewise-XOR (equivalently `F₂`) linearity in a theorem/audit
  leaf and prove the paper's nonlinearity assertion with a concrete failure of
  additivity; do not impose a heavy Boolean-ring API on the core state module.
- Keep the common one-controlled convention distinct from the paper primitive.
  Stage 9 later implements it as paper Fredkin followed by an explicit
  structural data-wire swap and proves its separately named truth table,
  basis certificate, and zero-latency theorem; no hidden control-negation
  primitive is introduced.

#### Completion Requirements

- All eight paper rows reduce or prove exactly with the documented output order.
- Separate theorems establish involution/reversibility and conservation.
- A stated XOR/`F₂` linearity predicate and checked counterexample establish
  exactly what “nonlinear” means.
- Unit-wire delay and identity-on-values are not conflated.
- Regression examples fail if the control convention or data-wire order flips.
- Focused/full builds, scans, and diff check pass.

### 4-CIRCUITS

**Status:** Complete (2026-07-17). The exact six-constructor balanced grammar,
static conservative evaluator, relational path-delay/common-latency layer,
certificate wrapper, no-cheating regressions, focused and clean builds, source
scans, and axiom audits are recorded in `goal-1/4-CIRCUITS.md`.

#### Big Picture Objective

Create arity-safe feed-forward circuit syntax and semantics whose composition
cannot perform implicit fan-out.

#### Detailed Implementation Plan

- Define primitive gates, identity, serial composition, parallel/tensor
  composition, and bijective wire permutations.
- Present the arity-indexed syntax as a corrected combinational model. Either
  prove normalization/correspondence for the paper's directed graphs or qualify
  graph-level claims; distinguish meta-level port reindexing from a synthesized
  permutation/wire circuit carrying delay.
- Encode input/output arity and linear port use so that duplication and dropping
  require explicit gates or realization interfaces.
- Define evaluation and prove semantic laws and preservation of reversibility
  and conservation.
- Add a timed feed-forward layer or well-formedness predicate for wire lengths,
  acyclicity, and equal input-output path latency.

#### Completion Requirements

- Ill-formed arity connections and nonbijective rewiring are unrepresentable or
  rejected by an explicit checker with soundness proof.
- No constructor provides contraction/fan-out or weakening/drop implicitly.
- The API and documentation identify whether each permutation is structural or
  a circuit resource; no unproved equivalence with arbitrary paper graphs is
  claimed.
- Evaluation respects identity, serial, tensor, and permutation composition.
- Well-formed conservative circuits preserve total Hamming weight.
- Timing tests distinguish acyclic unequal-latency networks from the paper's
  combinational networks.
- Focused/full builds, boundary scans, and diff check pass.

### 5-REALIZATION

**Status:** Complete (2026-07-17), from clean baseline `16562ab`. The exhaustive
interface, general constraints, exact routed Fredkin examples, negative
boundaries, focused/public/clean builds, source scans, and axiom audits are
recorded in `goal-1/5-REALIZATION.md`; Stage 6 builds on this completed boundary.

#### Big Picture Objective

Define reversible realization of ordinary finite Boolean functions with exact
constant, argument, result, garbage, and scratch interfaces.

#### Detailed Implementation Plan

- Define an explicit layout/partition abstraction and `Realizes` relation.
- Prove general injectivity/cardinality constraints imposed by reversible
  embeddings and conservation constraints imposed by total weight.
- Reconstruct AND, OR, NOT, and copy/fan-out realizations from the Fredkin gate,
  verifying every output and constant against the paper's convention.
- Distinguish ignored garbage from reusable clean scratch and state when garbage
  may depend on the argument.

#### Completion Requirements

- `Realizes` cannot hide extra inputs or outputs and handles zero-width blocks.
- Each primitive realization specifies the complete output tuple, not only the
  selected result bit.
- Copy/fan-out requires initialized auxiliary wires and proves global
  reversibility/conservation of the whole map.
- Negative tests show unrestricted `a -> (a,a)` is not treated as a reversible
  equal-arity gate.
- Focused/full builds, scans, and diff check pass.

### 6-SIMULATION

**Status:** Complete (2026-07-17). The closed finite source grammar, total
Fredkin-plus-structural-reindexing compiler, exact resources and timing,
complete Figure 7 reconstruction, adversarial audits, focused/public/full clean
builds, source scans, and axiom audits are recorded in
`goal-1/6-SIMULATION.md`.

#### Big Picture Objective

Prove a finite constructive simulation result translating an explicitly
defined ordinary feed-forward Boolean circuit grammar to conservative circuits
with constants and garbage.

#### Detailed Implementation Plan

- Define a small indexed source circuit language with explicit constants,
  discard, fan-out, serial composition, disjoint tensor, and no delay/state.
- Translate each source primitive through the stage-5 realizations, threading
  all wire blocks one-to-one.
- Prove complete semantic simulation and exact source, garbage, Fredkin-count,
  and abstract latency consequences supported by the construction.
- Handle combinational circuits first; do not infer the sequential theorem
  until stage 10 supplies feedback semantics.

#### Completion Requirements

- A structural induction proves the translation simulates every supported
  source circuit and exposes all ancilla/garbage widths.
- Fan-out in the source is translated to an explicit Fredkin construction.
- No delay-balancing algorithm is claimed: the source has no delay node and
  this compiler emits no unit wire, so the proved abstract latency is zero.
- The compiler is constructive and its exact Fredkin count is proved; no
  optimality, depth, physical routing, or asymptotic claim is inferred.
- Focused/full builds, scans, representative evaluation tests, and diff check
  pass.

### 7-INVERSE

**Status:** Complete (2026-07-17). From baseline `011b189`, Stage 7 adds the
total structural inverse, complete static inverse semantics, exact
endpoint-reversed path correspondence, common-latency preservation, and
latency-additive round trips for the corrected balanced feed-forward grammar.
Verification and boundary evidence are recorded in `goal-1/7-INVERSE.md`;
Stage 8 is now complete separately.

#### Big Picture Objective

Define inverse feed-forward networks, prove unconditional static inverse
correctness for every balanced `Circuit` term, and separately preserve exact
path and equal-latency certificates.

#### Detailed Implementation Plan

- Define syntactic inversion for every supported circuit constructor and gate.
- Reverse serial order, invert wire permutations/gates, and transform delay
  metadata without treating time reversal as Boolean negation.
- Prove inversion preserves arity and appropriate combinational
  well-formedness, and prove left/right cancellation semantically.
- Document why feedback networks require separate treatment.

#### Completion Requirements

- `eval (inverse c)` is proved equal to `(eval c).symm` for every supported
  balanced feed-forward `Circuit` term.
- Double inversion and both cancellation laws are proved.
- Equal-path/timing requirements are preserved or a precisely weaker corrected
  theorem is recorded.
- No theorem applies syntactic inversion unsafely to feedback circuits.
- Focused/full builds, scans, and diff check pass.

### 8-UNCOMPUTE

**Status:** Complete (2026-07-17), from clean synchronized baseline `ccab07c`.
The public explicit spy registers, all-width copy circuit, embedded
result-copy layer, complete compute-copy-uncompute theorem, global properties,
exact resources, corrected timing scope, adversarial regressions, and final
verification evidence are recorded in `goal-1/8-UNCOMPUTE.md`.

#### Big Picture Objective

Formalize the paper's garbageless compute-copy-uncompute construction with
complete ancilla accounting and restoration guarantees.

#### Detailed Implementation Plan

- Prove the Fredkin “spy” gadget with exact gate ports: control `a` and data
  inputs `(1,0)` produce through output `a` and data outputs `(a,not a)`.
  Separately prove any permutation from the result register's `(0^n,1^n)`
  layout to those gate ports.
- Lift copying componentwise to Boolean vectors without implicit wire reuse.
- Compose a realization, explicit copy layer, and inverse realization.
- Prove restoration of arguments, source/scratch constants, and transient
  garbage, plus the exact result-register encoding and weight preservation.

#### Completion Requirements

- The final theorem states every input and output block and proves the argument
  and scratch blocks return definitionally or propositionally unchanged.
- The `2n` result register starts with exactly `n` zeros and `n` ones and ends
  with `f x` and its bitwise complement in a documented order; the proof
  includes the wiring between register order and each Fredkin gate's data-port
  order.
- The construction uses no hidden fan-out and works for `n = 0`.
- “Garbageless” is documented as restoration of the supplied workspace and
  absence of the unnamed transient `g`; the intentionally returned argument
  and documented `(f x,not (f x))` encoding remain argument-dependent, and
  ancillary result-register wires are not absent.
- Focused/full builds, scans, axiom audit, and diff check pass.

### 9-COMPLETENESS

**Status:** Complete (2026-07-18), from clean synchronized baseline `5b28ef8`.
The paper text and Figures 24--26 were re-audited visually before the formal
contract was fixed in `goal-1/9-COMPLETENESS.md`.  At that checkpoint Stage 10
had not started; it is now complete under the separate Stage 10 report.

Current checked facts shaping the contract:

- Figure 25 gives only the initialized slice
  `(x,0^n,1^n) ↦ (x,f x,¬f x)`. Its finite total completion is noncanonical
  and must be chosen independently inside each Hamming layer.
- Figure 26c silently requires the same input/output width. Its arbitrary-gate
  sufficiency is definition-level, whereas the Fredkin-only statement is an
  unproved Silver attribution with unresolved returned-scratch and routing
  conventions.
- A dependency-free exact closure audit gives the full conservative group at
  widths one through three and index `2` at width four. Width four is therefore
  the first false no-ancilla reading in the exhaustively checked range.
- The width-four obstruction is proved structurally: every `Circuit 4`, even
  with arbitrary structural `WirePerm 4`, has global permutation sign `+1`,
  while the conservative transposition `1100 ↔ 1010` has sign `-1`.
- The positive theorem uses an explicit returned clean workspace and says
  "paper Fredkin plus structural reindexing." Structural permutations are
  zero-delay syntax in this library, not claimed to be synthesized physical
  Fredkin routing.

#### Big Picture Objective

Resolve the paper's strongest finite Fredkin-basis and scratch-space claims,
proving corrected forms and recording exact resource assumptions.

#### Implemented Result

- `Conservative.onWeightLayer` and `Conservative.ofWeightLayers` characterize
  finite conservative equivalences by Hamming-layer permutations;
  `exists_conservative_extending_pair` supplies the classical noncanonical
  completion used by `exists_figure25_conservative`.
- `CleanFredkinRealization` exposes a finite ancillary width, exact Boolean
  initialization, complete initialized-state equation, exact restoration,
  exclusion of `unitWire`, and zero path latency.
- An explicit pattern predicate, compute-copy-uncompute marker, one paper
  Fredkin, and structural routing realize each Johnson-graph edge.  Layer
  connectivity and finite permutation-group closure prove
  `fredkin_complete_conservative` at every finite width.
- `clean_fredkin_realizable_iff` records the corrected semantic boundary, and
  `figure25_fredkin_complete` keeps Figure 25's visible register separate from
  the additional returned completeness workspace.
- `circuit_four_even` and `middleLayerSwap_not_circuit` refute the false
  same-width/no-ancilla reading.  The exact group companion establishes the
  width-four minimality check through widths one to four.
- All-zero scratch conversion and the paper's asymptotic scratch/time claims
  remain explicitly unresolved because no supporting construction or cost
  model was available.

#### Completion Requirements

- `CleanFredkinRealization` records the selected width, exact ancillary
  initialization, full circuit, permitted-basis certificate, zero latency, and
  complete `clean ++ data ↦ clean ++ gate(data)` equation.  There is no unnamed
  garbage block; the named ancillary prefix is returned exactly.
- Small-width exhaustive checks agree with the general statement and guard
  against convention mistakes, but the general proof is not mere enumeration.
- Any false stronger reading has a minimal checked counterexample.
- All-zero scratch and asymptotic claims are either proved under formal cost
  definitions or remain clearly marked unresolved with concrete next work.
- Main theorem `#print axioms`, focused/full builds, scans, and diff check pass.

### 10-SEQUENTIAL

**Status:** Complete (2026-07-18), from clean synchronized baseline `29723da`.
The paper text and Figures 3, 8--11, and 19 were re-audited before the corrected
contract was fixed in `goal-1/10-SEQUENTIAL.md`.  The opt-in semantics, paper
examples, audit, scans, and post-clean finite/sequential builds pass.  At Stage
10 completion, no Stage 11 work had begun.

Current contract decisions:

- A tick has the explicit time convention
  `state(t), input(t) -> state(t+1), output(t)`, with initialization supplied by
  the caller and a unique causal trace.
- An open conservative transition is one complete permutation
  `memory ++ input <-> nextMemory ++ output`; its theorem is a total flux law,
  not preservation of memory weight alone.
- Feedback is register-separated.  Delayed closure stores the former output
  and consumes it at the next tick; no simultaneous fixed-point constructor is
  admitted.
- A feed-forward `Circuit` can serve as a within-tick core only with a proved
  zero-latency certificate.  Static evaluation of `Circuit.unitWire` must not
  be mistaken for execution of its stored value.
- Figure 8 is checked as the full conservative tick
  `(q,Kbar,J) -> (if q then Kbar else J, q, if q then J else Kbar)`.  Figure 9
  is a conventional recurrence whose full transition is bijective but not
  conservative.  Figure 11 is checked as a literal two-Fredkin network with
  three stored wires, fresh `(x,0,1)` per tick, all outputs, and its printed
  recurrence.  Figure 10's factor-five schedule and the general sequential
  compiler remain unsupported resource/simulation claims.

#### Big Picture Objective

Add a separate discrete sequential-circuit semantics with delays and feedback,
then determine exactly which paper simulation and inverse claims extend to it.

#### Implemented Result

- `Machine`, `Run`, and `Signal` give the exact
  `state(t),input(t) -> state(t+1),output(t)` convention.  Canonical execution,
  relational trace existence/uniqueness, strict-prefix state causality, and
  through-current-tick output causality are proved.
- `ConservativeMachine` packages one complete
  `memory ++ input ↔ nextMemory ++ output` permutation.  `tick_weight_balance`
  gives one-tick flux and `run_prefix_weight_balance` telescopes it over every
  finite prefix.  `tickEquiv` retains the complete inverse boundary.
- `executeList` and `retrodictList` prove finite open-run recovery from terminal
  memory and every complete output.  This is backward determinism, not graph or
  physical time reversal.
- `closeFeedback_step` formalizes register-separated closure: the former output
  occupies the loop-register block consumed on the next tick.  Closed orbits
  preserve complete weight at all natural times; explicit finite iterates are
  equivalences with both cancellation directions.
- `Network` admits an existing acyclic `Circuit` only with `HasLatency core 0`.
  The structural-swap `DelayCell` proves explicit initialization and the exact
  one-tick offset, while `unitWire_not_instantaneous` rejects the static
  positive-delay constructor at this bridge.
- `Figure8.tick` and `characteristic` verify the complete J-Kbar transition,
  visible garbage, initialization, all rows, and four standard modes.
- `SerialAdder.paper_recurrence` verifies Figure 9, while its complete tick is
  proved bijective and concretely nonconservative.
- `Figure11.tick_initialized`, `state_spec`, `output_spec`, and
  `paper_recurrence` verify the literal six-wire, two-Fredkin source slice,
  three stored wires, all external outputs, and
  `Y(t+2)=Y(t+1) xor X(t)`.
- `ConservativeLogic.Sequential` is opt-in and absent from the finite API/root.
  The adversarial audit checks zero widths, causality, initialization,
  open/closed counterexamples, delayed loops, retrodiction, and all examples.
  No general sequential compiler, Figure 10 schedule, Figure 19 graph
  elaboration, NAND-complexity, or physical conclusion is installed.

#### Detailed Implementation Plan

- Define deterministic machines, input/output signals, explicit
  initialization, canonical runs, relational traces, uniqueness, and prefix
  causality.
- Define balanced conservative machines on the complete joint boundary and
  prove the exact one-tick flux law and full-tick equivalence.  Separately
  define delayed closure, closed iteration, total-state conservation, and
  finite-iterate reversibility.
- Admit a circuit-backed within-tick network only from an acyclic
  `HasLatency 0` core.  Give a structural-swap delay cell a genuine one-tick
  trace semantics and reject positive-delay `Circuit.unitWire` at this bridge.
- Reconstruct Figures 8 and 11 with all state, source, selected, and garbage
  wires visible; check Figure 9's printed recurrence while proving that it is
  not itself a conservative transition.
- Revisit translation, Figure 19, and closed-computer claims without importing
  combinational inverse results blindly or converting per-invocation constants
  and garbage into unmentioned infinite resources.
- State latency/throughput/resource claims only when supported by a formal
  timing model.

#### Completion Requirements

- Feedback has a total, deterministic tick semantics with no instantaneous
  algebraic loops, and the accepted register-separated class is characterized
  explicitly.
- Closed conservative transitions preserve total state weight; reversibility is
  separately proved where valid.
- At least one paper sequential example is verified against a precise trace
  specification if its diagram can be reconstructed reliably.
- Unsupported comparable-complexity or multiplexing claims remain documented,
  not theoremized.
- Focused/full builds, trace tests, scans, and diff check pass.

### 11-BILLIARD

**Status:** Complete (2026-07-18), from clean synchronized baseline `898bfe5`.
The Section 6 text, footnotes, and original Figures 12--18 were re-audited.
They invoke continuous hard balls and fixed plane mirrors
sampled at integral times, but do not give a total discrete global transition:
occupancy lacks directed velocity, and multi-contact/simultaneous-event
behavior is unspecified.  Figure 14 has enough endpoint and timing information
for a narrow four-tick sampled refinement.  Figures 17--18 do not expose all
steering, delay, clearance, and crossover data needed for such a theorem.

Current corrected contract:

- Define the interaction and switch as heterogeneous equivalences from two
  input bits onto their exact four-state valid-output subtypes.  Prove separate
  ball-count preservation and raw-interface cardinality obstructions; do not
  use the equal-width `Conservative` structure.
- Supply a deterministic involutive collision-site step only on an explicit
  legal phase/state subtype.  A finite product means independent simultaneous
  sites and does not silently provide routing or continuous mechanics.
- Model directed diagonal sampled routes, axis-mirror turns, finite detours,
  sampled clearance, and time-indexed crossover conflicts.  A delayed crossing
  needs both an explicit no-same-place/same-time proof and the selected sampled
  clearance threshold before it can support even a sampled-clearance claim;
  neither establishes continuous clearance.
- Reconstruct Figure 14 as four unit diagonal ticks and prove its complete
  input/output rail refinement, exact latency, ball count, legal sampled
  frames, and scheduled right-angle direction changes.
- Record a checked under-specification boundary for raw illegal collision
  states and for the timing/layout data that Figure 18 says are not explicitly
  indicated.  Do not claim the radius-`1/√2` continuous dynamics, nontrivial
  bridge gadget, Figures 17--18,
  arbitrary conservative-circuit layout, physical reversibility, or
  thermodynamics.

#### Big Picture Objective

If practical, formalize the billiard-ball model as a discrete computational
model and prove refinement of selected collision networks to conservative gates.

#### Implemented Result

- `Billiard.Interaction` and `Billiard.Switch` give the exact paper tables as
  equivalences onto four-state valid-output subtypes, with selected inverses,
  ball-count laws, vacancy deltas, and raw unequal-width cardinality
  obstructions.  No constrained rail interface is mislabeled as an
  equal-width `Conservative` endomap.
- `Billiard.Collision` gives the selected `0110 <-> 1001` involution.  Its raw
  identity fallback is only an algebraic completion; executable scattering is
  restricted to `AllowedState`.  The initialized slice refines the interaction
  table, while explicit tests rule out illegal three-ball events, independent
  singleton superposition, and a structural wire-permutation explanation.
- `Billiard.ScatteringLayer` provides deterministic, involutive,
  count-preserving products of independently owned local sites, plus commuting
  distinct-site updates and a shared-particle support obstruction.  It does
  not claim a routed global mechanics.
- `Billiard.Grid` certifies directed unit sampled routes, fixed mirror turns,
  route timing, and integral-sample separation.  The checked examples
  distinguish simultaneous conflict, one-tick center noncoincidence that still
  fails radius-derived clearance, and a two-tick schedule that meets it.  The
  finite detour preserves endpoint positions but not boundary directions, so
  it is not installed as a general delay gadget.
- `Billiard.Figure14` is an explicit four-tick selected scheduled trace.  All
  input rows, frames, directions, output rails, ball counts, sampled clearance,
  the unique contact tick, and the conditional right-angle turn are checked.
  It is an endpoint/sampled-path refinement, not execution under continuous or
  total global dynamics.
- The billiard umbrella remains opt-in and outside both the finite and
  sequential APIs.  Figures 15, 17, and 18, between-sample mechanics,
  compositional physical layout, physical reversibility, and thermodynamics
  remain explicit unresolved boundaries.
- Focused/default/opt-in builds, an uncontended clean default rebuild and
  explicit post-clean audit builds, exhaustive row checks, completeness-group
  regression, forbidden-shortcut scans, axiom inspection, adversarial review,
  complete baseline diff inspection, and `git diff --check` pass.  Detailed
  evidence and repaired review findings are recorded in `11-BILLIARD.md`.

#### Detailed Implementation Plan

- Define a discrete grid, legal signals, mirrors, time steps, collision events,
  and global configurations with explicit exclusion/simultaneity conditions.
- Model the interaction gate on its constrained interface and prove
  reversibility and conservation of the discrete step relation/map.
- Formalize routing, delay, and crossover gadgets before the switch or Fredkin
  layouts.
- Treat the paper's geometry as diagrams needing reconstruction; do not assert
  continuous elastic mechanics or thermodynamics.

#### Completion Requirements

- The step semantics is proved well-defined on an explicit legal-state subset.
- The interaction interface has exactly the valid states claimed and its
  inverse uses the same constraint.
- Any formalized layout has a machine-checked refinement theorem to its logical
  gate and a timing statement.
- If the model is impractical, a checked obstruction and narrower discrete
  alternative are recorded instead of an invented proof.
- Isolated module builds, full build, scans, and diff check pass.

### 12-AUDIT

**Status:** In progress (2026-07-18), from clean synchronized baseline
`1047322`.  Repository-wide paper/correction, API/import, and adversarial audit
passes are underway before the final examples and axiom leaves are fixed.

#### Big Picture Objective

Finish the reusable API and produce an evidence-backed correspondence between
the paper, corrected Lean theorems, unresolved issues, and assumptions.

#### Detailed Implementation Plan

- Stabilize declaration names, namespaces, docstrings, minimal imports, and the
  thin public API.
- Update the paper map and correction log with exact declaration links and
  dispositions.
- Add representative examples and an axiom-audit module for all main results.
- Validate from a clean checkout and document exclusions, especially physical
  claims and any deferred billiard/sequential/resource results.

#### Completion Requirements

- Every in-scope paper claim maps to a built declaration, a documented corrected
  theorem, a checked disproof, or a clearly unresolved item.
- Public modules contain no proof holes, unexplained project axioms, accidental
  diagnostic dependencies, or hidden fallback implementations.
- `lake build`, focused examples/tests, proof-hole and forbidden-shortcut scans,
  `#print axioms` audits, and `git diff --check` all pass from a clean checkout.
- The README explains the formal model, convention differences, API entry
  points, theorem map, limitations, and reproduction commands.
- Completion is judged against the original objective, not merely green builds.
