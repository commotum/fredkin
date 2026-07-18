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
- An inverse network theorem must require enough structural and timing data to
  make reversal well-defined.
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
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`. On 2026-07-17, the guardrail,
  finite, and Fredkin audit targets, every Stage 2 and Stage 3 stable leaf, and
  an uncontended clean default `lake build` succeeded against the locked
  dependency tree.
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
- The strongest fixed-basis claim says every finite invertible conservative
  function is realizable without garbage using Fredkin gates. The paper
  attributes this to B. Silver but does not give the proof or state the ancilla
  convention with enough precision in the immediate claim.

### Assumptions to Test, Not Yet Facts

- A typed circuit syntax indexed by input/output arity, with explicit wire
  permutations and tensor/serial composition, is expected to prevent implicit
  fan-out. Stage 1 fixed the boundary constraints, but the exact syntax remains
  deliberately unsettled until stage 4.
- Combinational semantic maps may be modeled separately from timed graphs; a
  semantics-first core plus a realizability relation may be more reusable than
  making all proofs depend on graph syntax.
- Fredkin completeness for all weight-preserving permutations may require
  clean ancillas that are returned, arbitrary wire permutations, or both. The
  no-ancilla fixed-width interpretation must not be assumed.
- The paper's claim that an all-zero scratchpad loses no generality and its
  stated linear lower/upper scratch bounds require reconstruction from other
  sources or fresh proofs.
- A billiard-ball formalization is practical only if collision states,
  simultaneous events, mirrors, routing clearance, and discrete-time evolution
  can be specified without smuggling in continuous-mechanics assumptions.

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
| §2.2, P4–P6 | Separate delayed identity, reversible maps, and one-to-one composition | 2–5, 10 | Formalize the discrete content separately; the paper's physical motivations are not consequences of these definitions |
| §2.2, P7 | The abstract model should have at least one additive conserved quantity | — | Generic physical/mathematical motivation only; P7 itself does not select Hamming weight |
| §§2.3–2.5 | In the Boolean model, `N₁`/Hamming weight is additive across wire portions and preserved by unit wires, gates, and closed transitions | 2–4, 10 | Stage 2 proves static block additivity; Stage 3 proves static preservation by `UnitWire.value` and `PaperFredkin.map`; circuit composition and closed trajectories remain Stage 4/10 obligations |
| §2.2, P8 | Local-Euclidean/layout constraint on circuit connectivity | 11 or — | The paper explicitly does not develop P8; require an actual geometry model or keep the claim out of scope |
| §2.3 | Unit wire is delayed identity, reversible, and conservative | 3, 4 | `UnitWire.value_apply`, `value_isReversible`, and `value_weightPreserving` prove the aligned identity-on-values claim; `UnitWire.delay_eq_one` records one abstract time step only, while timed composition and oriented reversal remain later semantics |
| §2.4, Table (2) | Paper-convention Fredkin semantics, involution, bijection, weight preservation | 3 | `PaperFredkin.table` fixes the port order and convention; all eight rows are independently audited; `map_involutive`, `equiv`, `map_isReversible`, `map_weightPreserving`, and `conservative` prove the separate static properties |
| §2.4 | Fredkin is nonlinear under an explicitly selected coordinatewise-XOR/`F₂` notion | 3 | `XorLinear` states the selected reconstruction; the `PaperFredkin.map_xor_counterexample_*` equations and `map_not_xorLinear` prove a concrete failure of additivity, without attributing that definition to the paper |
| §2.5, Fig. 3 | Literal directed-graph open/closed transition semantics, feedback, memory, balanced external ports, and closed-system weight conservation | 10 | The paper's graph model is not feed-forward; it needs explicit state and feedback semantics |
| §§2.5, 7.1 | Acyclic/equal-latency combinational fragment and one-to-one composition | 4, 7 | Typed syntax may be a corrected fragment, not the literal graph model, absent a proved correspondence |
| §2.5 | Reversibility and conservation are independent | 2 | Proved semantically for ordinary Boolean endomaps by `Independence.reversible_not_weightPreserving` and `Independence.weightPreserving_not_reversible`; this does not assert a literal circuit realization |
| §3, Fig. 5 | Realization partitions source/argument and result/sink, fixes constants independently of the argument, and permits argument-dependent garbage | 5 | Central interface definition; every partition must be explicit |
| §3, Figs. 4–6 | Fredkin realizes AND, OR, NOT, and fan-out with constants/garbage | 5 | Ordering and interfaces must be reconstructed from figures |
| §3, Fig. 7 | Demultiplexer semantics include the complete output and address-echo garbage; argument-to-result paths have equal delay | 4, 6 | The paper does not establish equal delay for every source/sink path; reconstruct the exact function and latency scope |
| §3, Fig. 8 | Reconstruct a transition/trace specification for the asserted `J-K̄` flip-flop realization | 10 | The paper supplies only the assertion and diagram, not a transition equation or trace |
| §4 | Conventional finite combinational networks can be translated to conservative networks using constants and garbage | 6 | Corrected finite feed-forward target; needs a source language and delay normalization |
| §4 | Arbitrary conventional sequential networks can be simulated by conservative sequential networks | 10 | Paper argument is informal; requires state/feedback semantics and an exact simulation relation |
| §4, Figs. 9–11 | Serial-adder simulation includes initialization and stream semantics | 10 | Factor-5 slowdown, time multiplexing, and source/sink counts are separate resource obligations |
| §4 | Turing-machine/cellular-automaton universality | — | Out of verified core unless separately scoped |
| §6.1 | Discrete billiard states use a unit grid, radius `1/√2`, unit velocity, integral observation times, and a restriction to right-angle collisions | 11 | Requires a legal-state and simultaneous-event semantics before any refinement theorem |
| §6.2 | `(p,q) ↦ (pq, ¬p q, p ¬q, pq)` is an equivalence onto four valid rail states and preserves ball count | 11 | Heterogeneous constrained interface, not an ordinary equal-width gate |
| §6.3 | Interaction-gate AND/NOT realization plus universality with constants and valid routing/timing | 11 | Logical realization and geometric implementability are separate |
| §6 introduction and §6.4 | Any conservative-logic circuit has a billiard-ball realization | 11 | Strong whole-circuit refinement claim; primitive truth tables alone do not prove routing, clearance, or timing composition |
| §6.4, Figs. 16–18 | The switch `(c,x) ↦ (c,cx,¬c x)` is an equivalence onto four valid three-rail states, and collision layouts refine switch/Fredkin semantics | 11 | Switch inverse is constrained; Fig. 18 omits steering/timing mirrors and unit wires while explicitly classifying bridge versus trivial crossovers |
| §7.1 | Reversing gates and wires yields a semantic inverse for combinational networks | 7 | Requires acyclicity and delay/path discipline |
| §7.1, Figs. 22–24 | Compute-copy-uncompute returns argument and scratch and emits `(y, not y)` | 8 | Exact copy gadget and partitions must be proved |
| §7 introduction, §§7.1–7.2 | Garbage can be reduced to a returned copy of the argument, with claimed line-count and circuit-complexity consequences | 8, 9 | Separate restoration semantics from scratch/garbage size and complexity bounds; the latter need a cost model |
| §7.1, Fig. 24(b) | Scratch constants can all be zero without loss of generality | 9 | Attributed but unproved in paper |
| §7.2, Fig. 25 | For any `f`, the initialized-slice map `(x,0ⁿ,1ⁿ) ↦ (x,f x,¬f x)` extends to a total conservative permutation | 5, 9 | Requires a finite weight-layer extension theorem; the figure does not define the total map |
| §7.2 | Arbitrary computation needs scratch for a fixed primitive set; claimed size tradeoffs | 9 | Quantifiers and complexity model unclear |
| §7.3, Fig. 26 | Direct same-register semantic realization is characterized by invertibility plus conservation | 9 | Keep this arbitrary-gate statement separate from fixed-basis synthesis |
| §§2.5, 7.3 | Every invertible conservative finite function, and its iterates, are Fredkin-realizable without garbage | 9 | Central, but wire-permutation/ancilla scope is ambiguous; the paper tacitly includes unit wires and identity gates in realizability claims |
| §7.3 | Closed general-purpose computers have NAND-comparable gate complexity | 10 | External thesis/complexity model required; not core |
| Abstract and physical passages in §§1–2, 5–10 | Zero dissipation, entropy, energy, noise, topology, and physical-realizability conclusions | — | Documentation only absent explicit physical state, dynamics, and thermodynamic models |

## Correction and Uncertainty Log

Entries remain open until a stage records checked evidence and a final
disposition.

| ID | Issue | Required disposition |
|---|---|---|
| CL-001 | The paper uses zero-controlled swapping, opposite to the common modern Fredkin convention. | Resolved for the Stage 3 default by the explicit `PaperFredkin` namespace, public coordinate laws, `PaperFredkin.table`, and all eight audited rows. No one-controlled alternate is exposed; any future alternate still requires a separately named control-negation conjugacy theorem. |
| CL-002 | “Inverse wire” mixes identity-on-values with reversal of time/orientation, while footnote 3 separately warns that invertibility does not imply time-reversal invariance. | Partially resolved in Stage 3: `UnitWire.value` and `UnitWire.delay` separate aligned value identity from one-step metadata, while `PaperFredkin.map_involutive` concerns only a static gate map. Oriented network reversal and physical time-reversal symmetry remain explicit later obligations. |
| CL-003 | Reversibility and bit conservation are asserted independent, with external citations but no small witness or proof in the paper. | Resolved for the semantic predicate claim in Stage 2 by one-bit negation and two-bit Boolean sorting. The latter is documented only as an ordinary endomap, not a conservative-logic gate or literal circuit realization. |
| CL-004 | FAN-OUT is shown diagrammatically although arbitrary copying is not reversible. | State a constrained ancilla interface and account for every output. |
| CL-005 | Figure 7 states equal delay only from argument to result, whereas §7.1 defines a combinational network using equal delay from any input to any output. | Decide whether all-path equal latency is intrinsic syntax, a well-formedness predicate, or a retiming theorem; do not promote Figure 7's narrower statement to source/sink paths without checking them. |
| CL-006 | The §4 universality argument translates ordinary sequential circuits informally and handwaves delay normalization. A combinational translation cannot establish its stateful or resource claims. | Formalize source transition, initialization, scheduling, and noninterference semantics before the sequential theorem; state slowdown/time-multiplexing bounds separately from semantic simulation. |
| CL-007 | The interaction and switch gates use constrained, unequal-width rail encodings. They preserve balls/ones but not the number of zero-valued physical rails and are exceptions to the ordinary balanced-port gate type. | Model each valid-state subtype explicitly; never claim `Bool² ≃ Bool⁴`, `Bool² ≃ Bool³`, or an ordinary equal-width conservative-gate instance. Qualify port-balance claims accordingly. |
| CL-008 | Figure 18 explicitly omits steering/timing mirrors and unit wires, but identifies bridge crossovers and calls the others trivial; clearance and simultaneous collision scheduling are additional formalization obligations rather than quoted omissions. | Model the stated omissions, crossover cases, clearance, and event scheduling explicitly in a discrete geometry semantics. |
| CL-009 | The spy/copy gadget needs one `0` and one `1` per copied result bit and emits both value and complement; with Table (2)'s `(u,x1,x2)` order, `(x1,x2)=(1,0)` yields `(y1,y2)=(a,not a)`. | Make the gate-port wiring, any surrounding permutation, and the `2n`-wire result encoding explicit rather than reading vertical order from Figures 6(c) or 22. |
| CL-010 | “Garbageless” still returns the original argument and uses/restores scratch. | Define garbage relative to named interfaces; do not mean “no extra outputs whatsoever.” |
| CL-011 | All-zero scratch sufficiency is attributed to Margolus without proof. | Reconstruct a proof, cite a verifiable source, or leave the stronger version unresolved. |
| CL-012 | Scratchpad size claims use informal proportionality and an unstated cost model. | Define a circuit family and asymptotic measure before formalizing them. |
| CL-013 | “Any invertible conservative function” is Fredkin-realizable, attributed to Silver, but ancilla and wiring conventions are unclear; §2.5 also tacitly includes unit wires and identity gates in every realizability basis. | Prove the strongest accurate variant and document required ancillas/permutations and whether unit wires/identity are free basis elements. |
| CL-014 | Figure 25 specifies `F0` only on initialized inputs `(x,0ⁿ,1ⁿ)`; total invertibility and conservation do not follow “by definition,” and arbitrary-gate existence would not imply fixed-basis synthesis. | Prove the slice map injective and weight preserving, extend it independently within each finite Hamming layer to a total permutation, document that the completion is noncanonical, and keep semantic gatehood separate from Fredkin synthesis. |
| CL-015 | Claims about infinite blank tape/environment supplying constants and garbage space are not finite-circuit theorems. | Exclude or formalize in a separately scoped infinite model. |
| CL-016 | Physical reversibility, entropy, and zero-dissipation conclusions do not follow from finite bijections alone. | Keep them non-theorem commentary unless physical state and dynamics are formalized. |
| CL-017 | A serial/tensor/permutation syntax is not literally the paper's directed-graph circuit model, which includes feedback and open transducers with memory; structural wire renaming is also not automatically a physical wire/permutation circuit with delay. | Either prove a graph-fragment normalization/correspondence theorem or label the syntax as a corrected feed-forward semantic model; expose which wire permutations are free versus synthesized in completeness theorems. |
| CL-018 | The paper calls Fredkin nonlinear without naming the algebraic structure. | Resolved for one explicit reconstruction by `BitState.xor`, `BitState.falseState`, `XorLinear`, the named `PaperFredkin.map_xor_counterexample_*` equations, and `PaperFredkin.map_not_xorLinear`. This is not presented as the paper's missing definition or as physical nonlinearity. |
| CL-019 | Figure 8 is asserted to realize a `J-K̄` flip-flop, but the paper gives no transition equation, initialization condition, or trace specification. | Reconstruct and verify an exact sequential specification from the diagram, or leave the example explicitly unresolved. |

## Dependency Notes and Tentative Module Direction

Stage 1 selected matching stable Lean/mathlib release tags `v4.32.0` (published
2026-07-13). `formal/lean-toolchain` pins Lean, `formal/lakefile.toml` pins
mathlib by tag, and `formal/lake-manifest.json` locks mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. The private probe uses narrow
imports `Mathlib.Data.Fintype.Pi`,
`Mathlib.Logic.Equiv.Basic`, `Mathlib.Logic.Equiv.Fin.Basic`, plus
`Mathlib.Data.BitVec` solely to audit the rejected packed alternative.

Tentative low-to-high dependency layout (names provisional):

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
  Realization/Core.lean     -- constants/arguments/results/garbage partitions
  Realization/Primitive.lean
  Circuit/Inverse.lean
  Ancilla/Uncompute.lean
  Universality/Fredkin.lean
  Sequential/Core.lean      -- separate transition/feedback semantics
  Billiard/Discrete.lean    -- optional, late, isolated from the verified core
  Audit/Main.lean           -- theorem map, examples, `#print axioms`
  API.lean                  -- thin public re-export
```

Keep core definitions below proof-heavy universality and audit leaves. The
optional sequential and billiard modules must not become dependencies of the
finite combinational API. Use `fredkin-1982/BUILD-PLAN.md` for incremental build
discipline once Lean code exists.

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
- `Circuit.eval_id`, `Circuit.eval_seq`, `Circuit.eval_tensor`, and
  `Circuit.eval_permute`: compositional semantics.
- `Circuit.eval_reversible` and `Circuit.eval_conservative`: preservation from
  well-formed primitives and one-to-one wiring.
- `Realizes`: an explicit relation partitioning constant/argument inputs and
  result/garbage outputs.
- `fredkin_realizes_and`, `fredkin_realizes_or`,
  `fredkin_realizes_not`, `fredkin_realizes_copy`: primitive embeddings with
  exact constants and garbage.
- `Circuit.inverse_eval`: evaluation of an inverse feed-forward circuit is the
  inverse equivalence.
- `copyPair_spec`: in the paper's exact gate-port order, initialized `(1,0)`
  data targets become `(a, not a)` while the control/through wire retains `a`;
  relate this explicitly to the result register's chosen layout.
- `compute_copy_uncompute_spec`: argument and scratch return unchanged, with
  the result block encoding `(f x, bitwiseNot (f x))`.
- `compute_copy_uncompute_conservative`: the full construction preserves total
  Hamming weight.
- `fredkin_complete_conservative`: a carefully scoped synthesis theorem for
  finite weight-preserving permutations, with all clean ancillas and wire
  permutations exposed.
- `direct_realization_iff`: characterize direct same-register realizability,
  separately from fixed-Fredkin-basis synthesis.
- `TimedCircuit.inverse_wellFormed`: reversal preserves the selected acyclic
  equal-latency well-formedness condition.
- Optional `Billiard.step_reversible` and `interactionGate_refines_collision`:
  discrete model results only after collision well-definedness is proved.

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
- If useful, define the common one-controlled variant and prove the precise
  control-negation conjugacy; keep it out of the default paper API.

#### Completion Requirements

- All eight paper rows reduce or prove exactly with the documented output order.
- Separate theorems establish involution/reversibility and conservation.
- A stated XOR/`F₂` linearity predicate and checked counterexample establish
  exactly what “nonlinear” means.
- Unit-wire delay and identity-on-values are not conflated.
- Regression examples fail if the control convention or data-wire order flips.
- Focused/full builds, scans, and diff check pass.

### 4-CIRCUITS

**Status:** Next incomplete stage.

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

#### Big Picture Objective

Prove a finite, honest universality result translating an explicitly defined
ordinary Boolean circuit language to conservative circuits with constants and
garbage.

#### Detailed Implementation Plan

- Define or reuse a small source circuit language with explicit fan-out and,
  only if included, explicit delays/state.
- Translate each source primitive through the stage-5 realizations, threading
  all wire blocks one-to-one.
- Prove semantic simulation and state exact source, garbage, gate-count, depth,
  and latency consequences supported by the construction.
- Handle combinational circuits first; do not infer the sequential theorem
  until stage 10 supplies feedback semantics.

#### Completion Requirements

- A structural induction proves the translation simulates every supported
  source circuit and exposes all ancilla/garbage widths.
- Fan-out in the source is translated to an explicit Fredkin construction.
- Any delay balancing algorithm terminates and proves equal-latency output.
- The theorem is labeled existential unless verified cost bounds are included.
- Focused/full builds, scans, representative evaluation tests, and diff check
  pass.

### 7-INVERSE

#### Big Picture Objective

Define inverse feed-forward networks and prove that reversal really implements
the inverse semantic map under explicit structural/timing hypotheses.

#### Detailed Implementation Plan

- Define syntactic inversion for every supported circuit constructor and gate.
- Reverse serial order, invert wire permutations/gates, and transform delay
  metadata without treating time reversal as Boolean negation.
- Prove inversion preserves arity and appropriate combinational
  well-formedness, and prove left/right cancellation semantically.
- Document why feedback networks require separate treatment.

#### Completion Requirements

- `eval (inverse c)` is proved equal to `(eval c).symm` for all supported
  well-formed reversible combinational circuits.
- Double inversion and both cancellation laws are proved.
- Equal-path/timing requirements are preserved or a precisely weaker corrected
  theorem is recorded.
- No theorem applies syntactic inversion unsafely to feedback circuits.
- Focused/full builds, scans, and diff check pass.

### 8-UNCOMPUTE

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
- “Garbageless” is documented as restored scratch/no argument-dependent garbage,
  not absence of all ancillary wires.
- Focused/full builds, scans, axiom audit, and diff check pass.

### 9-COMPLETENESS

#### Big Picture Objective

Resolve the paper's strongest finite Fredkin-basis and scratch-space claims,
proving corrected forms and recording exact resource assumptions.

#### Detailed Implementation Plan

- Characterize finite conservative equivalences as permutations within Hamming
  weight layers.
- Analyze the group generated by embedded Fredkin gates and explicit wire
  permutations at fixed width; search for small counterexamples to overly strong
  no-ancilla readings.
- Construct a synthesis proof for the strongest valid theorem, exposing clean
  ancilla initialization/restoration and any constants or permutations.
- Separately investigate all-zero scratch conversion and claimed asymptotic
  scratch bounds after defining a cost model.

#### Completion Requirements

- The completeness theorem has explicit quantifiers over width, ancilla count,
  initialization, returned scratch, permitted wiring, and garbage.
- Small-width exhaustive checks agree with the general statement and guard
  against convention mistakes, but the general proof is not mere enumeration.
- Any false stronger reading has a minimal checked counterexample.
- All-zero scratch and asymptotic claims are either proved under formal cost
  definitions or remain clearly marked unresolved with concrete next work.
- Main theorem `#print axioms`, focused/full builds, scans, and diff check pass.

### 10-SEQUENTIAL

#### Big Picture Objective

Add a separate discrete sequential-circuit semantics with delays and feedback,
then determine exactly which paper simulation and inverse claims extend to it.

#### Detailed Implementation Plan

- Define state, one-tick transition, open input/output streams, initialization,
  and closed-system iteration for well-formed feedback networks.
- Establish determinism, port balance, state-weight invariants, and conditions
  for reversible global transitions.
- Revisit the flip-flop, serial-adder, translation, and closed-computer claims
  without importing combinational inverse results blindly.
- State latency/throughput/resource claims only when supported by a formal
  timing model.

#### Completion Requirements

- Feedback has a total, deterministic tick semantics with no instantaneous
  algebraic loops, or the accepted class is characterized explicitly.
- Closed conservative transitions preserve total state weight; reversibility is
  separately proved where valid.
- At least one paper sequential example is verified against a precise trace
  specification if its diagram can be reconstructed reliably.
- Unsupported comparable-complexity or multiplexing claims remain documented,
  not theoremized.
- Focused/full builds, trace tests, scans, and diff check pass.

### 11-BILLIARD

#### Big Picture Objective

If practical, formalize the billiard-ball model as a discrete computational
model and prove refinement of selected collision networks to conservative gates.

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
