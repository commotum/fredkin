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
- The repository currently contains only a placeholder Python project
  (`pyproject.toml`, `main.py`). It has no Lean toolchain pin, Lake manifest,
  mathlib dependency, Lean modules, or Lean tests.
- This scaffold creates documentation only. The scaffolding skill requires
  exactly `0-plan.md`, `0-loop.md`, and `0-prompt.md`; it does not require or
  authorize a Lean setup file at this stage.

### Checked Paper Facts

- The paper defines a unit wire as a one-step delayed identity bit.
- Its Fredkin table maps `(u, x1, x2)` to `(u, x2, x1)` when `u = 0` and to
  `(u, x1, x2)` when `u = 1`. Thus the printed control convention is
  zero-controlled swapping.
- A conservative gate is described as an invertible Boolean function that
  preserves the number of ones. The paper explicitly notes that reversibility
  and conservation are independent.
- Composition forbids implicit fan-out. Source constants and discarded sink
  outputs are used to realize noninvertible Boolean functions.
- The paper's circuit model is time-discrete. Wires carry delay; feedback gives
  sequential behavior. Its definition of a combinational network additionally
  requires no feedback and equal unit-wire path lengths from inputs to outputs.
- The interaction gate in the billiard model has constrained four-rail outputs:
  only four of the sixteen Boolean states are valid. Its inverse therefore has
  a partial/constrained input interface.
- The garbageless construction runs a realization, copies each result bit using
  constants `0` and `1`, and runs the inverse. It returns the argument and
  scratch constants and produces both `y` and `not y`.
- The strongest fixed-basis claim says every finite invertible conservative
  function is realizable without garbage using Fredkin gates. The paper
  attributes this to B. Silver but does not give the proof or state the ancilla
  convention with enough precision in the immediate claim.

### Assumptions to Test, Not Yet Facts

- `Fin n -> Bool` is likely the simplest public representation of an `n`-bit
  word; `Vector Bool n` or a finite-set representation may be preferable at API
  boundaries after checking mathlib ergonomics.
- Reversible maps should likely use `Equiv`, with a bundled conservative
  subtype/structure carrying a weight-preservation proof.
- Hamming weight can likely be defined by filtering `Finset.univ`, but existing
  mathlib Boolean-vector/Hamming-weight APIs must be checked first.
- A typed circuit syntax indexed by input/output arity, with explicit wire
  permutations and tensor/serial composition, is expected to prevent implicit
  fan-out. The exact syntax is deliberately unsettled until stage 1.
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

| Paper location | Reconstructed formal target | Planned stage | Initial status |
|---|---|---:|---|
| §2.3 | Unit wire is delayed identity, reversible, and conservative | 2, 4 | Precise after choosing time semantics |
| §2.4, Table (2) | Paper-convention Fredkin semantics, involution, bijection, weight preservation | 3 | Truth table checked; proof pending |
| §2.5 | One-to-one circuit composition preserves port balance and global weight | 4 | Graph/timing details underspecified |
| §2.5 | Reversibility and conservation are independent | 2 | Needs explicit finite witnesses |
| §3, Figs. 4–6 | Fredkin realizes AND, OR, NOT, and fan-out with constants/garbage | 5 | Ordering and interfaces must be reconstructed from figures |
| §3, Figs. 7–8 | Demultiplexer and flip-flop examples | 6, 10 | Deferred; timing/feedback must be explicit |
| §4 | Conventional finite networks can be translated to conservative networks using constants and garbage | 6 | Need a formal source circuit language and delay normalization |
| §4 | Turing-machine/cellular-automaton universality | — | Out of verified core unless separately scoped |
| §6.2 | Interaction gate implements four constrained output rails and is reversible on valid states | 11 | Must use a subtype/relation, not an unconstrained `Bool^4` equivalence |
| §6.3–6.4 | Mirrors route/delay/cross and collision networks realize switch/Fredkin gates | 11 | Diagram-only; requires a discrete geometry model |
| §7.1 | Reversing gates and wires yields a semantic inverse for combinational networks | 7 | Requires acyclicity and delay/path discipline |
| §7.1, Figs. 22–24 | Compute-copy-uncompute returns argument and scratch and emits `(y, not y)` | 8 | Exact copy gadget and partitions must be proved |
| §7.1(b) | Scratch constants can all be zero without loss of generality | 9 | Attributed but unproved in paper |
| §7.2 | Arbitrary computation needs scratch for a fixed primitive set; claimed size tradeoffs | 9 | Quantifiers and complexity model unclear |
| §7.3 | Every invertible conservative finite function is Fredkin-realizable without garbage | 9 | Central, but ancilla/basis scope is ambiguous |
| §7.3 | Closed general-purpose computers have NAND-comparable gate complexity | 10 | External thesis/complexity model required; not core |
| §§5, 8–10 | Zero dissipation, entropy, energy, noise, and physical realizability claims | — | Documentation only absent an explicit physical model |

## Correction and Uncertainty Log

Entries remain open until a stage records checked evidence and a final
disposition.

| ID | Issue | Required disposition |
|---|---|---|
| CL-001 | The paper uses zero-controlled swapping, opposite to the common modern Fredkin convention. | Name the convention, prove the table row-by-row, and provide an explicit conjugacy theorem if an alternate convention is exposed. |
| CL-002 | “Inverse wire” mixes identity-on-values with reversal of time/orientation. | Separate value semantics, delay, and oriented network reversal. |
| CL-003 | Reversibility and conservation are independent, but the prose supplies no small formal witnesses. | Give finite counterexamples in both directions. |
| CL-004 | FAN-OUT is shown diagrammatically although arbitrary copying is not reversible. | State a constrained ancilla interface and account for every output. |
| CL-005 | A feed-forward network is called combinational only when all path delays match. | Decide whether equal latency is intrinsic syntax, a well-formedness predicate, or a retiming theorem. |
| CL-006 | The §4 universality argument translates ordinary sequential circuits informally and handwaves delay normalization. | Formalize the source language and state exact simulation/slowdown hypotheses. |
| CL-007 | The interaction gate has only four valid states on four rails. | Model valid states explicitly; never claim an equivalence on all 16 states. |
| CL-008 | The billiard diagrams omit mirrors, unit wires, collision scheduling, and some crossovers. | Treat each as a construction obligation in a discrete geometry model. |
| CL-009 | The spy/copy gadget needs one `0` and one `1` per copied result bit and emits both value and complement. | Make the precondition and `2n`-wire result encoding explicit. |
| CL-010 | “Garbageless” still returns the original argument and uses/restores scratch. | Define garbage relative to named interfaces; do not mean “no extra outputs whatsoever.” |
| CL-011 | All-zero scratch sufficiency is attributed to Margolus without proof. | Reconstruct a proof, cite a verifiable source, or leave the stronger version unresolved. |
| CL-012 | Scratchpad size claims use informal proportionality and an unstated cost model. | Define a circuit family and asymptotic measure before formalizing them. |
| CL-013 | “Any invertible conservative function” is Fredkin-realizable, attributed to Silver, but ancilla and wiring conventions are unclear. | Prove the strongest accurate variant and document required ancillas/permutations. |
| CL-014 | The no-scratch map `F0` is called a gate “by definition,” which does not imply synthesis from a fixed basis. | Keep semantic gatehood and basis realizability as separate predicates. |
| CL-015 | Claims about infinite blank tape/environment supplying constants and garbage space are not finite-circuit theorems. | Exclude or formalize in a separately scoped infinite model. |
| CL-016 | Physical reversibility, entropy, and zero-dissipation conclusions do not follow from finite bijections alone. | Keep them non-theorem commentary unless physical state and dynamics are formalized. |

## Dependency Notes and Tentative Module Direction

No dependency has yet been pinned. Stage 1 must inspect current stable Lean 4
and a compatible mathlib release, then record exact versions in the project.
Likely reusable mathlib surfaces include `Equiv`, `Equiv.Perm`, `Fintype`,
`Finite`, `Fin`, `Finset`, `Bool`, finite sums/products, and permutation/group
lemmas. Their actual imports and conventions must be verified before adoption.

Tentative low-to-high dependency layout (names provisional):

```text
ConservativeLogic/
  BitVec/Core.lean          -- fixed-width words and Hamming weight
  Reversible/Core.lean      -- finite reversible and conservative maps
  Gate/Fredkin.lean         -- exact primitive semantics and audits
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

Names are placeholders to refine during stage work; they are not declarations.

- `hammingWeight_append`: weight is additive across explicit wire blocks.
- `Reversible.injective` / `Reversible.surjective`: finite reversible maps have
  the expected function properties.
- `Conservative.comp` and `Conservative.inverse`: conservation is closed under
  composition and inversion of an equivalence.
- `reversible_not_conservative` and `conservative_not_reversible`: concrete
  independence witnesses.
- `fredkin_apply_zero`, `fredkin_apply_one`: exact control behavior.
- `fredkin_involutive`, `fredkin_equiv`, `fredkin_conservative`: core primitive
  properties.
- `fredkin_table`: equivalence with all eight rows in the paper.
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
- `copyPair_spec`: initialized `(0,1)` targets become `(a, not a)` while the
  through-wire retains `a`.
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

#### Big Picture Objective

Formalize the unit wire and the paper's exact Fredkin gate and settle its truth
table, ordering, reversibility, and conservation without convention drift.

#### Detailed Implementation Plan

- Define the one-step unit-wire value semantics separately from delay metadata.
- Define Fredkin on an explicitly ordered triple `(u, x1, x2)` using the
  paper's zero-controlled swap.
- Check all eight table rows and prove control equations, involutivity,
  bijectivity, nonlinearity only if a useful algebraic definition is selected,
  and weight preservation.
- If useful, define the common one-controlled variant and prove the precise
  control-negation conjugacy; keep it out of the default paper API.

#### Completion Requirements

- All eight paper rows reduce or prove exactly with the documented output order.
- Separate theorems establish involution/reversibility and conservation.
- Unit-wire delay and identity-on-values are not conflated.
- Regression examples fail if the control convention or data-wire order flips.
- Focused/full builds, scans, and diff check pass.

### 4-CIRCUITS

#### Big Picture Objective

Create arity-safe feed-forward circuit syntax and semantics whose composition
cannot perform implicit fan-out.

#### Detailed Implementation Plan

- Define primitive gates, identity, serial composition, parallel/tensor
  composition, and bijective wire permutations.
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

- Prove the Fredkin “spy” gadget on the exact constrained `(0,1)` auxiliary
  input, including its through output and `(a, not a)` result pair.
- Lift copying componentwise to Boolean vectors without implicit wire reuse.
- Compose a realization, explicit copy layer, and inverse realization.
- Prove restoration of arguments, source/scratch constants, and transient
  garbage, plus the exact result-register encoding and weight preservation.

#### Completion Requirements

- The final theorem states every input and output block and proves the argument
  and scratch blocks return definitionally or propositionally unchanged.
- The `2n` result register starts with exactly `n` zeros and `n` ones and ends
  with `f x` and its bitwise complement in a documented order.
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
