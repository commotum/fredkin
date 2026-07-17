# 1-GUARDRAILS

## Current Facts

- The active goal is defined by `goal-1/0-plan.md` and the execution protocol by
  `goal-1/0-loop.md`.
- Before this stage, the repository had no Lean project, toolchain pin, Lake
  manifest, Lean module, or Lean test. The existing Python placeholder is
  unrelated and will be preserved.
- The host has `elan`, Lean `v4.31.0`, and Lean `v4.32.0`; `v4.31.0` was the
  ambient default before a project pin.
- Official Lean and mathlib GitHub releases both provide matching stable
  `v4.32.0` tags. Mathlib's `v4.32.0/lean-toolchain` names
  `leanprover/lean4:v4.32.0`.
- `formal/lake-manifest.json` now locks mathlib `v4.32.0` to commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`, and all inherited dependency
  checkouts match their manifest revisions.
- The strengthened private probe and the empty default target both build under
  the pinned project. The probe checks positive and deliberately absent
  candidate instances, reversible-map operations, composition order, and the
  selected block-construction surface.
- The paper source, extracted figures, generic Lean build plan, scaffold paper
  map, and correction log are present and readable.
- There is no previous implementation stage or Lean API to preserve.

## Updated Assumptions

- Use a self-contained `formal/` Lake project so the unrelated Python files do
  not become part of Lean's source root.
- Keep Lean and mathlib at the checked matching `v4.32.0` release pair and
  preserve the exact resolved revisions in `lake-manifest.json`.
- Use `Fin n → Bool` for the public mathematical bit-word representation; the
  private probe confirms its finite/decidable-equality instances and a direct
  `Finset.univ` Hamming-weight expression under narrow imports.
- Use `Equiv`/`Equiv.Perm` for reversible semantics; the private probe confirms
  identity, inverse, serial composition, and application order.
- Plan a bundled conservative equivalence with an explicit weight-preservation
  field in stage 2; do not implement that public structure in this stage.
- Keep combinational circuit syntax, timing, realization, and physical models
  out of this stage. This stage freezes their boundaries but adds no semantics.

## Big Picture Objective

Establish a reproducible minimal Lean/mathlib environment and evidence-backed
representation, module-layering, source-map, and audit policies that make stage
2 safe to begin without introducing any substantive paper formalization.

## Detailed Implementation Plan

- Add `formal/lean-toolchain` pinned to Lean `v4.32.0`.
- Add `formal/lakefile.toml` with mathlib pinned to `v4.32.0` and a single
  `ConservativeLogic` library.
- Add an intentionally empty public root module.
- Add `ConservativeLogic/Audit/Guardrails.lean` containing only private
  representation probes and compile-time examples for the proposed finite word,
  Hamming weight, `Equiv`, `Vector`, and `BitVec` surfaces.
- Resolve dependencies and fetch the matching mathlib cache.
- Record accepted/rejected representation choices, module ownership, exact
  imports, source boundaries, proof-hole policy, and axiom-audit policy here and
  fold checked facts into `0-plan.md`.
- Update the root README only with project scope, formal-build commands, and
  links to the authoritative plan/correction log.

## Build Structure

Expected files:

- `formal/lean-toolchain`
- `formal/lakefile.toml`
- `formal/lake-manifest.json` (generated dependency lock)
- `formal/ConservativeLogic.lean`
- `formal/ConservativeLogic/Audit/Guardrails.lean`
- `README.md`
- `goal-1/0-plan.md`
- `goal-1/1-GUARDRAILS.md`

Focused build command:

```text
cd formal && lake build ConservativeLogic.Audit.Guardrails
```

Full build command:

```text
cd formal && lake build
```

The empty `formal/ConservativeLogic.lean` is the public root and intentionally
imports nothing. `formal/ConservativeLogic/Audit/Guardrails.lean` is a private
diagnostic leaf that owns all candidate probes. No high-fanout or future core
module exists or is introduced in this stage.

## Boundary Checks

- Public API boundary: inspect `ConservativeLogic.lean` and confirm it has only
  the empty namespace skeleton and no audit import.
- Diagnostic boundary: inspect the audit leaf and confirm every candidate
  declaration is `private`; all remaining commands are `example`s or guarded
  `#check_failure` instance audits.
- Stage boundary: scan Lean declarations and file paths for Fredkin, circuit,
  realization, uncompute, universality, sequential, or billiard implementation.
- Dependency boundary: inspect the generated manifest revision and the imports
  reported by the audit leaf rather than treating a successful umbrella import
  as evidence.

## No-Cheating Checks

- The root module must not import the audit probe or expose temporary candidate
  definitions as public API.
- The audit probe may use only `private` abbreviations/definitions,
  `example`, `#check`, and guarded `#check_failure` diagnostics; it must not
  implement stage-2 structures or theorems.
- The dependency manifest must resolve mathlib at the requested matching tag,
  not an unpinned branch.
- `Fin n -> Bool` is accepted only after compile checks establish the required
  finite and decidable-equality instances and weight expression.
- No Fredkin, circuit, realization, universality, sequential, billiard, energy,
  or entropy declaration may be introduced in this stage.
- Documentation occurrences of `sorry`, `admit`, and `axiom` are classified;
  Lean sources must contain none.
- No hidden fallback implementation or reference evaluator is introduced.

## Completion Requirements

- Exact Lean and mathlib pins exist, the manifest records the resolved revision,
  and the project reports Lean `v4.32.0` under its directory.
- The private guardrail probe builds with narrow verified imports and checks all
  representation candidates named above.
- The selected public representation, Hamming-weight expression, reversible
  map representation, conservative bundle plan, rejected alternatives, and
  import/module boundaries are documented with compile evidence.
- Every central paper claim is mapped in `0-plan.md` to a stage, correction, or
  explicit out-of-scope status; missing claims found in the audit are added.
- The root README identifies the formal core and warns that physical claims are
  not consequences of finite circuit semantics.
- Focused build and full `lake build` succeed.
- Lean sources have no `sorry`, `admit`, or `axiom`; stage-specific forbidden
  feature scans have no implementation hits.
- The only stage-specific Lean file is an audit probe and the public root remains
  an empty namespace skeleton.
- `git diff --check` passes and the complete diff is inspected.

## Stage Results

**Stage status: complete (2026-07-17).** The locked project, strengthened
private probe, paper/correction map, focused and default builds, clean rebuild,
boundary scans, and diff checks satisfy every Stage 1 completion requirement.

### Work completed

- Added an isolated `formal/` Lake project with matching Lean/mathlib
  `v4.32.0` pins and global mathlib-standard lint options.
- Materialized the dependency graph and committed `formal/lake-manifest.json`,
  which records mathlib tag `v4.32.0` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Added an empty `ConservativeLogic` public root. It exports no definitions and
  does not import the audit probe.
- Added the private diagnostic leaf
  `ConservativeLogic.Audit.Guardrails`, containing only private candidate
  aliases/weight definition, compile examples, and guarded expected-failure
  instance checks. It covers finite/decidable function words, `Equiv` inverse
  and serial semantics, `Fin.addCases`, and the accepted/rejected candidate
  container surfaces.
- Added root documentation for scope, physical-model boundaries, and build
  entry points, and ignored only generated `.lake/` directories.
- Corrected the main paper map: unit wire begins in stage 3; combinational and
  sequential §4 simulation claims are now separate; closed trajectory
  conservation has a stage-10 target; and §7.2's `F0` requires an initialized
  slice-to-total-permutation extension theorem.
- Corrected further source-audit errors: the paper's §2.5 graph model includes
  feedback and memory rather than being feed-forward; Figure 7 states equal
  delay only from argument to result; and Figure 8 provides no transition or
  trace specification. Added explicit dispositions for P4–P8, the §6.1
  discrete billiard state, the strong whole-circuit billiard correspondence,
  §7 resource headlines, physical claims throughout the paper, and the tacit
  unit-wire/identity basis convention.
- Narrowed correction CL-008 to what Figure 18 actually says: steering/timing
  mirrors and unit wires are omitted, while bridge and trivial crossovers are
  explicitly distinguished. Clearance and collision scheduling remain inferred
  formalization obligations, not alleged quotations.
- Corrected the planned copy theorem. With Table (2)'s exact
  `(u,x1,x2)`/`(v,y1,y2)` order, `(x1,x2)=(1,0)` gives
  `(y1,y2)=(a,not a)`. The later proof must not infer port order from the
  vertical placement of constants in Figures 6(c) or 22.

### Toolchain and source evidence

- Lean's stable `v4.32.0` and mathlib's matching `v4.32.0` release are both
  non-prerelease releases published 2026-07-13.
- Lean tag commit:
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Locked mathlib tag/manifest commit:
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Mathlib's tagged `lean-toolchain` selects exactly
  `leanprover/lean4:v4.32.0`.
- Authoritative upstream evidence:
  [Lean release](https://github.com/leanprover/lean4/releases/tag/v4.32.0),
  [Lean release notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.0/),
  [mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.32.0),
  and
  [mathlib dependency guidance](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).
- The paper PDF is the primary local artifact. The extracted Markdown and
  figures are navigation/reconstruction aids and must be checked against the
  PDF when typography, wire routing, or formulas matter. External attributions
  to Silver, Margolus, Bennett, Toffoli, or Ressler are leads, not imported
  proof evidence.

### Representation decision record

The following decisions are accepted for stage 2 by the in-project compiled
probe:

- Core state: transparent `abbrev BitState (n : Nat) := Fin n → Bool`.
  This gives coordinate access, function extensionality, finite enumeration,
  and decidable equality while preserving wire identity through `Fin n`.
- Hamming weight: project-owned
  `(Finset.univ.filter fun i => x i = true).card`. This directly expresses the
  paper's number of one-valued wires without imposing unrelated algebra on
  `Bool`.
- Reversible state map: `Equiv.Perm (BitState n)` (or a transparent project
  alias), not a separately proved bijective function.
- Wire permutation: `Equiv.Perm (Fin n)`, kept nominally distinct from a state
  permutation. Its action on states will be defined explicitly in stage 2/4.
- Conservative map: a project structure bundling a reversible map with a
  separate field `∀ x, hammingWeight (e x) = hammingWeight x`. Conservation
  will not be an instance inferred from reversibility.
- Block wiring: project-owned `append`/`split` operations based on
  `Fin.addCases` with named projection lemmas. Do not expose a long composite
  of `sumArrowEquivProdArrow`, `piCongrLeft`, and `finSumFinEquiv` in the public
  API.
- Serial semantic composition: spell it using `Equiv.trans` and document that
  `e.trans f` applies `e` then `f`. Do not silently substitute permutation group
  multiplication, whose function-composition reading is ordered differently.
- Circuit model: use arity-indexed serial/tensor/permutation syntax as the
  primary corrected combinational model, not as an unproved literal encoding of
  every directed graph in §2.5. Any theorem about the paper's graph model needs
  a normalization/correspondence proof. Structural reindexing and a physical
  permutation/wire circuit with delay remain separate notions, and every
  completeness theorem must say which is free.

Rejected or deferred alternatives:

- Root `Vector Bool n` is an array-backed executable container but lacks the
  needed local `Fintype` surface and makes proofs array/Nat-index oriented.
- `List.Vector Bool n` has finite instances but adds subtype/list indirection
  without an advantage over the Pi representation.
- `BitVec n` is useful for a future executable adapter, but lacks the desired
  finite-enumeration instance and mixes LSB indexing with big-endian
  append/cons conventions, creating avoidable Fredkin ordering risk.
- `Mathlib.InformationTheory.Hamming.hammingNorm` has the right filtered-card
  shape but requires a global `Zero Bool` supplied by Boolean-ring imports and
  pulls a much heavier analysis surface. A bridge may live in a later optional
  interoperability leaf; it is not the core definition.
- Representing a state only as a set of true indices is useful extensionally
  but obscures the primary Boolean-wire interface and ordinary Boolean target
  functions. It is not the public state type.

### Module, import, and audit policy

- Public namespace: `ConservativeLogic`. Stable definitions live in narrow
  low-dependency leaves; the root/API remains a thin re-export surface.
- The foundational state module will be `ConservativeLogic/State/Core.lean`,
  not `BitVec/Core.lean`, to avoid falsely implying use of Lean's packed
  `BitVec` type.
- Core state imports should begin with `Mathlib.Data.Fintype.Pi` and
  `Mathlib.Logic.Equiv.Basic`; `Mathlib.Logic.Equiv.Fin.Basic` belongs in the
  first leaf that needs block/wire equivalences. `Mathlib.Data.BitVec` remains
  audit/adapter-only.
- Umbrella `Mathlib` and `Mathlib.Tactic` imports are forbidden in foundational
  runtime/API leaves. Proof leaves may add narrow tactic imports with a concrete
  need.
- `relaxedAutoImplicit = false` and the mathlib standard linter set are project
  options. New global simp lemmas, instances, coercions, or notation require a
  demonstrated public need.
- Diagnostics, exhaustive fixed-width checks, counterexamples, and
  `#print axioms` commands live under `ConservativeLogic/Audit/` and do not feed
  runtime definitions or stable theorem statements.
- Every completed stage scans Lean sources for `sorry`, `admit`, and
  project-specific `axiom`; documentation matches are classified manually.
  Main stable theorems receive recorded `#print axioms` output. Mathlib's
  ordinary foundational axioms are distinguished from new project axioms.
- Combinational syntax must not depend on sequential or billiard modules;
  optional physical/discrete geometry modules must not become dependencies of
  the finite logical API.

### Verification evidence

- `cd formal && lean --version` selected Lean `v4.32.0` at commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- The first sandboxed `lake update` failed because Reservoir's `curl` exited
  with code 6. The approved network retry succeeded, checked out mathlib at the
  exact locked revision, materialized all inherited dependencies, and ran
  mathlib's cache hook successfully.
- The first focused build exposed a real compatibility defect:
  `invalid 'import' command, it must be used in the beginning of the file`.
  Moving the four imports before the module doc command fixed the probe for
  Lean 4.32.0.
- `lake build ConservativeLogic.Audit.Guardrails` then succeeded with 762 jobs.
  This focused command remains required because the private audit leaf is not
  imported by the intentionally empty default target.
- The default `lake build` succeeded with 3 jobs, confirming that the public
  root remains independently buildable.
- The strengthened probe rebuild succeeded after adding guarded missing-instance
  checks for `Vector Bool 3` and `BitVec 3`, `DecidableEq` checks, `Equiv.symm`,
  `Equiv.trans`, its application order, and `Fin.addCases`.
- After `lake clean`, the focused build succeeded with 770 jobs and the default
  build with 3 jobs from a clean project build directory against the locked
  dependencies.
- Lean-source scans found no `sorry`, `admit`, `axiom`, later-stage
  implementation declarations, or unsafe/fallback constructs. Stage 1 exports
  no theorem, so no `#print axioms` target applies yet.
- The manifest revision/import boundary checks, `git diff --check`, complete
  diff inspection, and final clean-worktree check passed. Stage 2 is the first
  incomplete stage and was not started.
