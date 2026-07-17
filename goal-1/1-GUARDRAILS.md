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
- The paper source, extracted figures, generic Lean build plan, scaffold paper
  map, and correction log are present and readable.
- There is no previous implementation stage or Lean API to preserve.

## Updated Assumptions

- Use a self-contained `formal/` Lake project so the unrelated Python files do
  not become part of Lean's source root.
- Pin Lean and mathlib to the matching `v4.32.0` release pair; record the exact
  resolved mathlib commit in `lake-manifest.json`.
- Compile-check `Fin n -> Bool`, `Vector Bool n`, and `BitVec n` in a private
  audit leaf before fixing the public bit-word representation.
- Prefer `Fin n -> Bool` if it supplies finite/decidable equality instances and
  a direct `Finset.univ` Hamming-weight definition without broad imports.
- Use `Equiv`/`Equiv.Perm` for reversible semantics if the narrow import and
  composition/inverse operations compile as expected.
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
  declaration is `private` and all remaining commands are `example`s.
- Stage boundary: scan Lean declarations and file paths for Fredkin, circuit,
  realization, uncompute, universality, sequential, or billiard implementation.
- Dependency boundary: inspect the generated manifest revision and the imports
  reported by the audit leaf rather than treating a successful umbrella import
  as evidence.

## No-Cheating Checks

- The root module must not import the audit probe or expose temporary candidate
  definitions as public API.
- The audit probe may use only `private` abbreviations/definitions and
  `example`/`#check`; it must not implement stage-2 structures or theorems.
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

**Stage status: incomplete.** Offline setup and decisions are recorded, but the
mathlib dependency has not been materialized and the required focused/full
builds have not run.

### Work completed

- Added an isolated `formal/` Lake project with matching Lean/mathlib
  `v4.32.0` pins and global mathlib-standard lint options.
- Added an empty `ConservativeLogic` public root. It exports no definitions and
  does not import the audit probe.
- Added the private diagnostic leaf
  `ConservativeLogic.Audit.Guardrails`, containing only private candidate
  aliases/weight definition and compile examples.
- Added root documentation for scope, physical-model boundaries, and build
  entry points, and ignored only generated `.lake/` directories.
- Corrected the main paper map: unit wire begins in stage 3; combinational and
  sequential §4 simulation claims are now separate; closed trajectory
  conservation has a stage-10 target; and §7.2's `F0` requires an initialized
  slice-to-total-permutation extension theorem.
- Corrected the planned copy theorem. With Table (2)'s exact
  `(u,x1,x2)`/`(v,y1,y2)` order, `(x1,x2)=(1,0)` gives
  `(y1,y2)=(a,not a)`. The later proof must not infer port order from the
  vertical placement of constants in Figures 6(c) or 22.

### Toolchain and source evidence

- Lean's stable `v4.32.0` and mathlib's matching `v4.32.0` release are both
  non-prerelease releases published 2026-07-13.
- Lean tag commit:
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Expected mathlib tag/manifest commit:
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

The following decisions are accepted for stage 2, conditional only on the
pending in-project build reproducing the compile audit:

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

### Verification evidence and remaining action

- `cd formal && lean --version` selected Lean `v4.32.0` at commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- `cd formal && lean ConservativeLogic.lean` succeeded for the empty public
  root.
- The offline Lean-source scan found no `sorry`, `admit`, or `axiom`; the
  declaration scan found no Fredkin/circuit/realization/uncompute/universality/
  sequential/billiard implementation; the whitespace scan and
  `git diff --check` passed.
- `lake update` inside `formal/` failed in the sandbox because Reservoir's
  `curl` exited with code 6. The required escalated retry was rejected by the
  approval gate, which still treated the prior scaffold-only instruction as a
  prohibition. No indirect dependency-fetch workaround was attempted.
- Consequently, `lake-manifest.json`, the local mathlib checkout, the focused
  audit build, cache retrieval, and full build are still missing. The exact next
  action after explicit approval is:

  ```text
  cd formal
  lake update
  lake exe cache get
  lake build ConservativeLogic.Audit.Guardrails
  lake build
  ```

- After those commands pass, verify the manifest revision, run the Lean-source
  proof-hole/forbidden-feature scans, `git diff --check`, inspect the diff, and
  fold final evidence into `0-plan.md`. Do not start stage 2 before that.
