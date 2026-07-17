# Conservative Logic Goal Execution Loop

Use this protocol to execute `goal-1/0-plan.md` one stage at a time. Do not
start a later stage merely because an easier subset of the current stage builds.

## Repeatable Loop

1. Sync current state with actual files and tests.
2. Update `0-plan.md` with current facts before starting the next stage.
3. Select the first incomplete stage.
4. Create or refresh `goal-1/[INDEX]-[SHORTHAND].md` from the stage template.
5. Implement only that stage.
6. Add verification and no-cheating checks.
7. Run focused tests, full verification, and whitespace/diff checks appropriate
   to the repo.
8. Record results in the stage file.
9. Fold results back into `0-plan.md`.
10. Continue toward the original objective. If stopping for the session, leave
    the goal in a resumable state with current evidence, next experiments,
    unblock actions, and assumptions to challenge.

## Invariants

- Do not narrow the user's objective without saying so.
- Do not mark a stage complete without evidence.
- Do not use tests or green checks as evidence unless they cover the
  requirement.
- Prefer small, low-complexity stages that narrow uncertainty.
- Convert blockers into work items: decompose them, route around them, or turn
  them into proof and verification tasks.
- Preserve the distinction between implementation, verifier, diagnostic, and
  fallback paths.
- Re-read the relevant paper prose, truth tables, footnotes, and figures before
  formalizing a claim; diagrams are evidence to reconstruct, not formal specs.
- Record every material correction or added hypothesis in the correction log
  and in the affected declaration's documentation.
- Keep reversibility/conservation, combinational/sequential,
  semantics/resources, and logical/physical claims separated throughout.
- Never introduce implicit fan-out, hidden ancillas, hidden garbage, or an
  unconstrained total interface for a partial gate.
- Do not accept a universality theorem until its basis, wiring, constants,
  garbage, scratch, restoration, and efficiency quantifiers are explicit.
- Use `fredkin-1982/BUILD-PLAN.md` for Lean module layering and incremental
  build discipline once implementation begins.

## Current-State and Verification Protocol

At the beginning of every stage:

- Read `goal-1/0-plan.md`, this loop, the previous stage result, the relevant
  paper sections, and current Lean modules/tests.
- Inspect `git status --short` and preserve unrelated user changes.
- Replace assumptions contradicted by code, mathlib, or proof attempts with
  checked facts in the plan before editing.
- Name the exact theorem statements, forbidden shortcuts, expected files, and
  focused build commands in the stage file.

Before completing every Lean stage:

- Run focused builds for every touched leaf and adjacent public consumer.
- Run full `lake build` when the stage changes configuration, shared APIs,
  global notation/instances, or when its completion requirements demand it.
- Run repository-appropriate evaluation/property tests and fixed-gate truth
  table checks.
- Scan changed Lean sources for `sorry`, `admit`, and project-specific `axiom`;
  classify any documentation-only matches.
- Run stage-specific scans for hidden fan-out, fallback routes, or erased
  ancilla/resource information.
- Run `#print axioms` on the stage's main theorems when they enter the stable
  theorem surface.
- Run `git diff --check` and inspect the complete diff.
- Record commands, outputs, declaration names, corrections, failed obligations,
  and remaining uncertainty in the stage report and fold them into the plan.

## Stage File Template

```markdown
# [INDEX]-[SHORTHAND]

## Current Facts

- Facts from current code, tests, docs, and previous stage results.

## Updated Assumptions

- Assumptions that still look valid.
- Assumptions that changed.
- Assumptions that need tests before being trusted.

## Big Picture Objective

- Restate the stage objective, adjusted for current facts.

## Detailed Implementation Plan

- Concrete code/doc/test changes for this stage.
- Files expected to change.
- New tests or commands required.

## Build Structure

- New or touched Lean modules and why each owns its declarations.
- High-fanout modules intentionally avoided.
- Repository-specific focused and adjacent-consumer build commands.

## Boundary Checks

- Runtime/API/proof-side/diagnostic boundaries relevant to this stage.
- Forbidden structural shortcuts and how inspection or scans detect them.

## No-Cheating Checks

- Explicit checks proving the implementation does not route through forbidden fallback paths.

## Completion Requirements

- Requirement-by-requirement checks.
- Required test commands.
- Documentation updates required.

## Stage Results

- Fill in at the end of the stage.
- Include tests run and outcomes.
- Include what was learned.
- Include what should change in `0-plan.md` before the next stage.
```

## Stop/Resume Discipline

If work stops before the whole objective is achieved, the active stage remains
incomplete. Record the exact checked state, smallest next proof or diagnostic,
unblock options, and assumptions most likely to fail. A blocker is not a reason
to redefine success; it becomes a construction, counterexample, source-research,
or verifier task in the same goal.
