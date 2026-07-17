# Continuation Prompt

```text
Work through goal-1/0-plan.md using the repeatable protocol in
goal-1/0-loop.md, beginning with the first incomplete stage and implementing
only one stage at a time.

The high-level objective is to turn Fredkin and Toffoli's “Conservative Logic”
into a correct, reusable Lean 4 library for finite reversible Boolean maps,
Hamming-weight-preserving maps, the paper-convention Fredkin gate, one-to-one
circuit semantics, realization with constants and garbage, inverse circuits,
compute-copy-uncompute with restored scratch, and accurately scoped Fredkin
universality; add sequential and discrete billiard-ball models later only when
their semantics can be made precise.

Independently verify the paper. Do not use unjustified axioms, fabricated
proofs, implicit fan-out, hidden ancillas, or green tests that do not cover the
claim. Keep reversibility distinct from conservation, combinational circuits
distinct from sequential circuits, semantic existence distinct from resource
bounds, and mathematical circuit theorems distinct from physical claims. Use
the paper's printed Fredkin ordering and zero-controlled swap convention unless
an alternative is explicitly named. State all constants, arguments, results,
garbage, scratch, constrained interfaces, delay assumptions, and restoration
conditions. Correct mistakes or missing hypotheses and update the paper map and
correction log; carry unresolved issues forward rather than guessing.

For each stage: inspect current files, tests, relevant paper sections, and the
previous evidence; update current facts in the plan; create or refresh the stage
file from the loop template; implement only that stage; add no-cheating checks;
run focused and required full builds, truth-table/property tests, proof-hole and
axiom scans, axiom audits, and diff checks; record exact results; then fold them
back into the plan. If stopping, leave precise next work and assumptions to
challenge.

Completion means the original objective is actually achieved: the pinned
project builds cleanly, completed modules contain no sorry/admit or unexplained
project axioms, main results have axiom audits, reusable declarations map the
paper's core discrete claims to verified or corrected theorems, and all open
issues are explicit next work rather than silently omitted.
```
