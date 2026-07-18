# Stage 11: Constrained Billiard-Ball Abstraction

## Status

In progress on 2026-07-18 from clean synchronized baseline `898bfe5`.
Section 6, footnotes 6--7, and the original images of Figures 12--18 have been
read together.  No Lean implementation has yet been accepted as a result.

## Current Facts

- Section 6.1 describes continuous hard balls of radius `1/sqrt(2)` and fixed
  plane mirrors, with centers sampled on a unit grid at integral times.  It
  restricts attention to right-angle elastic collisions, but does not define a
  total discrete global transition or the outcome of multi-contact events.
- A grid occupancy at one instant is not a state of that mechanics: the same
  occupied point can have several future trajectories unless directed velocity
  and mirror information are retained.
- Figure 14 is unusually precise.  Its two vertically aligned inputs approach
  in the southeast/northeast directions; a lone ball continues straight, two
  balls turn onto the outer rails, and `A,B,C,D` are sampled exactly four steps
  later.  Its complete table is
  `(p,q) -> (p q, !p q, p !q, p q)`.
- Footnote 7 explicitly says that the four output rails of the interaction gate
  have only four valid states, not sixteen, and that composition must retain
  this constraint.  The valid rows are `0000,0100,0010,1001`.
- Figure 16 similarly defines the switch table
  `(c,x) -> (c,c x,!c x)`, whose valid rows are `000,001,100,110`.
- Section 6.3 says mirrors provide turns, shifts, arbitrary delays, and a
  nontrivial crossover.  Figure 15 supplies drawings but no coordinates or
  numerical delays.  A crossover is called trivial only when logic or timing
  excludes simultaneous balls at the crossing.
- Figure 18's caption explicitly omits steering/timing mirrors and unit wires,
  identifies its bridge as a nontrivial crossover, and calls the other
  crossovers trivial.  The drawing is therefore not a complete timed layout.
  Finite-radius clearance and simultaneous collision scheduling are additional
  proof obligations.
- Existing `WeightPreserving` already permits unequal widths, but
  `Reversible n` and `Conservative n` are equal-width Boolean endomaps.  The
  latter must not be used for either constrained rail interface.
- The finite API and the Stage 10 opt-in sequential API contain no physical
  routing or billiard module.  Stage 11 can remain a separate opt-in leaf.

## Updated Assumptions

- Accepted: the two endpoint tables can be formalized exactly as equivalences
  onto range subtypes, with inverse reconstruction and separate ball-count
  preservation.
- Accepted: a local collision-site abstraction can be total, deterministic,
  involutive, and count-preserving on an explicit legal phase/state subtype.
  Products of this state mean independent sites only.
- Accepted: a directed sampled-path language can certify unit diagonal moves,
  mirror direction changes, finite detours, sampled clearance, and
  same-place/same-time conflicts without claiming continuous mechanics.
- Accepted: Figure 14 can be reconstructed at that sampled abstraction with
  exact latency four and complete endpoint refinement.
- Rejected: occupancy-only samples determine a global update.
- Rejected: primitive truth tables or the erased Figure 18 drawing prove a
  whole-circuit billiard refinement.
- Unresolved: continuous elastic/specular correspondence, between-sample
  clearance, multi-contact rules, the Figure 15 bridge, the full Figure 17
  switch layout, either Figure 18 Fredkin layout, arbitrary delay, and
  compositional physical layout.

## Big Picture Objective

Build the strongest honest reusable discrete abstraction supported by Section
6: exact constrained interfaces, an executable legal collision-site step, and
one machine-checked four-tick sampled collision layout.  Turn the missing
global mechanics and erased layout data into checked boundary results rather
than filling them in by convention.

## Detailed Implementation Plan

1. Add `Billiard/Interface.lean` with ordered input/output constructors,
   interaction and switch range predicates/subtypes, selected inverses,
   equivalences, all-row laws, count preservation, exact valid-state counts,
   and impossibility of raw `2<->4` and `2<->3` equivalences.
2. Add `Billiard/Collision.lean` with the selected four-channel
   `0110 <-> 1001` scattering permutation, its explicitly admitted local
   subtype, count preservation, and exact initialized interaction slice.  Its
   total identity fallback outside the subtype must be labeled algebraic only.
3. Add `Billiard/Discrete.lean` with independent finite-site products of the
   admitted local collision state, an involutive simultaneous step, commuting
   single-site updates, total ball-count preservation, and an illegal
   three-ball boundary.
4. Add `Billiard/Geometry.lean` with integer grid points, four directed diagonal
   velocities, certified finite routes, horizontal/vertical mirror reflection,
   a finite delay detour, sampled clearance, and time-indexed route conflict.
   Check a simultaneous crossing conflict and a staggered conflict-free use.
5. Add `Billiard/Figure14.lean` with four explicit directed routes, the active
   sampled configuration for each `(p,q)`, exact start/end observation, latency
   four, frame legality/clearance, count preservation, and a right-angle-turn
   certificate used exactly when both inputs are true.
6. Add a thin opt-in `ConservativeLogic.Billiard` umbrella and a non-public
   `Audit/Billiard.lean`.  Do not import either from the finite API or sequential
   umbrella.
7. Update the README, paper map, correction log, dependency map, and this report
   only after the focused implementation and adversarial checks pass.

Expected principal declarations:

```text
Billiard.Interaction.encode
Billiard.Interaction.ValidOutput
Billiard.Interaction.equiv
Billiard.Interaction.weightPreserving
Billiard.Interaction.validOutput_card
Billiard.Interaction.no_raw_equiv
Billiard.Switch.equiv
Billiard.Switch.weightPreserving
Billiard.Switch.validOutput_card
Billiard.Switch.no_raw_equiv
Billiard.Collision.map
Billiard.Collision.conservative
Billiard.Collision.AllowedState
Billiard.Collision.allowedEquiv
Billiard.Collision.map_embed
Billiard.ScatteringLayer.Configuration.stepEquiv
Billiard.ScatteringLayer.Configuration.stepAt_commute
Billiard.ScatteringLayer.Configuration.totalBallCount_step
Billiard.Grid.Route
Billiard.Grid.Mirror.reflect
Billiard.Grid.simultaneous_crossing_conflict
Billiard.Grid.staggered_crossing_clear
Billiard.Figure14.output_refines
Billiard.Figure14.exact_latency
Billiard.Figure14.sampled_clearance
```

## Build Structure

```text
Billiard/Interface.lean  exact heterogeneous rail interfaces
Billiard/Collision.lean  selected local permutation and admitted subtype
Billiard/Discrete.lean   independent simultaneous scattering layers
Billiard/Geometry.lean   directed sampled routes and timing conflicts
Billiard/Figure14.lean   selected coordinate/timing refinement
Billiard.lean            opt-in umbrella
Audit/Billiard.lean      rows, illegal states, conflicts, and axiom audit
```

No existing high-fanout Lean module should change.  Focused builds:

```text
cd formal
lake build ConservativeLogic.Billiard.Interface
lake build ConservativeLogic.Billiard.Discrete
lake build ConservativeLogic.Billiard.Geometry
lake build ConservativeLogic.Billiard.Figure14
lake build ConservativeLogic.Billiard ConservativeLogic.Audit.Billiard
```

The ordinary `lake build` must still omit the opt-in billiard leaf.  A clean
default build followed by explicit umbrella/audit builds will verify that
boundary if the stage implementation is accepted.

## Boundary Checks

- `ValidOutput` is part of each inverse's type.  No theorem may erase the
  constraint or package either interface as `Conservative`.
- The local step accepts only its explicit legal subtype.  An independent-site
  product means no shared ball, route, mirror, or collision locus.
- A sampled route certificate records discrete coordinates and directions; it
  is not a proof about radius, momentum, energy, elastic impact, specular
  reflection, or continuous time.
- Sampled clearance is checked only at integral frames.  Between-frame contact
  and finite-radius obstacle clearance remain outside the theorem.
- A trivial crossover requires a theorem excluding the same coordinate at the
  same global tick.  Spatial crossing alone is insufficient.
- Figure 14 is a stated coordinate reconstruction matching the four endpoint
  rows and latency.  It is not presented as extracted coordinates from the
  unscaled drawing.
- No Figure 17/18 refinement theorem, arbitrary layout compiler, physical time
  reversal, or thermodynamic result may appear.

## No-Cheating Checks

- Exhaust all four interaction rows and all four switch rows.
- Prove the valid subtype has cardinality four in each case and prove the raw
  target type has the wrong cardinality.
- Scan the Stage 11 sources for `Conservative`, `Classical.choice`, project
  axioms, proof holes, unsafe evaluation, and claims about Figure 17/18,
  elasticity, energy, or thermodynamics; classify every documentation hit.
- Check that an invalid three-ball output event cannot inhabit the legal local
  phase and that stepping twice restores every legal local/global state.
- Check a pair of spatially crossing routes both with simultaneous conflict and
  with an explicitly staggered conflict-free schedule.
- Check every Figure 14 input row, every integral frame, both active-ball count
  and sampled clearance, all route directions, and the exact four-tick output.
- Use `#print axioms` on both constrained equivalences' central laws, the global
  step/count theorem, the crossover checks, and Figure 14 refinement.

## Completion Requirements

- The selected local collision is restricted to an explicit admitted subtype;
  its step and every independent finite-site product are deterministic,
  involutive, and preserve the stated ball count.  Any total raw fallback is
  exposed as algebraic completion rather than physical semantics.
- Interaction and switch inverses have the exact valid-output subtype in their
  signatures; valid cardinalities and raw-interface impossibility are checked.
- Figure 14 has a coordinate-level sampled refinement theorem and exact latency
  four, with sampled legality and all intermediate directions checked.
- Routing examples distinguish mirrors, delay, spatial crossing, timing, and
  sampled clearance.  Unsupported continuous/global claims remain explicit.
- All focused, umbrella, audit, default, and post-clean builds; row tests;
  forbidden-shortcut/proof-hole scans; axiom audit; complete diff inspection;
  and `git diff --check` pass.

## Stage Results

Pending implementation and verification.
