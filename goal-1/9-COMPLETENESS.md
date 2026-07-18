# Stage 9: Finite Completeness and Its Resource Boundary

## Status

In progress from clean synchronized baseline `5b28ef8` on 2026-07-17.
This document fixes the proof contract before implementation. Stage 10 has not
started.

## Re-Audited Paper Claims

The authoritative text and the local images of Figures 24, 25, and 26 were
read together.

- Section 2.5 defines literal conservative circuits as directed graphs with
  instantaneous gates and delay-bearing wires. It tacitly includes the unit
  wire and identity gate in every primitive-basis realizability claim. It does
  not grant arbitrary zero-cost wire permutations or identify every open,
  possibly stateful graph with a static boundary permutation.
- Figure 24's scratchpad is the fixed `c` source of the original realization
  `phi`; it is consumed into `g` and restored by the complete
  compute-copy-uncompute network. In the library `Layout`, paper `c`
  corresponds to `source`. The library's separate already-returned `scratch`
  block is a stronger interface.
- The statement that this restored workspace can start all zero is attributed
  to Margolus, but no proof or precise source is supplied. The text gives no
  width-, gate-count-, or delay-preservation statement for that conversion.
- Figure 25 displays only

  `(x,0^n,1^n) -> (x,f(x),not f(x))`

  at total width `m + 2n`. Retaining `x` makes the slice injective, and both
  ancillary pairs have exactly `n` true bits. Calling the displayed box a
  total invertible conservative gate suppresses a real, noncanonical finite
  extension within each Hamming layer.
- Figure 26c is a same-register endomap, so its hidden boundary hypothesis is
  `m = n`. Bijectivity plus conservation is definition-level sufficient only
  when the whole endomap may itself be selected as one arbitrary primitive.
- Fredkin-only sufficiency is attributed to **B. Silver** in Section 7.3, but
  the acknowledgments name **D. Silver** and the bibliography contains no
  Silver item. The proof, ancilla count, and routing convention cannot be
  recovered from this paper.
- Figure 26's caption says that scratch was omitted for clarity, and the next
  paragraph recycles scratch constants. Consequently, “without garbage” is
  not safely readable as “without returned clean ancillary wires.”

Modern primary literature confirms why this qualification matters. Aaronson,
Grier, and Schaeffer prove Fredkin completeness with five returned ancillas
under explicitly free swaps and note that the 1982 Silver result was stated
without proof and with an unknown ancilla count. Xu later gives a one-ancilla
construction and proves an ancilla-free reading false even with borrowed bits.
Those external results guide adversarial checks; no unformalized external
construction will be installed as a Lean theorem.

## Current Repository Boundary

- `BitState n` is `Fin n -> Bool`; `hammingWeight` counts true wires.
- `Conservative n` is an equivalence plus a separate weight-preservation proof.
- `Circuit n` has exactly identity, unit wire, paper-convention zero-controlled
  Fredkin, arbitrary structural `WirePerm n`, serial composition, and disjoint
  tensor. There is no arbitrary semantic-gate constructor.
- `Circuit.permute` is an allowed zero-delay structural port reindexing. It is
  not a theorem that physical routing has been synthesized from Fredkin gates.
- Stage 8 supplies exact `(0^n,1^n)` and `(y,not y)` result registers and
  compute-copy-uncompute for an already supplied realization. It does not
  synthesize an arbitrary function or conservative endomap.

## Corrected Formal Contract

### Hamming layers

Add a semantic completeness leaf defining

- `WeightLayer n weight := {x : BitState n // hammingWeight x = weight}`;
- restriction of a `Conservative n` to every `WeightLayer n weight`;
- assembly of independent layer permutations into a `Conservative n` through
  an explicit sigma decomposition of all states by their exact weight.

Prove that two finite, injective state families paired pointwise at equal
weight extend to a total conservative permutation. The construction will use
`Equiv.Perm.exists_extending_pair` separately in every layer and will be
documented as classical and noncanonical.

### Figure 25

For every finite `f : BitState m -> BitState n`, prove existence of a total
`Conservative (m + (n + n))` extending exactly

`(x, resultRegisterInput n) -> (x, resultRegisterOutput (f x))`.

This is semantic gate existence, not yet fixed-basis synthesis.

### Direct semantic realization

Define direct realization by one arbitrary conservative gate, and prove

`DirectlyRealizable f <-> IsReversible f and WeightPreserving f`

for a same-width endomap only. The predicate must not mention `Circuit` and
must not be presented as Fredkin synthesis.

### Fixed-basis completeness

Prove a general theorem named `fredkin_complete_conservative` for arbitrary
data width `n` and `gate : Conservative n`.  Its witness is a
`CleanFredkinRealization gate.toEquiv`, whose public fields expose:

- a concrete finite `ancillaWidth` selected by the proof;
- one exact `ancillaInit : BitState ancillaWidth`, including every zero and one
  constant;
- `circuit : Circuit (ancillaWidth + n)`;
- the complete initialized-state equation

  `eval circuit (clean ++ data) = clean ++ gate(data)`;

- bit-for-bit restoration of every ancillary wire and hence no garbage;
- a recursive syntax certificate excluding `unitWire` and allowing only paper
  Fredkin, identity, serial/tensor composition, and structural `WirePerm`;
- a zero-latency certificate for that corrected feed-forward syntax.

The checked construction isolates one Johnson-graph edge, rather than assuming
an external Fredkin-completeness theorem:

1. For `n = m + 2`, an explicit conventional `patternMatch` source circuit
   recognizes the first `m` data bits.  Its true and false literal branches are
   separate syntax, and the existing compiler makes all source constants and
   garbage explicit.
2. Existing compute-copy-uncompute turns that predicate into a returned
   dual-rail marker.  One real paper Fredkin conditionally exchanges the last
   two data bits, and the predicate computation is inverted exactly.
3. This canonical macro swaps only `(pattern,0,1)` and `(pattern,1,0)`.  Its
   ancillary width is `sourceWidth(patternMatch pattern) + 2 <= 3*m + 3`, its
   complete width is at most `4*m + 5`, and its exact Fredkin count is proved.
4. A structural wire conjugation routes any true/false coordinate exchange to
   the final pair.  This changes no value-dependent resource and is explicitly
   the library's admitted reindexing convention.
5. Equal-weight states form a connected Johnson graph.  The subgroup of clean
   realizable state permutations contains every edge transposition, so the
   finite permutation-group closure theorem supplies every conservative
   permutation.  Clean composition concatenates independently returned
   ancillary blocks.

The common one-controlled Fredkin convention will not be smuggled in. It is
implemented as the paper's zero-controlled Fredkin followed by the explicit
data-wire swap; the theorem therefore remains about the repository basis.

This route proves existence of a concrete finite clean block but does not expose
a useful uniform closed-form bound for the final group-closure witness: the
subgroup proof may concatenate blocks for multiple transpositions.  The earlier
direct `2*n + 7` marker design remains a checked design sketch, not the theorem
installed in Lean.  No optimality claim is made.

### False no-ancilla reading

Add a separate parity leaf and prove:

- every `Circuit 4` evaluation has global permutation sign `+1`, including
  arbitrary structural `WirePerm 4` nodes;
- the total state transposition `1100 <-> 1010`, fixing every other state, is
  bijective and Hamming-weight preserving but has sign `-1`;
- no `Circuit 4` has that complete-state semantics.

The proof is structural over arbitrary circuit syntax. Only the finite lemma
that all 24 structural four-wire reindexings induce even state permutations is
kernel-checked by exhaustive `decide`; the circuit theorem itself is not an
enumeration of syntax.

External generator enumeration is a redundant audit, not the proof. With
paper Fredkin plus structural wire permutations, widths one, two, and three
generate the full conservative group; widths four, five, and six have indices
`2`, `4`, and `8`. Hence width four is the minimal counterexample.

### Figure 25 fixed-basis corollary

Combine the noncanonical Figure 25 extension with
`fredkin_complete_conservative`. The corollary must expose both the
`m + 2n` visible Figure 25 register and the completeness workspace, and must
return the latter exactly. It may not call the extension canonical or claim
that Figure 25 itself supplied a small circuit.

## Resource and Terminology Decisions

- “Fredkin complete” means paper Fredkin plus explicitly permitted structural
  reindexing. It does not mean physical permutation routing has been compiled.
- Identity nodes are structural. Unit wires are excluded from the synthesis
  witness, rather than being silently included through Section 2.5.
- “Clean” means one exact known mixed Boolean state, not necessarily all zero.
- “No garbage” means the complete ancillary register is returned bit for bit.
- The returned scratch is visible in the theorem even though Figure 26 omits
  it from the drawing.
- The canonical edge macro has explicit linear local bounds.  The final
  completeness theorem exposes its selected finite ancillary width but makes
  no global linear, least-space, least-time, gate-count, or physical line-count
  claim.
- The Margolus all-zero source/workspace conversion remains unresolved unless
  an independent proof is reconstructed.
- The paper's `exp(m)` and proportional-to-`m` endpoint assertions remain
  unresolved absent their missing family and cost definitions.
- A fixed finite iterate is another finite conservative permutation. A closed
  iterative computer with feedback, initialization, and delay remains Stage
  10.

## Planned Public Surface

The names may be refined for Lean elaboration, but the distinctions may not be
collapsed:

```text
Completeness.WeightLayer
Conservative.onWeightLayer
Conservative.ofWeightLayers
exists_conservative_extending_pair
exists_figure25_conservative
DirectlyRealizable
direct_realization_iff

Circuit.FredkinStructural
CleanFredkinRealization
CleanFredkinRealizable
oneControlledFredkin
patternMatch
adjacentTranspositionCircuit
adjacentTranspositionClean
Conservative.weightLayer_exchange_connected
fredkin_complete_conservative
figure25_fredkin_complete

middleLayerSwapConservative
circuit_four_even
middleLayerSwap_not_circuit
```

The parity counterexample may remain in a separate public correction leaf,
but the exhaustive group harness stays under `ConservativeLogic.Audit`.

## Adversarial Matrix

The audit must cover at least:

- widths `0`, `1`, `2`, `3`, and the minimal obstructed width `4`;
- result width zero in Figure 25;
- a noninjective arbitrary `f` in Figure 25, confirming that retained `x`, not
  injectivity of `f`, makes the initialized slice injective;
- two different states with the same weight and two with different weights;
- rejection of extending a paired family whose target weight differs;
- paper zero-control versus derived one-control truth rows;
- true- and false-literal pattern steps, preventing a hidden NOT;
- both directions of the isolated transposition;
- a third state fixed by that transposition;
- nonzero initialized scratch and exact restoration;
- active `WirePerm` direction and data/scratch block order;
- the odd four-wire target versus even circuit invariant;
- absence of `unitWire`, generic semantic gates, fan-out, weakening, and
  contraction in synthesis witnesses;
- Figure 25 semantic existence kept separate from its fixed-basis corollary;
- finite iterate wording kept separate from feedback execution.

## Verification Plan

Run focused builds for each new public leaf, the API/root build, and the
non-public audit. Then run an uncontended clean default build and rebuild the
audit after the clean. Print axioms for the layer assembly, extension theorem,
Figure 25 theorem, direct iff, fixed-basis theorem, parity invariant, and
counterexample. Expected axioms are only standard Lean/mathlib classical or
quotient principles; no project axiom, `sorry`, unsafe proof shortcut, or
native-code trust axiom is acceptable in the public results.

Scan new public and audit files for placeholders, accidental broad imports,
generic semantic-gate constructors, hidden fan-out language, unsupported
physical claims, and stale Stage 9 markers. Inspect the final diff and confirm
that unrelated synchronized changes were not overwritten.
