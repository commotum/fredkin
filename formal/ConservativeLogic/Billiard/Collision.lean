import ConservativeLogic.Billiard.Interface

/-!
# A local discrete collision permutation

This module supplies a deliberately narrow sampled collision rule on four
ordered channels `(A,B,C,D)`.  The two-ball straight mask `0110` is exchanged
with the two-ball deflected mask `1001`; zero- and one-ball masks are fixed.
On the initialized slice `(0,q,p,0)`, that rule is exactly the interaction
encoder from Section 6.2.

`map` is defined on all sixteen raw masks so that its reversibility and weight
preservation can be stated with the existing finite-state API.  Its identity
behavior on masks outside `AllowedLocal` is only an algebraic completion.  It
is not a rule for three-ball, four-ball, or unselected simultaneous physical
collisions.  The selected local abstraction interface is `AllowedState` and
its restricted equivalence `allowedEquiv`.

Nothing here models continuous trajectories, radius, elastic impact, mirrors,
clearance, or a global lattice evolution.
-/

namespace ConservativeLogic.Billiard.Collision

/-- Both straight-through singleton channels occupied: `(A,B,C,D) = 0110`. -/
def straightPair : BitState 4 :=
  Interaction.output false true true false

/-- Both deflected channels occupied: `(A,B,C,D) = 1001`. -/
def deflectedPair : BitState 4 :=
  Interaction.output true false false true

/-- The two selected two-ball masks are distinct. -/
theorem straightPair_ne_deflectedPair : straightPair ≠ deflectedPair := by
  decide

/--
Exchange the selected straight and deflected pairs, fixing every other raw
mask.  The fallback cases make a total permutation; only `AllowedLocal` is
given collision semantics.
-/
def map (state : BitState 4) : BitState 4 :=
  if state = straightPair then deflectedPair
  else if state = deflectedPair then straightPair
  else state

/-- The selected straight pair scatters to the selected deflected pair. -/
@[simp]
theorem map_straightPair : map straightPair = deflectedPair := by
  simp [map]

/-- Reversing the local orientation maps the deflected pair back to the straight pair. -/
@[simp]
theorem map_deflectedPair : map deflectedPair = straightPair := by
  simp [map, Ne.symm straightPair_ne_deflectedPair]

/-- Every mask other than the selected pair states is fixed. -/
theorem map_of_ne {state : BitState 4}
    (notStraight : state ≠ straightPair)
    (notDeflected : state ≠ deflectedPair) :
    map state = state := by
  simp [map, notStraight, notDeflected]

/-- The completed local collision map is its own inverse on all raw masks. -/
theorem map_involutive : Function.Involutive map := by
  intro state
  by_cases straight : state = straightPair
  · subst state
    simp
  · by_cases deflected : state = deflectedPair
    · subst state
      simp
    · rw [map_of_ne straight deflected]
      exact map_of_ne straight deflected

/-- The total algebraic completion bundled with its explicit inverse. -/
def equiv : Reversible 4 where
  toFun := map
  invFun := map
  left_inv := map_involutive
  right_inv := map_involutive

/-- Applying the bundled equivalence agrees with the completed collision map. -/
@[simp]
theorem equiv_apply (state : BitState 4) : equiv state = map state := rfl

/-- The completed collision permutation preserves occupied-channel count. -/
theorem map_weightPreserving : WeightPreserving map := by
  intro state
  by_cases straight : state = straightPair
  · subst state
    decide
  · by_cases deflected : state = deflectedPair
    · subst state
      decide
    · rw [map_of_ne straight deflected]

/-- The total algebraic completion as an equal-width conservative map. -/
def conservative : Conservative 4 where
  toEquiv := equiv
  weight_preserving := map_weightPreserving

/-- Applying the conservative bundle agrees with the completed collision map. -/
@[simp]
theorem conservative_apply (state : BitState 4) : conservative state = map state := rfl

/--
Admitted local masks contain at most one ball, or exactly one of the two
selected two-ball event patterns.  All other simultaneous masks are excluded.
-/
def AllowedLocal (state : BitState 4) : Prop :=
  hammingWeight state ≤ 1 ∨ state = straightPair ∨ state = deflectedPair

/-- Both selected two-ball masks are admitted local states. -/
theorem straightPair_allowed : AllowedLocal straightPair :=
  Or.inr (Or.inl rfl)

/-- Both selected two-ball masks are admitted local states. -/
theorem deflectedPair_allowed : AllowedLocal deflectedPair :=
  Or.inr (Or.inr rfl)

/-- The collision permutation preserves and reflects the admitted-state condition. -/
theorem map_allowed_iff (state : BitState 4) :
    AllowedLocal (map state) ↔ AllowedLocal state := by
  by_cases straight : state = straightPair
  · subst state
    simp only [map_straightPair]
    exact ⟨fun _ => straightPair_allowed, fun _ => deflectedPair_allowed⟩
  · by_cases deflected : state = deflectedPair
    · subst state
      simp only [map_deflectedPair]
      exact ⟨fun _ => deflectedPair_allowed, fun _ => straightPair_allowed⟩
    · rw [map_of_ne straight deflected]

/-- Forward closure of the admitted local-state predicate. -/
theorem map_preserves_allowed {state : BitState 4}
    (allowed : AllowedLocal state) : AllowedLocal (map state) :=
  (map_allowed_iff state).2 allowed

/-- A raw mask equipped with the selected local-event legality proof. -/
def AllowedState := {state : BitState 4 // AllowedLocal state}

/-- The completed collision permutation restricted to its admitted local states. -/
def allowedEquiv : AllowedState ≃ AllowedState where
  toFun state := ⟨map state.1, map_preserves_allowed state.2⟩
  invFun state := ⟨map state.1, map_preserves_allowed state.2⟩
  left_inv state := Subtype.ext (map_involutive state.1)
  right_inv state := Subtype.ext (map_involutive state.1)

/-- The restricted local step still preserves the exact number of occupied channels. -/
theorem allowedEquiv_weight (state : AllowedState) :
    hammingWeight (allowedEquiv state).1 = hammingWeight state.1 :=
  map_weightPreserving state.1

/--
Outside the admitted subtype the total map is identity.  This theorem records
the algebraic fallback explicitly; it does not assign those masks a physical
collision interpretation.
-/
theorem map_of_not_allowed {state : BitState 4}
    (notAllowed : ¬ AllowedLocal state) : map state = state := by
  apply map_of_ne
  · intro equality
    apply notAllowed
    rw [equality]
    exact straightPair_allowed
  · intro equality
    apply notAllowed
    rw [equality]
    exact deflectedPair_allowed

/-- Embed an ordered interaction input `(p,q)` as straight channels `(0,q,p,0)`. -/
def embed (value : BitState 2) : BitState 4 :=
  Interaction.output false (value 1) (value 0) false

/-- Coordinate form of the initialized local collision slice. -/
@[simp]
theorem embed_input (p q : Bool) :
    embed (Interaction.input p q) = Interaction.output false q p false := rfl

private theorem map_embed_input (p q : Bool) :
    map (embed (Interaction.input p q)) =
      Interaction.encode (Interaction.input p q) := by
  cases p <;> cases q <;> rfl

/-- The local collision rule refines the exact constrained interaction encoder. -/
theorem map_embed (value : BitState 2) :
    map (embed value) = Interaction.encode value := by
  rw [← Interaction.input_eta value]
  exact map_embed_input (value 0) (value 1)

private theorem embed_input_allowed (p q : Bool) :
    AllowedLocal (embed (Interaction.input p q)) := by
  cases p <;> cases q
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl rfl)

/-- Every initialized two-input slice is an admitted local collision state. -/
theorem embed_allowed (value : BitState 2) : AllowedLocal (embed value) := by
  rw [← Interaction.input_eta value]
  exact embed_input_allowed (value 0) (value 1)

/-- Package an initialized interaction input in the admitted local-state subtype. -/
def embedAllowed (value : BitState 2) : AllowedState :=
  ⟨embed value, embed_allowed value⟩

/-- The initialized embedding itself preserves the number of balls. -/
theorem embed_weightPreserving : WeightPreserving embed := by
  intro value
  rw [← Interaction.input_eta value]
  cases value 0 <;> cases value 1 <;> rfl

/-- The scattered initialized slice remains within the admitted local subtype. -/
theorem map_embed_allowed (value : BitState 2) :
    AllowedLocal (map (embed value)) :=
  map_preserves_allowed (embed_allowed value)

/-- The scattered initialized slice is a valid constrained interaction output. -/
theorem map_embed_validOutput (value : BitState 2) :
    Interaction.IsValidOutput (map (embed value)) := by
  refine ⟨value, ?_⟩
  exact (map_embed value).symm

/-- The complete initialized collision step preserves the input ball count. -/
theorem map_embed_weight (value : BitState 2) :
    hammingWeight (map (embed value)) = hammingWeight value := by
  exact (map_weightPreserving (embed value)).trans (embed_weightPreserving value)

end ConservativeLogic.Billiard.Collision
