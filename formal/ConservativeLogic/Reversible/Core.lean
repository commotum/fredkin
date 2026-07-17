import ConservativeLogic.State.Core

/-!
# Reversible and conservative finite Boolean maps

Reversibility and Hamming-weight preservation are independent predicates in
this module. `Reversible` packages an executable inverse, while `Conservative`
packages both an equivalence and a separate weight-preservation proof. None of
these static notions asserts involutivity, time-reversal symmetry, or circuit
realizability.
-/

namespace ConservativeLogic

/-- An ordinary finite Boolean state map is reversible when it is bijective. -/
def IsReversible {n : Nat} (f : BitState n → BitState n) : Prop :=
  Function.Bijective f

/-- A state map is weight-preserving when every output has its input's Hamming weight. -/
def WeightPreserving {m n : Nat} (f : BitState m → BitState n) : Prop :=
  ∀ x, hammingWeight (f x) = hammingWeight x

namespace IsReversible

/-- The identity state map is reversible at every width. -/
theorem identity (n : Nat) : IsReversible (id : BitState n → BitState n) :=
  Function.bijective_id

/-- Serial composition preserves reversibility. `first` is applied before `second`. -/
theorem comp {n : Nat} {first second : BitState n → BitState n}
    (hfirst : IsReversible first) (hsecond : IsReversible second) :
    IsReversible (fun x => second (first x)) := by
  constructor
  · intro x y hxy
    exact hfirst.1 (hsecond.1 hxy)
  · intro z
    obtain ⟨y, hy⟩ := hsecond.2 z
    obtain ⟨x, hx⟩ := hfirst.2 y
    exact ⟨x, by simpa [hx] using hy⟩

end IsReversible

namespace WeightPreserving

/-- The identity state map preserves Hamming weight at every width. -/
theorem identity (n : Nat) : WeightPreserving (id : BitState n → BitState n) :=
  fun _ => rfl

/-- Serial composition preserves Hamming weight, including between differing widths. -/
theorem comp {l m n : Nat} {first : BitState l → BitState m}
    {second : BitState m → BitState n} (hfirst : WeightPreserving first)
    (hsecond : WeightPreserving second) :
    WeightPreserving (fun x => second (first x)) := by
  intro x
  exact (hsecond (first x)).trans (hfirst x)

end WeightPreserving

/-- A reversible width-`n` Boolean map with an explicitly available inverse. -/
abbrev Reversible (n : Nat) := Equiv.Perm (BitState n)

namespace Reversible

/-- The identity reversible map. -/
def identity (n : Nat) : Reversible n := Equiv.refl _

/-- Serial composition of reversible maps, applying `first` before `second`. -/
def comp {n : Nat} (first second : Reversible n) : Reversible n :=
  first.trans second

/-- The selected inverse of a reversible map. -/
def inverse {n : Nat} (f : Reversible n) : Reversible n := f.symm

/-- A bundled reversible map is injective as an ordinary function. -/
theorem injective {n : Nat} (f : Reversible n) : Function.Injective f :=
  Equiv.injective f

/-- A bundled reversible map is surjective as an ordinary function. -/
theorem surjective {n : Nat} (f : Reversible n) : Function.Surjective f :=
  Equiv.surjective f

/-- A bundled reversible map satisfies the standalone reversibility predicate. -/
theorem isReversible {n : Nat} (f : Reversible n) : IsReversible f :=
  f.bijective

/-- Applying the reversible identity map changes no state. -/
@[simp]
theorem identity_apply {n : Nat} (x : BitState n) : identity n x = x := rfl

/-- The application order of serial reversible composition. -/
@[simp]
theorem comp_apply {n : Nat} (first second : Reversible n) (x : BitState n) :
    comp first second x = second (first x) := rfl

/-- Applying the selected inverse after a reversible map recovers the input. -/
@[simp]
theorem inverse_apply_apply {n : Nat} (f : Reversible n) (x : BitState n) :
    inverse f (f x) = x :=
  f.symm_apply_apply x

end Reversible

namespace WeightPreserving

/-- The inverse of a weight-preserving equivalence is weight-preserving. -/
theorem inverse {n : Nat} (f : Reversible n) (hf : WeightPreserving f) :
    WeightPreserving f.symm := by
  intro x
  have h := hf (f.symm x)
  simpa using h.symm

end WeightPreserving

/--
A reversible Boolean endomap carrying a separate Hamming-weight preservation
proof. This is the static semantic conjunction used for a conservative map; it
does not by itself claim realization by any gate basis.
-/
structure Conservative (n : Nat) where
  toEquiv : Reversible n
  weight_preserving : WeightPreserving toEquiv

namespace Conservative

/-- A conservative map can be applied as an ordinary state function. -/
instance {n : Nat} : CoeFun (Conservative n) (fun _ => BitState n → BitState n) :=
  ⟨fun f => f.toEquiv⟩

/-- Conservative maps are equal when their underlying equivalences are equal. -/
@[ext]
theorem ext {n : Nat} {f g : Conservative n} (h : f.toEquiv = g.toEquiv) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity map is conservative at every width. -/
def identity (n : Nat) : Conservative n where
  toEquiv := Reversible.identity n
  weight_preserving := WeightPreserving.identity n

/-- Serial composition of conservative maps, applying `first` before `second`. -/
def comp {n : Nat} (first second : Conservative n) : Conservative n where
  toEquiv := Reversible.comp first.toEquiv second.toEquiv
  weight_preserving :=
    WeightPreserving.comp (first := first.toEquiv) (second := second.toEquiv)
      first.weight_preserving second.weight_preserving

/-- The inverse of a conservative map is conservative. -/
def inverse {n : Nat} (f : Conservative n) : Conservative n where
  toEquiv := Reversible.inverse f.toEquiv
  weight_preserving := WeightPreserving.inverse f.toEquiv f.weight_preserving

/-- A conservative map is injective because its underlying map is an equivalence. -/
theorem injective {n : Nat} (f : Conservative n) : Function.Injective f :=
  f.toEquiv.injective

/-- A conservative map is surjective because its underlying map is an equivalence. -/
theorem surjective {n : Nat} (f : Conservative n) : Function.Surjective f :=
  f.toEquiv.surjective

/-- A conservative map satisfies the standalone reversibility predicate. -/
theorem isReversible {n : Nat} (f : Conservative n) : IsReversible f :=
  f.toEquiv.bijective

/-- Applying the conservative identity map changes no state. -/
@[simp]
theorem identity_apply {n : Nat} (x : BitState n) : identity n x = x := rfl

/-- The application order of serial conservative composition. -/
@[simp]
theorem comp_apply {n : Nat} (first second : Conservative n) (x : BitState n) :
    comp first second x = second (first x) := rfl

end Conservative

/-- A bijective permutation of the wire indices at width `n`. -/
abbrev WirePerm (n : Nat) := Equiv.Perm (Fin n)

namespace WirePerm

/--
The active action of a wire permutation on states. Old wire `i` moves to new
wire `σ i`, equivalently the new value at `i` is read from `σ.symm i`.
-/
def onState {n : Nat} (σ : WirePerm n) : Reversible n where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

/-- Pointwise form of the active wire-permutation action. -/
@[simp]
theorem onState_apply {n : Nat} (σ : WirePerm n) (x : BitState n) (i : Fin n) :
    onState σ x i = x (σ.symm i) := rfl

/-- Old wire `i` appears at new wire `σ i`. -/
@[simp]
theorem onState_apply_image {n : Nat} (σ : WirePerm n) (x : BitState n) (i : Fin n) :
    onState σ x (σ i) = x i := by
  simp [onState]

/-- The identity wire permutation induces the identity state equivalence. -/
@[simp]
theorem onState_identity (n : Nat) :
    onState (Equiv.refl (Fin n)) = Reversible.identity n := by
  ext x i
  rfl

/-- Active wire actions respect serial permutation composition. -/
theorem onState_comp {n : Nat} (first second : WirePerm n) :
    onState (first.trans second) = Reversible.comp (onState first) (onState second) := by
  ext x i
  rfl

/-- Inverting a wire permutation inverts its action on states. -/
theorem onState_inverse {n : Nat} (σ : WirePerm n) :
    onState σ.symm = Reversible.inverse (onState σ) := by
  ext x i
  rfl

private def truePositionsOnStateEquiv {n : Nat} (σ : WirePerm n) (x : BitState n) :
    {i : Fin n // onState σ x i = true} ≃ {i : Fin n // x i = true} where
  toFun i := ⟨σ.symm i.1, i.2⟩
  invFun i := ⟨σ i.1, by simpa [onState] using i.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv i := by
    apply Subtype.ext
    simp

/-- Every bijective wire reindexing preserves total Hamming weight. -/
theorem onState_weightPreserving {n : Nat} (σ : WirePerm n) :
    WeightPreserving (onState σ) := by
  intro x
  calc
    hammingWeight (onState σ x) =
        Fintype.card {i : Fin n // onState σ x i = true} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {i : Fin n // x i = true} :=
      Fintype.card_congr (truePositionsOnStateEquiv σ x)
    _ = hammingWeight x := Fintype.card_subtype _

/-- Every bijective wire permutation induces a conservative state map. -/
def conservative {n : Nat} (σ : WirePerm n) : Conservative n where
  toEquiv := onState σ
  weight_preserving := onState_weightPreserving σ

end WirePerm

end ConservativeLogic
