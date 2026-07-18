import ConservativeLogic.Reversible.Core

/-!
# The paper-convention Fredkin gate

This module formalizes Table (2) of Fredkin and Toffoli's *Conservative Logic*
with port order `(u, x₁, x₂)`. The paper convention is zero-controlled:
control `false` swaps the two data values, while control `true` leaves them in
order. These declarations give static finite-state semantics only; they do not
assert a circuit realization, fan-out, delay, or a physical time-reversal law.
-/

namespace ConservativeLogic.PaperFredkin

/-- Build an explicitly ordered `(control, data₁, data₂)` gate state. -/
def state (control data₁ data₂ : Bool) : BitState 3 :=
  BitState.append (fun _ : Fin 1 => control)
    (BitState.append (fun _ : Fin 1 => data₁) (fun _ : Fin 1 => data₂))

/-- The first coordinate of an explicitly ordered gate state is its control. -/
@[simp]
theorem state_control (control data₁ data₂ : Bool) : state control data₁ data₂ 0 = control := by
  rfl

/-- The second coordinate is the first data value. -/
@[simp]
theorem state_data₁ (control data₁ data₂ : Bool) : state control data₁ data₂ 1 = data₁ := by
  rfl

/-- The third coordinate is the second data value. -/
@[simp]
theorem state_data₂ (control data₁ data₂ : Bool) : state control data₁ data₂ 2 = data₂ := by
  rfl

/-- Width-three states are equal when their ordered control and data coordinates agree. -/
theorem state_ext {left right : BitState 3}
    (hcontrol : left 0 = right 0) (hdata₁ : left 1 = right 1)
    (hdata₂ : left 2 = right 2) : left = right := by
  funext i
  refine Fin.cases hcontrol ?_ i
  intro j
  refine Fin.cases hdata₁ ?_ j
  intro k
  refine Fin.cases hdata₂ ?_ k
  intro impossible
  exact Fin.elim0 impossible

/--
The semantic coordinate permutation that fixes the control wire and swaps the
two data wires. This is a state reindexing, not a claim that a corresponding
wire-permutation circuit is available for free.
-/
def dataSwap : WirePerm 3 := Equiv.swap (1 : Fin 3) 2

@[simp]
private theorem dataSwap_control : dataSwap (0 : Fin 3) = 0 := by
  decide

@[simp]
private theorem dataSwap_data₁ : dataSwap (1 : Fin 3) = 2 := by
  decide

@[simp]
private theorem dataSwap_data₂ : dataSwap (2 : Fin 3) = 1 := by
  decide

@[simp]
private theorem dataSwap_symm : dataSwap.symm = dataSwap := by
  rfl

/--
Table (2)'s Fredkin map: control `false` selects the data swap and control
`true` selects the identity map.
-/
def map (input : BitState 3) : BitState 3 :=
  if input 0 = true then input else WirePerm.onState dataSwap input

/-- The Fredkin gate retains its control bit. -/
@[simp]
theorem map_control (input : BitState 3) : map input 0 = input 0 := by
  by_cases h : input 0 = true
  · simp [map, h]
  · rw [map, if_neg h, WirePerm.onState_apply, dataSwap_symm, dataSwap_control]

/-- The first data output follows Table (2)'s zero-controlled convention. -/
@[simp]
theorem map_data₁ (input : BitState 3) :
    map input 1 = if input 0 = true then input 1 else input 2 := by
  by_cases h : input 0 = true
  · simp [map, h]
  · rw [map, if_neg h, WirePerm.onState_apply, dataSwap_symm, dataSwap_data₁]
    simp [h]

/-- The second data output follows Table (2)'s zero-controlled convention. -/
@[simp]
theorem map_data₂ (input : BitState 3) :
    map input 2 = if input 0 = true then input 2 else input 1 := by
  by_cases h : input 0 = true
  · simp [map, h]
  · rw [map, if_neg h, WirePerm.onState_apply, dataSwap_symm, dataSwap_data₂]
    simp [h]

/-- A false control selects the explicit semantic data-wire swap. -/
theorem map_of_control_false {input : BitState 3} (h : input 0 = false) :
    map input = WirePerm.onState dataSwap input := by
  simp [map, h]

/-- A true control selects the identity state map. -/
theorem map_of_control_true {input : BitState 3} (h : input 0 = true) :
    map input = input := by
  simp [map, h]

/-- With control `false`, Table (2) swaps the ordered data values. -/
@[simp]
theorem map_state_false (data₁ data₂ : Bool) :
    map (state false data₁ data₂) = state false data₂ data₁ := by
  apply state_ext
  · rfl
  · rfl
  · rfl

/-- With control `true`, Table (2) retains the ordered data values. -/
@[simp]
theorem map_state_true (data₁ data₂ : Bool) :
    map (state true data₁ data₂) = state true data₁ data₂ := by
  simp [map]

/--
Parametric form of all eight rows of Table (2), with output order
`(control, data₁, data₂)` made explicit.
-/
@[simp]
theorem table (control data₁ data₂ : Bool) :
    map (state control data₁ data₂) =
      state control
        (if control = true then data₁ else data₂)
        (if control = true then data₂ else data₁) := by
  cases control <;> simp

/-- Applying the paper-convention Fredkin map twice restores every input. -/
theorem map_involutive : Function.Involutive map := by
  intro input
  by_cases h : input 0 = true
  · simp [map, h]
  · have hmap : map input 0 ≠ true := by
      simpa [map_control] using h
    change (if map input 0 = true then map input
      else WirePerm.onState dataSwap (map input)) = input
    rw [if_neg hmap]
    rw [map, if_neg h]
    apply state_ext <;> simp [WirePerm.onState, dataSwap]

/-- The paper-convention Fredkin map, bundled with itself as inverse. -/
def equiv : Reversible 3 where
  toFun := map
  invFun := map
  left_inv := map_involutive
  right_inv := map_involutive

/-- Applying the bundled equivalence agrees with the unbundled table map. -/
@[simp]
theorem equiv_apply (input : BitState 3) : equiv input = map input := rfl

/-- The Fredkin table map is reversible. -/
theorem map_isReversible : IsReversible map :=
  equiv.bijective

/-- The Fredkin table map preserves Hamming weight. -/
theorem map_weightPreserving : WeightPreserving map := by
  intro input
  by_cases h : input 0 = true
  · simp [map, h]
  · simpa [map, h] using WirePerm.onState_weightPreserving dataSwap input

/-- The Fredkin table map, bundled as a conservative equivalence. -/
def conservative : Conservative 3 where
  toEquiv := equiv
  weight_preserving := map_weightPreserving

/-- Applying the conservative bundle agrees with the unbundled table map. -/
@[simp]
theorem conservative_apply (input : BitState 3) : conservative input = map input := rfl

end ConservativeLogic.PaperFredkin
