import ConservativeLogic.Reversible.Core

/-!
# Constrained logical interfaces for the billiard-ball gates

The interaction and switch gates in Sections 6.2 and 6.4 of Fredkin and
Toffoli's paper have two input rails but respectively four and three output
rails.  Their raw output spaces are therefore larger than their input spaces.
This module models each gate as an equivalence onto its exact range, rather
than pretending that either encoder is an equal-width reversible gate.

These are Boolean boundary semantics only.  They do not supply ball
trajectories, collision dynamics, mirrors, routing, delay, or a physical
realization theorem.
-/

namespace ConservativeLogic.Billiard

/-- Number of unoccupied rails at a fixed-width Boolean boundary. -/
def vacancies {width : Nat} (value : BitState width) : Nat :=
  width - hammingWeight value

namespace Interaction

/-- An explicitly ordered interaction-gate input `(p,q)`. -/
def input (p q : Bool) : BitState 2 :=
  BitState.append (fun _ : Fin 1 => p) (fun _ : Fin 1 => q)

/-- The first coordinate of an explicitly ordered interaction input. -/
@[simp]
theorem input_first (p q : Bool) : input p q 0 = p := rfl

/-- The second coordinate of an explicitly ordered interaction input. -/
@[simp]
theorem input_second (p q : Bool) : input p q 1 = q := rfl

/-- Every width-two state is recovered from its ordered coordinates. -/
@[simp]
theorem input_eta (value : BitState 2) : input (value 0) (value 1) = value := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro impossible
  exact Fin.elim0 impossible

/-- An explicitly ordered interaction output `(A,B,C,D)`. -/
def output (a b c d : Bool) : BitState 4 :=
  BitState.append (fun _ : Fin 1 => a)
    (BitState.append (fun _ : Fin 1 => b)
      (BitState.append (fun _ : Fin 1 => c) (fun _ : Fin 1 => d)))

/-- Coordinate `A` of an explicitly ordered interaction output. -/
@[simp]
theorem output_a (a b c d : Bool) : output a b c d 0 = a := rfl

/-- Coordinate `B` of an explicitly ordered interaction output. -/
@[simp]
theorem output_b (a b c d : Bool) : output a b c d 1 = b := rfl

/-- Coordinate `C` of an explicitly ordered interaction output. -/
@[simp]
theorem output_c (a b c d : Bool) : output a b c d 2 = c := rfl

/-- Coordinate `D` of an explicitly ordered interaction output. -/
@[simp]
theorem output_d (a b c d : Bool) : output a b c d 3 = d := rfl

/-- Every width-four state is recovered from its ordered coordinates. -/
@[simp]
theorem output_eta (value : BitState 4) :
    output (value 0) (value 1) (value 2) (value 3) = value := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro k
  refine Fin.cases rfl ?_ k
  intro l
  refine Fin.cases rfl ?_ l
  intro impossible
  exact Fin.elim0 impossible

/--
Figure 13's exact rail order:
`(p,q) ↦ (p q, ¬p q, p ¬q, p q)`.
-/
def encode (value : BitState 2) : BitState 4 :=
  output
    (value 0 && value 1)
    (!value 0 && value 1)
    (value 0 && !value 1)
    (value 0 && value 1)

/-- Parametric form of the interaction table in the paper's rail order. -/
@[simp]
theorem encode_input (p q : Bool) :
    encode (input p q) = output (p && q) (!p && q) (p && !q) (p && q) := rfl

/-- The `A` output is the selected logical AND coordinate. -/
@[simp]
theorem encode_a (value : BitState 2) : encode value 0 = (value 0 && value 1) := rfl

/--
Supplying one ball on `q` exposes `p` and `¬p` on named rails, with the full
four-rail output retained.  This is a fixed occupied source, not a free mirror.
-/
theorem not_with_true_source (p : Bool) :
    encode (input p true) = output p (!p) false p := by
  cases p <;> rfl

/-- Raw coordinate decoder; it is an inverse only on valid outputs. -/
def decodeRaw (value : BitState 4) : BitState 2 :=
  input (value 0 || value 2) (value 0 || value 1)

/-- Decoding an encoded interaction input recovers both input bits. -/
@[simp]
theorem decodeRaw_encode (value : BitState 2) : decodeRaw (encode value) = value := by
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> rfl

/-- A raw four-rail value is valid exactly when the encoder can produce it. -/
def IsValidOutput (value : BitState 4) : Prop :=
  ∃ inputValue : BitState 2, encode inputValue = value

/-- The constrained four-rail output interface of the interaction gate. -/
def ValidOutput := {value : BitState 4 // IsValidOutput value}

/-- Package every encoded input with its range witness. -/
def toValidOutput (value : BitState 2) : ValidOutput :=
  ⟨encode value, value, rfl⟩

/-- Decode a constrained interaction output. -/
def decode (value : ValidOutput) : BitState 2 :=
  decodeRaw value.1

/-- The constrained decoder is a left inverse to the encoder. -/
@[simp]
theorem decode_toValidOutput (value : BitState 2) :
    decode (toValidOutput value) = value :=
  decodeRaw_encode value

/-- Re-encoding a constrained output recovers its complete four-rail value. -/
@[simp]
theorem encode_decode (value : ValidOutput) : encode (decode value) = value.1 := by
  obtain ⟨inputValue, equality⟩ := value.2
  change encode (decodeRaw value.1) = value.1
  rw [← equality]
  rw [decodeRaw_encode]

/-- The interaction map is an equivalence onto exactly its four valid outputs. -/
def equiv : BitState 2 ≃ ValidOutput where
  toFun := toValidOutput
  invFun := decode
  left_inv := decode_toValidOutput
  right_inv value := Subtype.ext (encode_decode value)

/-- Applying the interaction equivalence exposes the raw encoder. -/
@[simp]
theorem equiv_apply_value (value : BitState 2) : (equiv value).1 = encode value := rfl

/-- Applying the inverse interaction equivalence is the constrained decoder. -/
@[simp]
theorem equiv_symm_apply (value : ValidOutput) : equiv.symm value = decode value := rfl

/-- The four-rail interaction encoding preserves the number of present balls. -/
theorem encode_weightPreserving : WeightPreserving encode := by
  intro value
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> rfl

/-- Unequal arity adds two vacant rails even though occupied-ball count is preserved. -/
theorem encode_vacancies (value : BitState 2) :
    vacancies (encode value) = vacancies value + 2 := by
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> decide

/-- A constructive finite enumeration transported through `equiv`. -/
instance validOutputFintype : Fintype ValidOutput :=
  Fintype.ofEquiv (BitState 2) equiv

/-- Exactly four of the sixteen raw four-rail states are valid outputs. -/
@[simp]
theorem card_validOutput : Fintype.card ValidOutput = 4 := by
  rw [Fintype.card_congr equiv.symm]
  rfl

/-- A raw tuple with both single-ball branches occupied is not an output. -/
def invalidBothSingles : BitState 4 := output false true true false

/-- The named raw interaction witness lies outside the constrained interface. -/
theorem invalidBothSingles_not_valid : ¬ IsValidOutput invalidBothSingles := by
  rintro ⟨inputValue, equality⟩
  have branchB : !inputValue 0 && inputValue 1 = true := by
    simpa [encode, invalidBothSingles] using congrFun equality (1 : Fin 4)
  have branchC : inputValue 0 && !inputValue 1 = true := by
    simpa [encode, invalidBothSingles] using congrFun equality (2 : Fin 4)
  cases control : inputValue 0 <;> simp [control] at branchB branchC

/-- The interaction encoder is not surjective onto all sixteen raw states. -/
theorem encode_not_surjective : ¬ Function.Surjective encode := by
  intro surjective
  obtain ⟨inputValue, equality⟩ := surjective invalidBothSingles
  exact invalidBothSingles_not_valid ⟨inputValue, equality⟩

/-- Width two and raw width four are not equivalent finite state spaces. -/
theorem no_raw_equiv : ¬ Nonempty (BitState 2 ≃ BitState 4) := by
  rintro ⟨rawEquiv⟩
  have cardinality := Fintype.card_congr rawEquiv
  have inputCard : Fintype.card (BitState 2) = 4 := by rfl
  have outputCard : Fintype.card (BitState 4) = 16 := by rfl
  have impossible : (4 : Nat) = 16 := inputCard.symm.trans (cardinality.trans outputCard)
  exact (by decide : (4 : Nat) ≠ 16) impossible

end Interaction

namespace Switch

/-- An explicitly ordered switch input `(c,x)`. -/
def input (control data : Bool) : BitState 2 :=
  BitState.append (fun _ : Fin 1 => control) (fun _ : Fin 1 => data)

/-- The control coordinate of an explicitly ordered switch input. -/
@[simp]
theorem input_control (control data : Bool) : input control data 0 = control := rfl

/-- The data coordinate of an explicitly ordered switch input. -/
@[simp]
theorem input_data (control data : Bool) : input control data 1 = data := rfl

/-- Every width-two switch input is recovered from its ordered coordinates. -/
@[simp]
theorem input_eta (value : BitState 2) : input (value 0) (value 1) = value := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro impossible
  exact Fin.elim0 impossible

/-- An explicitly ordered switch output `(c,cx,¬c x)`. -/
def output (control controlledTrue controlledFalse : Bool) : BitState 3 :=
  BitState.append (fun _ : Fin 1 => control)
    (BitState.append (fun _ : Fin 1 => controlledTrue)
      (fun _ : Fin 1 => controlledFalse))

/-- The retained-control coordinate of an explicitly ordered switch output. -/
@[simp]
theorem output_control (control controlledTrue controlledFalse : Bool) :
    output control controlledTrue controlledFalse 0 = control := rfl

/-- The `c x` coordinate of an explicitly ordered switch output. -/
@[simp]
theorem output_controlledTrue (control controlledTrue controlledFalse : Bool) :
    output control controlledTrue controlledFalse 1 = controlledTrue := rfl

/-- The `¬c x` coordinate of an explicitly ordered switch output. -/
@[simp]
theorem output_controlledFalse (control controlledTrue controlledFalse : Bool) :
    output control controlledTrue controlledFalse 2 = controlledFalse := rfl

/-- Every width-three state is recovered from its ordered coordinates. -/
@[simp]
theorem output_eta (value : BitState 3) :
    output (value 0) (value 1) (value 2) = value := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro k
  refine Fin.cases rfl ?_ k
  intro impossible
  exact Fin.elim0 impossible

/-- Figure 16's exact switch map `(c,x) ↦ (c,cx,¬c x)`. -/
def encode (value : BitState 2) : BitState 3 :=
  output (value 0) (value 0 && value 1) (!value 0 && value 1)

/-- Parametric form of all four rows of the switch table. -/
@[simp]
theorem encode_input (control data : Bool) :
    encode (input control data) =
      output control (control && data) (!control && data) := rfl

/-- Raw switch decoder; it is an inverse only on valid three-rail states. -/
def decodeRaw (value : BitState 3) : BitState 2 :=
  input (value 0) (value 1 || value 2)

/-- Decoding an encoded switch input recovers control and data. -/
@[simp]
theorem decodeRaw_encode (value : BitState 2) : decodeRaw (encode value) = value := by
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> rfl

/-- A raw three-rail value is valid exactly when the switch can produce it. -/
def IsValidOutput (value : BitState 3) : Prop :=
  ∃ inputValue : BitState 2, encode inputValue = value

/-- The constrained three-rail output interface of the switch gate. -/
def ValidOutput := {value : BitState 3 // IsValidOutput value}

/-- Package every encoded switch input with its range witness. -/
def toValidOutput (value : BitState 2) : ValidOutput :=
  ⟨encode value, value, rfl⟩

/-- Decode a constrained switch output. -/
def decode (value : ValidOutput) : BitState 2 :=
  decodeRaw value.1

/-- The constrained switch decoder is a left inverse to the encoder. -/
@[simp]
theorem decode_toValidOutput (value : BitState 2) :
    decode (toValidOutput value) = value :=
  decodeRaw_encode value

/-- Re-encoding a constrained switch output recovers all three rails. -/
@[simp]
theorem encode_decode (value : ValidOutput) : encode (decode value) = value.1 := by
  obtain ⟨inputValue, equality⟩ := value.2
  change encode (decodeRaw value.1) = value.1
  rw [← equality]
  rw [decodeRaw_encode]

/-- The switch map is an equivalence onto exactly its four valid outputs. -/
def equiv : BitState 2 ≃ ValidOutput where
  toFun := toValidOutput
  invFun := decode
  left_inv := decode_toValidOutput
  right_inv value := Subtype.ext (encode_decode value)

/-- Applying the switch equivalence exposes the raw encoder. -/
@[simp]
theorem equiv_apply_value (value : BitState 2) : (equiv value).1 = encode value := rfl

/-- Applying the inverse switch equivalence is the constrained decoder. -/
@[simp]
theorem equiv_symm_apply (value : ValidOutput) : equiv.symm value = decode value := rfl

/-- The three-rail switch encoding preserves the number of present balls. -/
theorem encode_weightPreserving : WeightPreserving encode := by
  intro value
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> rfl

/-- Unequal arity adds one vacant rail even though occupied-ball count is preserved. -/
theorem encode_vacancies (value : BitState 2) :
    vacancies (encode value) = vacancies value + 1 := by
  rw [← input_eta value]
  cases value 0 <;> cases value 1 <;> decide

/-- A constructive finite enumeration transported through `equiv`. -/
instance validOutputFintype : Fintype ValidOutput :=
  Fintype.ofEquiv (BitState 2) equiv

/-- Exactly four of the eight raw three-rail states are valid switch outputs. -/
@[simp]
theorem card_validOutput : Fintype.card ValidOutput = 4 := by
  rw [Fintype.card_congr equiv.symm]
  rfl

/-- With false control, occupation of the `c x` branch is invalid. -/
def invalidTrueBranch : BitState 3 := output false true false

/-- With true control, occupation of the `¬c x` branch is invalid. -/
def invalidFalseBranch : BitState 3 := output true false true

/-- The false-control/true-branch triple is outside the switch range. -/
theorem invalidTrueBranch_not_valid : ¬ IsValidOutput invalidTrueBranch := by
  rintro ⟨inputValue, equality⟩
  have controlFalse : inputValue 0 = false := by
    simpa [encode, invalidTrueBranch] using congrFun equality (0 : Fin 3)
  have trueBranch : inputValue 0 && inputValue 1 = true := by
    simpa [encode, invalidTrueBranch] using congrFun equality (1 : Fin 3)
  simp [controlFalse] at trueBranch

/-- The true-control/false-branch triple is outside the switch range. -/
theorem invalidFalseBranch_not_valid : ¬ IsValidOutput invalidFalseBranch := by
  rintro ⟨inputValue, equality⟩
  have controlTrue : inputValue 0 = true := by
    simpa [encode, invalidFalseBranch] using congrFun equality (0 : Fin 3)
  have falseBranch : !inputValue 0 && inputValue 1 = true := by
    simpa [encode, invalidFalseBranch] using congrFun equality (2 : Fin 3)
  simp [controlTrue] at falseBranch

/-- The switch encoder is not surjective onto all eight raw states. -/
theorem encode_not_surjective : ¬ Function.Surjective encode := by
  intro surjective
  obtain ⟨inputValue, equality⟩ := surjective invalidTrueBranch
  exact invalidTrueBranch_not_valid ⟨inputValue, equality⟩

/-- Width two and raw width three are not equivalent finite state spaces. -/
theorem no_raw_equiv : ¬ Nonempty (BitState 2 ≃ BitState 3) := by
  rintro ⟨rawEquiv⟩
  have cardinality := Fintype.card_congr rawEquiv
  have inputCard : Fintype.card (BitState 2) = 4 := by rfl
  have outputCard : Fintype.card (BitState 3) = 8 := by rfl
  have impossible : (4 : Nat) = 8 := inputCard.symm.trans (cardinality.trans outputCard)
  exact (by decide : (4 : Nat) ≠ 8) impossible

end Switch

end ConservativeLogic.Billiard
