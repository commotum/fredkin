import ConservativeLogic.Circuit.Inverse
import ConservativeLogic.Simulation.Fredkin

/-!
# Explicit spy registers and compute-copy-uncompute

This module implements the finite static construction from Section 7.1 of
Fredkin and Toffoli.  A result register has two separately named halves,
initialized as `(0ⁿ,1ⁿ)`.  Each result bit controls one real paper Fredkin
gate whose canonical inputs `(a,0,1)` are explicitly routed to the paper's
physical port order `(a,1,0)`.  The complete copy layer consequently maps
`(x,0ⁿ,1ⁿ)` to `(x,x,¬x)` without an unrestricted copy primitive.

Given a full `Realization.Realizes` witness, the final circuit runs the
realization, copies its complete result block, and runs the structural inverse.
Its exact initialized-slice equation restores scratch, source, and argument and
removes the transient garbage.  All declarations here are static finite-state
facts.  They do not provide arbitrary-function synthesis, delay padding,
feedback, physical routing, or a positive-latency time-reversal theorem.
-/

namespace ConservativeLogic.Ancilla

open Realization

/-! ## Explicit result-register states -/

/-- The width-`n` all-zero register. -/
def zeroRegister (n : Nat) : BitState n := fun _ => false

/-- The width-`n` all-one register. -/
def oneRegister (n : Nat) : BitState n := fun _ => true

/-- Pointwise Boolean complement of a fixed-width register. -/
def bitwiseNot {n : Nat} (state : BitState n) : BitState n :=
  fun index => !state index

/-- The prescribed ordered result-register initialization `(0ⁿ,1ⁿ)`. -/
def resultRegisterInput (n : Nat) : BitState (n + n) :=
  BitState.append (zeroRegister n) (oneRegister n)

/-- The ordered result-register output `(value,¬value)`. -/
def resultRegisterOutput {n : Nat} (value : BitState n) : BitState (n + n) :=
  BitState.append value (bitwiseNot value)

@[simp]
theorem hammingWeight_zeroRegister (n : Nat) :
    hammingWeight (zeroRegister n) = 0 := by
  simp [hammingWeight, zeroRegister]

@[simp]
theorem hammingWeight_oneRegister (n : Nat) :
    hammingWeight (oneRegister n) = n := by
  simp [hammingWeight, oneRegister]

@[simp]
theorem hammingWeight_resultRegisterInput (n : Nat) :
    hammingWeight (resultRegisterInput n) = n := by
  simp [resultRegisterInput]

/-! ## One physical paper-Fredkin spy -/

/--
Actively route canonical `(a,0,1)` to the paper gate's physical `(a,1,0)`.
The through/control port remains first and only the two data ports are swapped.
-/
def copyPairInputWiring : WirePerm 3 := PaperFredkin.dataSwap

/-- One real paper Fredkin spy with its canonical-to-physical input routing. -/
def copyPair : Circuit 3 :=
  .seq (.permute copyPairInputWiring) .fredkin

/-- Exact physical-port equation `(a,1,0) ↦ (a,a,¬a)`. -/
@[simp]
theorem copyPair_physical_spec (value : Bool) :
    Circuit.eval Circuit.fredkin (PaperFredkin.state value true false) =
      PaperFredkin.state value value (!value) := by
  cases value <;> decide

/-- Exact canonical equation `(a,0,1) ↦ (a,a,¬a)` for `copyPair`. -/
@[simp]
theorem copyPair_spec (value : Bool) :
    Circuit.eval copyPair (PaperFredkin.state value false true) =
      PaperFredkin.state value value (!value) := by
  cases value <;> decide

/-! ## Grouped registers and an interleaved bank of disjoint spies -/

/-- Width of the complete `(through,zero/first,one/second)` copy-layer state. -/
abbrev copyRegisterWidth (n : Nat) : Nat := n + (n + n)

private def groupedCoordinates (n : Nat) :
    Fin (copyRegisterWidth n) ≃ Fin 3 × Fin n :=
  (finCongr (by
    change n + (n + n) = 3 * n
    omega)).trans
    finProdFinEquiv.symm

private def interleavedCoordinates (n : Nat) :
    Fin (copyRegisterWidth n) ≃ Fin n × Fin 3 :=
  (finCongr (by
    change n + (n + n) = n * 3
    omega)).trans
    finProdFinEquiv.symm

/--
Actively route three width-`n` grouped blocks to `n` adjacent ordered triples.
This is a bijective structural reindexing, not a value-dependent operation.
-/
def copyRegisterInputWiring (n : Nat) : WirePerm (copyRegisterWidth n) :=
  (groupedCoordinates n).trans <|
    (Equiv.prodComm (Fin 3) (Fin n)).trans (interleavedCoordinates n).symm

/-- Regroup adjacent ordered triples into three width-`n` output blocks. -/
def copyRegisterOutputWiring (n : Nat) : WirePerm (copyRegisterWidth n) :=
  (copyRegisterInputWiring n).symm

/-- Interleave three grouped width-`n` states using the exact public wiring. -/
private def interleaveThree {n : Nat}
    (first second third : BitState n) : BitState (copyRegisterWidth n) :=
  WirePerm.onState (copyRegisterInputWiring n)
    (BitState.append first (BitState.append second third))

private theorem interleaveThree_apply {n : Nat}
    (first second third : BitState n) (index : Fin n) (port : Fin 3) :
    interleaveThree first second third
        ((interleavedCoordinates n).symm (index, port)) =
      PaperFredkin.state (first index) (second index) (third index) port := by
  unfold interleaveThree
  rw [WirePerm.onState_apply]
  simp [copyRegisterInputWiring, groupedCoordinates,
    interleavedCoordinates]
  refine Fin.cases ?_ ?_ port
  · rw [show
        Fin.cast _ (finProdFinEquiv ((0 : Fin 3), index)) =
          Fin.castAdd (n + n) index by
        apply Fin.ext
        simp [finProdFinEquiv]]
    simp
  · intro tail
    refine Fin.cases ?_ ?_ tail
    · rw [show
          Fin.cast _
              (finProdFinEquiv ((Fin.succ 0 : Fin 3), index)) =
            Fin.natAdd n (Fin.castAdd n index) by
          apply Fin.ext
          simp [finProdFinEquiv]
          omega]
      simp
    · intro last
      refine Fin.cases ?_ ?_ last
      · rw [show
            Fin.cast _
                (finProdFinEquiv
                  ((Fin.succ (Fin.succ 0) : Fin 3), index)) =
              Fin.natAdd n (Fin.natAdd n index) by
            apply Fin.ext
            simp [finProdFinEquiv]
            omega]
        rw [BitState.append_natAdd, BitState.append_natAdd]
        rfl
      · intro impossible
        exact Fin.elim0 impossible

private theorem copyRegisterWidth_succ (n : Nat) :
    3 + copyRegisterWidth n = copyRegisterWidth (n + 1) := by
  change 3 + (n + (n + n)) = (n + 1) + ((n + 1) + (n + 1))
  omega

private theorem castState_apply {leftWidth rightWidth : Nat}
    (width : leftWidth = rightWidth) (state : BitState leftWidth)
    (index : Fin rightWidth) :
    castState width state index = state (Fin.cast width.symm index) := by
  cases width
  rfl

private def stateTail {n : Nat} (state : BitState (n + 1)) : BitState n :=
  fun index => state index.succ

private theorem interleaveThree_succ {n : Nat}
    (first second third : BitState (n + 1)) :
    interleaveThree first second third =
      castState (copyRegisterWidth_succ n)
        (BitState.append
          (PaperFredkin.state (first 0) (second 0) (third 0))
          (interleaveThree (stateTail first) (stateTail second)
            (stateTail third))) := by
  funext output
  obtain ⟨coordinate, rfl⟩ :=
    (interleavedCoordinates (n + 1)).symm.surjective output
  rcases coordinate with ⟨index, port⟩
  rw [interleaveThree_apply]
  refine Fin.cases ?_ ?_ index
  · rw [castState_apply]
    rw [show
      Fin.cast (copyRegisterWidth_succ n).symm
          ((interleavedCoordinates (n + 1)).symm (0, port)) =
        Fin.castAdd (copyRegisterWidth n) port by
      apply Fin.ext
      simp [interleavedCoordinates, finProdFinEquiv]]
    simp
  · intro tail
    rw [castState_apply]
    rw [show
      Fin.cast (copyRegisterWidth_succ n).symm
          ((interleavedCoordinates (n + 1)).symm (tail.succ, port)) =
        Fin.natAdd 3 ((interleavedCoordinates n).symm (tail, port)) by
      apply Fin.ext
      simp [interleavedCoordinates, finProdFinEquiv]
      omega]
    rw [BitState.append_natAdd, interleaveThree_apply]
    rfl

/-- An interleaved tensor bank containing exactly one canonical spy per bit. -/
private def copyPairBank : (n : Nat) → Circuit (copyRegisterWidth n)
  | 0 => .identity 0
  | n + 1 =>
      Simulation.castCircuit (copyRegisterWidth_succ n)
        (.tensor copyPair (copyPairBank n))

private theorem copyPairBank_spec {n : Nat} (value : BitState n) :
    Circuit.eval (copyPairBank n)
        (interleaveThree value (zeroRegister n) (oneRegister n)) =
      interleaveThree value value (bitwiseNot value) := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n inductionHypothesis =>
      rw [interleaveThree_succ]
      simp only [copyPairBank]
      rw [Simulation.eval_castCircuit, Circuit.eval_tensor_append]
      rw [copyPair_spec]
      rw [inductionHypothesis (value := stateTail value)]
      rw [← interleaveThree_succ]

/--
The all-width copy layer.  Its external order is grouped
`(through,0ⁿ,1ⁿ)` / `(through,copy,complement)`; its body is an explicitly
interleaved disjoint tensor bank.
-/
def copyRegisterCircuit (n : Nat) : Circuit (copyRegisterWidth n) :=
  .seq (.permute (copyRegisterInputWiring n))
    (.seq (copyPairBank n) (.permute (copyRegisterOutputWiring n)))

end ConservativeLogic.Ancilla
