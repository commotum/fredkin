import ConservativeLogic.Simulation.Fredkin
import Mathlib.Tactic.FinCases

/-!
# Exact static reconstruction of Figure 7

This module reconstructs the paper's three-Fredkin demultiplexer on the complete
six-wire boundary

`(0, 0, 0, A₀, A₁, X) ↦ (Y₀, Y₁, Y₂, Y₃, A₁, A₀)`.

All three zero sources and both garbage outputs are explicit.  The syntax also
contains exactly the seven unit-wire nodes drawn in Figure 7.  The timing
theorems below establish a delay-two path for each argument/result port pair
and prove that every grammar-induced path between such a pair has delay two.
A separate zero-delay source/result path proves that the complete six-wire
term does not satisfy the library's stronger global equal-path criterion.

The active `WirePerm` nodes only encode the drawing's structural port routes;
they are zero-delay syntax here and are not a synthesis claim for physical
permutation hardware.
-/

namespace ConservativeLogic.Simulation.Demultiplexer

open Realization
open Realization.Primitive

private def fin6Perm (forward inverse : Fin 6 → Fin 6)
    (leftInverse : Function.LeftInverse inverse forward)
    (rightInverse : Function.RightInverse inverse forward) : WirePerm 6 :=
  Equiv.mk forward inverse leftInverse rightInverse

private def g1InputWiring : WirePerm 6 :=
  fin6Perm ![2, 3, 4, 5, 0, 1] ![4, 5, 0, 1, 2, 3] (by decide) (by decide)

private def g1OutputWiring : WirePerm 6 :=
  fin6Perm ![3, 4, 5, 0, 1, 2] ![3, 4, 5, 0, 1, 2] (by decide) (by decide)

private def delay1InputWiring : WirePerm 6 :=
  fin6Perm ![3, 4, 0, 5, 1, 2] ![2, 4, 5, 0, 1, 3] (by decide) (by decide)

private def delay1OutputWiring : WirePerm 6 :=
  fin6Perm ![2, 4, 5, 0, 1, 3] ![3, 4, 0, 5, 1, 2] (by decide) (by decide)

private def g2InputWiring : WirePerm 6 :=
  fin6Perm ![1, 3, 0, 4, 2, 5] ![2, 0, 4, 1, 3, 5] (by decide) (by decide)

private def g2OutputWiring : WirePerm 6 :=
  fin6Perm ![1, 4, 5, 0, 2, 3] ![3, 0, 4, 5, 1, 2] (by decide) (by decide)

private def delay2InputWiring : WirePerm 6 :=
  fin6Perm ![4, 0, 5, 1, 2, 3] ![1, 3, 4, 5, 0, 2] (by decide) (by decide)

private def delay2OutputWiring : WirePerm 6 :=
  fin6Perm ![1, 3, 4, 5, 0, 2] ![4, 0, 5, 1, 2, 3] (by decide) (by decide)

private def g3InputWiring : WirePerm 6 :=
  fin6Perm ![1, 0, 5, 2, 3, 4] ![1, 0, 3, 4, 5, 2] (by decide) (by decide)

private def g3OutputWiring : WirePerm 6 :=
  fin6Perm ![5, 0, 1, 2, 3, 4] ![1, 2, 3, 4, 5, 0] (by decide) (by decide)

private def routedGate (inputWiring outputWiring : WirePerm 6) : Circuit 6 :=
  .seq (.permute inputWiring)
    (.seq (.tensor .fredkin (.identity 3)) (.permute outputWiring))

private def threeUnitWires : Circuit 3 :=
  .tensor (.tensor .unitWire .unitWire) .unitWire

private def fourUnitWires : Circuit 4 :=
  .tensor (.tensor (.tensor .unitWire .unitWire) .unitWire) .unitWire

private def routedDelay1 : Circuit 6 :=
  .seq (.permute delay1InputWiring)
    (.seq (.tensor threeUnitWires (.identity 3)) (.permute delay1OutputWiring))

private def routedDelay2 : Circuit 6 :=
  .seq (.permute delay2InputWiring)
    (.seq (.tensor fourUnitWires (.identity 2)) (.permute delay2OutputWiring))

/-- Figure 7 as a literal six-wire term with three Fredkins and seven unit wires. -/
def demuxCircuit : Circuit 6 :=
  .seq (routedGate g1InputWiring g1OutputWiring)
    (.seq routedDelay1
      (.seq (routedGate g2InputWiring g2OutputWiring)
        (.seq routedDelay2 (routedGate g3InputWiring g3OutputWiring))))

/-- Canonical ordered three-bit state used for `(A₀,A₁,X)`. -/
def threeBits (first second third : Bool) : BitState 3 :=
  BitState.append (twoBits first second) (oneBit third)

/-- Canonical ordered four-bit state used for `(Y₀,Y₁,Y₂,Y₃)`. -/
def fourBits (a b c d : Bool) : BitState 4 :=
  BitState.append (twoBits a b) (twoBits c d)

/-- Exhaustive source/argument/result/garbage layout of the Figure 7 boundary. -/
def demuxLayout : Layout where
  sourceWidth := 3
  scratchWidth := 0
  argumentWidth := 3
  resultWidth := 4
  garbageWidth := 2
  balanced := rfl

/-- The three independently supplied zero sources in their canonical source block. -/
def demuxSource : BitState 3 := threeBits false false false

/-- One-hot selected-data outputs `(Y₀,Y₁,Y₂,Y₃)`, addressed by `(A₀,A₁)`. -/
def demuxTarget (argument : BitState 3) : BitState 4 :=
  fourBits
    (!argument 0 && !argument 1 && argument 2)
    (argument 0 && !argument 1 && argument 2)
    (!argument 0 && argument 1 && argument 2)
    (argument 0 && argument 1 && argument 2)

/-- The complete two-wire sink block `(A₁,A₀)` shown in Figure 7. -/
def demuxGarbage (argument : BitState 3) : BitState 2 :=
  twoBits (argument 1) (argument 0)

/-- Complete initialized-slice equation, including all sources and garbage. -/
theorem demux_complete (a0 a1 x : Bool) :
    Circuit.eval demuxCircuit
        (demuxLayout.packInput noBits demuxSource (threeBits a0 a1 x)) =
      demuxLayout.packOutput noBits
        (fourBits
          (!a0 && !a1 && x)
          (a0 && !a1 && x)
          (!a0 && a1 && x)
          (a0 && a1 && x))
        (twoBits a1 a0) := by
  cases a0 <;> cases a1 <;> cases x <;> decide

private theorem threeBits_eta (input : BitState 3) :
    threeBits (input 0) (input 1) (input 2) = input := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro k
  refine Fin.cases rfl ?_ k
  intro impossible
  exact Fin.elim0 impossible

/-- Figure 7 realizes the selected-data target with no hidden boundary wires. -/
theorem demux_realizes :
    Realizes demuxLayout demuxCircuit noBits demuxSource demuxTarget demuxGarbage := by
  intro argument
  change BitState 3 at argument
  rw [← threeBits_eta argument]
  exact demux_complete (argument 0) (argument 1) (argument 2)

/-- Number of literal unit-wire constructors in a circuit syntax tree. -/
def unitWireCount : {n : Nat} → Circuit n → Nat
  | _, .identity _ => 0
  | _, .unitWire => 1
  | _, .fredkin => 0
  | _, .permute _ => 0
  | _, .seq first second => unitWireCount first + unitWireCount second
  | _, .tensor left right => unitWireCount left + unitWireCount right

/-- The literal Figure 7 reconstruction contains exactly three Fredkin nodes. -/
theorem demux_fredkinCount : Circuit.fredkinCount demuxCircuit = 3 := by decide

/-- The literal reconstruction contains exactly the seven unit wires drawn in Figure 7. -/
theorem demuxCircuit_unitWireCount : unitWireCount demuxCircuit = 7 := by decide

private theorem routedGate_gatePath (inputWiring outputWiring : WirePerm 6)
    (input : Fin 6) (gateInput gateOutput : Fin 3)
    (inputAtGate : inputWiring input = Fin.castAdd 3 gateInput) :
    Circuit.PathDelay (routedGate inputWiring outputWiring) input
      (outputWiring (Fin.castAdd 3 gateOutput)) 0 := by
  have gatePath : Circuit.PathDelay (.tensor .fredkin (.identity 3))
      (inputWiring input) (Fin.castAdd 3 gateOutput) 0 := by
    rw [inputAtGate]
    exact Circuit.PathDelay.tensorLeft (right := .identity 3)
      (Circuit.PathDelay.fredkin gateInput gateOutput)
  simpa [routedGate] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute inputWiring input)
    (Circuit.PathDelay.seq gatePath
      (Circuit.PathDelay.permute outputWiring (Fin.castAdd 3 gateOutput)))

private theorem routedGate_bypassPath (inputWiring outputWiring : WirePerm 6)
    (input : Fin 6) (bypass : Fin 3)
    (inputAtBypass : inputWiring input = Fin.natAdd 3 bypass) :
    Circuit.PathDelay (routedGate inputWiring outputWiring) input
      (outputWiring (Fin.natAdd 3 bypass)) 0 := by
  have bypassPath : Circuit.PathDelay (.tensor .fredkin (.identity 3))
      (inputWiring input) (Fin.natAdd 3 bypass) 0 := by
    rw [inputAtBypass]
    exact Circuit.PathDelay.tensorRight (left := .fredkin)
      (Circuit.PathDelay.identity bypass)
  simpa [routedGate] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute inputWiring input)
    (Circuit.PathDelay.seq bypassPath
      (Circuit.PathDelay.permute outputWiring (Fin.natAdd 3 bypass)))

private theorem threeUnitWires_path (input : Fin 3) :
    Circuit.PathDelay threeUnitWires input input 1 := by
  refine Fin.cases ?_ ?_ input
  · simpa [threeUnitWires] using
      Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
        (Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
          Circuit.PathDelay.unitWire_one)
  · intro tail
    refine Fin.cases ?_ ?_ tail
    · simpa [threeUnitWires] using
        Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
          (Circuit.PathDelay.tensorRight (left := Circuit.unitWire)
            Circuit.PathDelay.unitWire_one)
    · intro last
      have : last = (0 : Fin 1) := Subsingleton.elim _ _
      subst last
      simpa [threeUnitWires] using
        Circuit.PathDelay.tensorRight (left := Circuit.tensor .unitWire .unitWire)
          Circuit.PathDelay.unitWire_one

private theorem fourUnitWires_path (input : Fin 4) :
    Circuit.PathDelay fourUnitWires input input 1 := by
  refine Fin.cases ?_ ?_ input
  · simpa [fourUnitWires] using
      Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
        (Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
          (Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
            Circuit.PathDelay.unitWire_one))
  · intro tail
    refine Fin.cases ?_ ?_ tail
    · simpa [fourUnitWires] using
        Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
          (Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
            (Circuit.PathDelay.tensorRight (left := Circuit.unitWire)
              Circuit.PathDelay.unitWire_one))
    · intro tail'
      refine Fin.cases ?_ ?_ tail'
      · simpa [fourUnitWires] using
          Circuit.PathDelay.tensorLeft (right := Circuit.unitWire)
            (Circuit.PathDelay.tensorRight
              (left := Circuit.tensor .unitWire .unitWire)
              Circuit.PathDelay.unitWire_one)
      · intro last
        have : last = (0 : Fin 1) := Subsingleton.elim _ _
        subst last
        simpa [fourUnitWires] using
          Circuit.PathDelay.tensorRight
            (left := Circuit.tensor (Circuit.tensor .unitWire .unitWire) .unitWire)
            Circuit.PathDelay.unitWire_one

private theorem routedDelay1_path (input : Fin 6) (delayed : Fin 3)
    (inputAtDelay : delay1InputWiring input = Fin.castAdd 3 delayed) :
    Circuit.PathDelay routedDelay1 input
      (delay1OutputWiring (Fin.castAdd 3 delayed)) 1 := by
  have corePath : Circuit.PathDelay (.tensor threeUnitWires (.identity 3))
      (delay1InputWiring input) (Fin.castAdd 3 delayed) 1 := by
    rw [inputAtDelay]
    exact Circuit.PathDelay.tensorLeft (right := .identity 3)
      (threeUnitWires_path delayed)
  simpa [routedDelay1] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute delay1InputWiring input)
    (Circuit.PathDelay.seq corePath
      (Circuit.PathDelay.permute delay1OutputWiring (Fin.castAdd 3 delayed)))

private theorem routedDelay1_bypassPath (input : Fin 6) (bypass : Fin 3)
    (inputAtBypass : delay1InputWiring input = Fin.natAdd 3 bypass) :
    Circuit.PathDelay routedDelay1 input
      (delay1OutputWiring (Fin.natAdd 3 bypass)) 0 := by
  have corePath : Circuit.PathDelay (.tensor threeUnitWires (.identity 3))
      (delay1InputWiring input) (Fin.natAdd 3 bypass) 0 := by
    rw [inputAtBypass]
    exact Circuit.PathDelay.tensorRight (left := threeUnitWires)
      (Circuit.PathDelay.identity bypass)
  simpa [routedDelay1] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute delay1InputWiring input)
    (Circuit.PathDelay.seq corePath
      (Circuit.PathDelay.permute delay1OutputWiring (Fin.natAdd 3 bypass)))

private theorem routedDelay2_path (input : Fin 6) (delayed : Fin 4)
    (inputAtDelay : delay2InputWiring input = Fin.castAdd 2 delayed) :
    Circuit.PathDelay routedDelay2 input
      (delay2OutputWiring (Fin.castAdd 2 delayed)) 1 := by
  have corePath : Circuit.PathDelay (.tensor fourUnitWires (.identity 2))
      (delay2InputWiring input) (Fin.castAdd 2 delayed) 1 := by
    rw [inputAtDelay]
    exact Circuit.PathDelay.tensorLeft (right := .identity 2)
      (fourUnitWires_path delayed)
  simpa [routedDelay2] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute delay2InputWiring input)
    (Circuit.PathDelay.seq corePath
      (Circuit.PathDelay.permute delay2OutputWiring (Fin.castAdd 2 delayed)))

private theorem routedDelay2_bypassPath (input : Fin 6) (bypass : Fin 2)
    (inputAtBypass : delay2InputWiring input = Fin.natAdd 4 bypass) :
    Circuit.PathDelay routedDelay2 input
      (delay2OutputWiring (Fin.natAdd 4 bypass)) 0 := by
  have corePath : Circuit.PathDelay (.tensor fourUnitWires (.identity 2))
      (delay2InputWiring input) (Fin.natAdd 4 bypass) 0 := by
    rw [inputAtBypass]
    exact Circuit.PathDelay.tensorRight (left := fourUnitWires)
      (Circuit.PathDelay.identity bypass)
  simpa [routedDelay2] using Circuit.PathDelay.seq
    (Circuit.PathDelay.permute delay2InputWiring input)
    (Circuit.PathDelay.seq corePath
      (Circuit.PathDelay.permute delay2OutputWiring (Fin.natAdd 4 bypass)))

private theorem assembleDemuxPath
    {input afterGate1 afterDelay1 afterGate2 afterDelay2 output : Fin 6}
    (gate1 : Circuit.PathDelay (routedGate g1InputWiring g1OutputWiring)
      input afterGate1 0)
    (delay1 : Circuit.PathDelay routedDelay1 afterGate1 afterDelay1 1)
    (gate2 : Circuit.PathDelay (routedGate g2InputWiring g2OutputWiring)
      afterDelay1 afterGate2 0)
    (delay2 : Circuit.PathDelay routedDelay2 afterGate2 afterDelay2 1)
    (gate3 : Circuit.PathDelay (routedGate g3InputWiring g3OutputWiring)
      afterDelay2 output 0) :
    Circuit.PathDelay demuxCircuit input output 2 := by
  simpa [demuxCircuit] using Circuit.PathDelay.seq gate1
    (Circuit.PathDelay.seq delay1
      (Circuit.PathDelay.seq gate2 (Circuit.PathDelay.seq delay2 gate3)))

/-!
The following private invariant assigns an absolute phase to every port at
each boundary between the five routed layers.  `RespectsPhase` says that a
grammar-induced path advances from its input phase to its output phase by
exactly its unit-wire delay.  This proves route-independent timing without
enumerating whole-circuit paths.
-/

private def RespectsPhase {n : Nat} (circuit : Circuit n)
    (before after : Fin n → Nat) : Prop :=
  ∀ {input output delay}, Circuit.PathDelay circuit input output delay →
    before input + delay = after output

private theorem RespectsPhase.identity {n : Nat} (phase : Fin n → Nat) :
    RespectsPhase (.identity n) phase phase := by
  rintro input output delay ⟨rfl, rfl⟩
  simp

private theorem RespectsPhase.unitWire (phase : Nat) :
    RespectsPhase .unitWire (fun _ ↦ phase) (fun _ ↦ phase + 1) := by
  intro input output delay path
  change delay = UnitWire.delay at path
  rw [path, UnitWire.delay_eq_one]

private theorem RespectsPhase.fredkin (phase : Nat) :
    RespectsPhase .fredkin (fun _ ↦ phase) (fun _ ↦ phase) := by
  intro input output delay path
  change delay = 0 at path
  omega

private theorem RespectsPhase.permute {n : Nat} (wiring : WirePerm n)
    {before after : Fin n → Nat}
    (route : ∀ input, before input = after (wiring input)) :
    RespectsPhase (.permute wiring) before after := by
  rintro input output delay ⟨rfl, rfl⟩
  simpa using route input

private theorem RespectsPhase.seq {n : Nat} {first second : Circuit n}
    {before middle after : Fin n → Nat}
    (firstPhase : RespectsPhase first before middle)
    (secondPhase : RespectsPhase second middle after) :
    RespectsPhase (.seq first second) before after := by
  rintro input output delay
    ⟨wire, firstDelay, secondDelay, firstPath, secondPath, rfl⟩
  calc
    before input + (firstDelay + secondDelay) =
        (before input + firstDelay) + secondDelay := by omega
    _ = middle wire + secondDelay := by rw [firstPhase firstPath]
    _ = after output := secondPhase secondPath

private theorem RespectsPhase.tensor {m n : Nat}
    {left : Circuit m} {right : Circuit n}
    {leftBefore leftAfter : Fin m → Nat}
    {rightBefore rightAfter : Fin n → Nat}
    (leftPhase : RespectsPhase left leftBefore leftAfter)
    (rightPhase : RespectsPhase right rightBefore rightAfter) :
    RespectsPhase (.tensor left right)
      (Fin.append leftBefore rightBefore) (Fin.append leftAfter rightAfter) := by
  intro input output delay path
  rcases path with ⟨leftInput, leftOutput, rfl, rfl, leftPath⟩ |
    ⟨rightInput, rightOutput, rfl, rfl, rightPath⟩
  · simpa using leftPhase leftPath
  · simpa using rightPhase rightPath

private theorem routedGate_respectsPhase (inputWiring outputWiring : WirePerm 6)
    (gatePhase : Nat) (bypassPhase : Fin 3 → Nat)
    (before after : Fin 6 → Nat)
    (inputRoute : ∀ input,
      before input =
        Fin.append (fun _ : Fin 3 ↦ gatePhase) bypassPhase (inputWiring input))
    (outputRoute : ∀ input,
      Fin.append (fun _ : Fin 3 ↦ gatePhase) bypassPhase input =
        after (outputWiring input)) :
    RespectsPhase (routedGate inputWiring outputWiring) before after := by
  have inputPhase := RespectsPhase.permute inputWiring inputRoute
  have corePhase := (RespectsPhase.fredkin gatePhase).tensor
    (RespectsPhase.identity bypassPhase)
  have outputPhase := RespectsPhase.permute outputWiring outputRoute
  simpa [routedGate] using inputPhase.seq (corePhase.seq outputPhase)

private def threeWirePhase (phase : Nat) : Fin 3 → Nat :=
  Fin.append (Fin.append (fun _ : Fin 1 ↦ phase) (fun _ : Fin 1 ↦ phase))
    (fun _ : Fin 1 ↦ phase)

private theorem threeUnitWires_respectsPhase (phase : Nat) :
    RespectsPhase threeUnitWires (threeWirePhase phase) (threeWirePhase (phase + 1)) := by
  have one := RespectsPhase.unitWire phase
  simpa [threeUnitWires, threeWirePhase, Nat.add_assoc] using (one.tensor one).tensor one

private def fourWirePhase (phase : Nat) : Fin 4 → Nat :=
  Fin.append
    (Fin.append (Fin.append (fun _ : Fin 1 ↦ phase) (fun _ : Fin 1 ↦ phase))
      (fun _ : Fin 1 ↦ phase))
    (fun _ : Fin 1 ↦ phase)

private theorem fourUnitWires_respectsPhase (phase : Nat) :
    RespectsPhase fourUnitWires (fourWirePhase phase) (fourWirePhase (phase + 1)) := by
  have one := RespectsPhase.unitWire phase
  simpa [fourUnitWires, fourWirePhase, Nat.add_assoc] using
    ((one.tensor one).tensor one).tensor one

private theorem gate1_respectsPhase :
    RespectsPhase (routedGate g1InputWiring g1OutputWiring)
      ![0, 1, 2, 0, 0, 0] ![1, 2, 0, 0, 0, 0] := by
  apply routedGate_respectsPhase g1InputWiring g1OutputWiring 0 ![1, 2, 0]
  · intro input
    fin_cases input <;> decide
  · intro input
    fin_cases input <;> decide

private theorem delay1_respectsPhase :
    RespectsPhase routedDelay1
      ![1, 2, 0, 0, 0, 0] ![1, 2, 1, 0, 1, 1] := by
  have inputPhase : RespectsPhase (.permute delay1InputWiring)
      ![1, 2, 0, 0, 0, 0]
      (Fin.append (threeWirePhase 0) ![1, 2, 0]) := by
    apply RespectsPhase.permute
    intro input
    fin_cases input <;> decide
  have corePhase := (threeUnitWires_respectsPhase 0).tensor
    (RespectsPhase.identity ![1, 2, 0])
  have outputPhase : RespectsPhase (.permute delay1OutputWiring)
      (Fin.append (threeWirePhase 1) ![1, 2, 0])
      ![1, 2, 1, 0, 1, 1] := by
    apply RespectsPhase.permute
    intro input
    fin_cases input <;> decide
  simpa [routedDelay1] using inputPhase.seq (corePhase.seq outputPhase)

private theorem gate2_respectsPhase :
    RespectsPhase (routedGate g2InputWiring g2OutputWiring)
      ![1, 2, 1, 0, 1, 1] ![2, 1, 0, 1, 1, 1] := by
  apply routedGate_respectsPhase g2InputWiring g2OutputWiring 1 ![2, 0, 1]
  · intro input
    fin_cases input <;> decide
  · intro input
    fin_cases input <;> decide

private theorem delay2_respectsPhase :
    RespectsPhase routedDelay2
      ![2, 1, 0, 1, 1, 1] ![2, 2, 0, 2, 2, 2] := by
  have inputPhase : RespectsPhase (.permute delay2InputWiring)
      ![2, 1, 0, 1, 1, 1]
      (Fin.append (fourWirePhase 1) ![2, 0]) := by
    apply RespectsPhase.permute
    intro input
    fin_cases input <;> decide
  have corePhase := (fourUnitWires_respectsPhase 1).tensor
    (RespectsPhase.identity ![2, 0])
  have outputPhase : RespectsPhase (.permute delay2OutputWiring)
      (Fin.append (fourWirePhase 2) ![2, 0])
      ![2, 2, 0, 2, 2, 2] := by
    apply RespectsPhase.permute
    intro input
    fin_cases input <;> decide
  simpa [routedDelay2] using inputPhase.seq (corePhase.seq outputPhase)

private theorem gate3_respectsPhase :
    RespectsPhase (routedGate g3InputWiring g3OutputWiring)
      ![2, 2, 0, 2, 2, 2] ![2, 2, 2, 2, 0, 2] := by
  apply routedGate_respectsPhase g3InputWiring g3OutputWiring 2 ![2, 2, 0]
  · intro input
    fin_cases input <;> decide
  · intro input
    fin_cases input <;> decide

private theorem demuxCircuit_respectsPhase :
    RespectsPhase demuxCircuit
      ![0, 1, 2, 0, 0, 0] ![2, 2, 2, 2, 0, 2] := by
  change ∀ {_ _ _}, _ → _
  exact gate1_respectsPhase.seq
    (delay1_respectsPhase.seq
      (gate2_respectsPhase.seq (delay2_respectsPhase.seq gate3_respectsPhase)))

private theorem a0Y0Path :
    Circuit.PathDelay demuxCircuit (3 : Fin 6) (0 : Fin 6) 2 := by
  have p1 : Circuit.PathDelay (routedGate g1InputWiring g1OutputWiring)
      (3 : Fin 6) (2 : Fin 6) 0 := by
    simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
      routedGate_bypassPath g1InputWiring g1OutputWiring (3 : Fin 6) (2 : Fin 3) (by decide)
  have p2 : Circuit.PathDelay routedDelay1 (2 : Fin 6) (2 : Fin 6) 1 := by
    simpa [delay1InputWiring, delay1OutputWiring, fin6Perm] using
      routedDelay1_path (2 : Fin 6) (0 : Fin 3) (by decide)
  have p3 : Circuit.PathDelay (routedGate g2InputWiring g2OutputWiring)
      (2 : Fin 6) (1 : Fin 6) 0 := by
    simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
      routedGate_gatePath g2InputWiring g2OutputWiring (2 : Fin 6)
        (0 : Fin 3) (0 : Fin 3) (by decide)
  have p4 : Circuit.PathDelay routedDelay2 (1 : Fin 6) (1 : Fin 6) 1 := by
    simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
      routedDelay2_path (1 : Fin 6) (0 : Fin 4) (by decide)
  have p5 : Circuit.PathDelay (routedGate g3InputWiring g3OutputWiring)
      (1 : Fin 6) (0 : Fin 6) 0 := by
    simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
      routedGate_gatePath g3InputWiring g3OutputWiring (1 : Fin 6)
        (0 : Fin 3) (1 : Fin 3) (by decide)
  exact assembleDemuxPath p1 p2 p3 p4 p5

private theorem g1A0 : Circuit.PathDelay
    (routedGate g1InputWiring g1OutputWiring) (3 : Fin 6) (2 : Fin 6) 0 := by
  simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
    routedGate_bypassPath g1InputWiring g1OutputWiring (3 : Fin 6) (2 : Fin 3) (by decide)

private theorem g1A1P : Circuit.PathDelay
    (routedGate g1InputWiring g1OutputWiring) (4 : Fin 6) (4 : Fin 6) 0 := by
  simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
    routedGate_gatePath g1InputWiring g1OutputWiring (4 : Fin 6)
      (0 : Fin 3) (1 : Fin 3) (by decide)

private theorem g1A1Q : Circuit.PathDelay
    (routedGate g1InputWiring g1OutputWiring) (4 : Fin 6) (5 : Fin 6) 0 := by
  simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
    routedGate_gatePath g1InputWiring g1OutputWiring (4 : Fin 6)
      (0 : Fin 3) (2 : Fin 3) (by decide)

private theorem g1XP : Circuit.PathDelay
    (routedGate g1InputWiring g1OutputWiring) (5 : Fin 6) (4 : Fin 6) 0 := by
  simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
    routedGate_gatePath g1InputWiring g1OutputWiring (5 : Fin 6)
      (1 : Fin 3) (1 : Fin 3) (by decide)

private theorem g1XQ : Circuit.PathDelay
    (routedGate g1InputWiring g1OutputWiring) (5 : Fin 6) (5 : Fin 6) 0 := by
  simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
    routedGate_gatePath g1InputWiring g1OutputWiring (5 : Fin 6)
      (1 : Fin 3) (2 : Fin 3) (by decide)

private theorem d1A0 : Circuit.PathDelay routedDelay1 (2 : Fin 6) (2 : Fin 6) 1 := by
  simpa [delay1InputWiring, delay1OutputWiring, fin6Perm] using
    routedDelay1_path (2 : Fin 6) (0 : Fin 3) (by decide)

private theorem d1P : Circuit.PathDelay routedDelay1 (4 : Fin 6) (4 : Fin 6) 1 := by
  simpa [delay1InputWiring, delay1OutputWiring, fin6Perm] using
    routedDelay1_path (4 : Fin 6) (1 : Fin 3) (by decide)

private theorem d1Q : Circuit.PathDelay routedDelay1 (5 : Fin 6) (5 : Fin 6) 1 := by
  simpa [delay1InputWiring, delay1OutputWiring, fin6Perm] using
    routedDelay1_path (5 : Fin 6) (2 : Fin 3) (by decide)

private theorem g2A0Control : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (2 : Fin 6) (1 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_gatePath g2InputWiring g2OutputWiring (2 : Fin 6)
      (0 : Fin 3) (0 : Fin 3) (by decide)

private theorem g2A0Y2 : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (2 : Fin 6) (4 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_gatePath g2InputWiring g2OutputWiring (2 : Fin 6)
      (0 : Fin 3) (1 : Fin 3) (by decide)

private theorem g2A0Y3 : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (2 : Fin 6) (5 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_gatePath g2InputWiring g2OutputWiring (2 : Fin 6)
      (0 : Fin 3) (2 : Fin 3) (by decide)

private theorem g2PY2 : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (4 : Fin 6) (4 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_gatePath g2InputWiring g2OutputWiring (4 : Fin 6)
      (2 : Fin 3) (1 : Fin 3) (by decide)

private theorem g2PY3 : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (4 : Fin 6) (5 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_gatePath g2InputWiring g2OutputWiring (4 : Fin 6)
      (2 : Fin 3) (2 : Fin 3) (by decide)

private theorem g2Q : Circuit.PathDelay
    (routedGate g2InputWiring g2OutputWiring) (5 : Fin 6) (3 : Fin 6) 0 := by
  simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
    routedGate_bypassPath g2InputWiring g2OutputWiring (5 : Fin 6) (2 : Fin 3) (by decide)

private theorem d2A0 : Circuit.PathDelay routedDelay2 (1 : Fin 6) (1 : Fin 6) 1 := by
  simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
    routedDelay2_path (1 : Fin 6) (0 : Fin 4) (by decide)

private theorem d2Q : Circuit.PathDelay routedDelay2 (3 : Fin 6) (3 : Fin 6) 1 := by
  simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
    routedDelay2_path (3 : Fin 6) (1 : Fin 4) (by decide)

private theorem d2Y2 : Circuit.PathDelay routedDelay2 (4 : Fin 6) (4 : Fin 6) 1 := by
  simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
    routedDelay2_path (4 : Fin 6) (2 : Fin 4) (by decide)

private theorem d2Y3 : Circuit.PathDelay routedDelay2 (5 : Fin 6) (5 : Fin 6) 1 := by
  simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
    routedDelay2_path (5 : Fin 6) (3 : Fin 4) (by decide)

private theorem g3A0Y0 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (1 : Fin 6) (0 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_gatePath g3InputWiring g3OutputWiring (1 : Fin 6)
      (0 : Fin 3) (1 : Fin 3) (by decide)

private theorem g3A0Y1 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (1 : Fin 6) (1 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_gatePath g3InputWiring g3OutputWiring (1 : Fin 6)
      (0 : Fin 3) (2 : Fin 3) (by decide)

private theorem g3QY0 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (3 : Fin 6) (0 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_gatePath g3InputWiring g3OutputWiring (3 : Fin 6)
      (2 : Fin 3) (1 : Fin 3) (by decide)

private theorem g3QY1 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (3 : Fin 6) (1 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_gatePath g3InputWiring g3OutputWiring (3 : Fin 6)
      (2 : Fin 3) (2 : Fin 3) (by decide)

private theorem g3Y2 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (4 : Fin 6) (2 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_bypassPath g3InputWiring g3OutputWiring (4 : Fin 6) (0 : Fin 3) (by decide)

private theorem g3Y3 : Circuit.PathDelay
    (routedGate g3InputWiring g3OutputWiring) (5 : Fin 6) (3 : Fin 6) 0 := by
  simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
    routedGate_bypassPath g3InputWiring g3OutputWiring (5 : Fin 6) (1 : Fin 3) (by decide)

private theorem a0Y1Path : Circuit.PathDelay demuxCircuit 3 1 2 :=
  assembleDemuxPath g1A0 d1A0 g2A0Control d2A0 g3A0Y1

private theorem a0Y2Path : Circuit.PathDelay demuxCircuit 3 2 2 :=
  assembleDemuxPath g1A0 d1A0 g2A0Y2 d2Y2 g3Y2

private theorem a0Y3Path : Circuit.PathDelay demuxCircuit 3 3 2 :=
  assembleDemuxPath g1A0 d1A0 g2A0Y3 d2Y3 g3Y3

private theorem a1Y0Path : Circuit.PathDelay demuxCircuit 4 0 2 :=
  assembleDemuxPath g1A1Q d1Q g2Q d2Q g3QY0

private theorem a1Y1Path : Circuit.PathDelay demuxCircuit 4 1 2 :=
  assembleDemuxPath g1A1Q d1Q g2Q d2Q g3QY1

private theorem a1Y2Path : Circuit.PathDelay demuxCircuit 4 2 2 :=
  assembleDemuxPath g1A1P d1P g2PY2 d2Y2 g3Y2

private theorem a1Y3Path : Circuit.PathDelay demuxCircuit 4 3 2 :=
  assembleDemuxPath g1A1P d1P g2PY3 d2Y3 g3Y3

private theorem xY0Path : Circuit.PathDelay demuxCircuit 5 0 2 :=
  assembleDemuxPath g1XQ d1Q g2Q d2Q g3QY0

private theorem xY1Path : Circuit.PathDelay demuxCircuit 5 1 2 :=
  assembleDemuxPath g1XQ d1Q g2Q d2Q g3QY1

private theorem xY2Path : Circuit.PathDelay demuxCircuit 5 2 2 :=
  assembleDemuxPath g1XP d1P g2PY2 d2Y2 g3Y2

private theorem xY3Path : Circuit.PathDelay demuxCircuit 5 3 2 :=
  assembleDemuxPath g1XP d1P g2PY3 d2Y3 g3Y3

/-- Embed an argument port `(A₀,A₁,X)` into the canonical six-wire input. -/
def argumentPort (input : Fin 3) : Fin 6 := Fin.natAdd 3 input

/-- Embed a result port `(Y₀,Y₁,Y₂,Y₃)` into the canonical six-wire output. -/
def resultPort (output : Fin 4) : Fin 6 := Fin.castAdd 2 output

/-- Every argument/result port pair has a grammar-induced path of delay exactly two. -/
theorem argument_to_result_path (input : Fin 3) (output : Fin 4) :
    Circuit.PathDelay demuxCircuit (argumentPort input) (resultPort output) 2 := by
  fin_cases input <;> fin_cases output
  · exact a0Y0Path
  · exact a0Y1Path
  · exact a0Y2Path
  · exact a0Y3Path
  · exact a1Y0Path
  · exact a1Y1Path
  · exact a1Y2Path
  · exact a1Y3Path
  · exact xY0Path
  · exact xY1Path
  · exact xY2Path
  · exact xY3Path

/-- Every grammar-induced argument/result path has delay exactly two. -/
theorem argument_to_result_path_delay_two (input : Fin 3) (output : Fin 4)
    {actual : Nat}
    (path : Circuit.PathDelay demuxCircuit
      (argumentPort input) (resultPort output) actual) :
    actual = 2 := by
  have timing := demuxCircuit_respectsPhase path
  fin_cases input <;> fin_cases output <;>
    simpa [argumentPort, resultPort] using timing

/-- The third zero source has a zero-delay grammar path to `Y₀`. -/
theorem zero_source_to_y0_path :
    Circuit.PathDelay demuxCircuit (2 : Fin 6) (0 : Fin 6) 0 := by
  have p1 : Circuit.PathDelay (routedGate g1InputWiring g1OutputWiring)
      (2 : Fin 6) (1 : Fin 6) 0 := by
    simpa [g1InputWiring, g1OutputWiring, fin6Perm] using
      routedGate_bypassPath g1InputWiring g1OutputWiring (2 : Fin 6) (1 : Fin 3) (by decide)
  have p2 : Circuit.PathDelay routedDelay1 (1 : Fin 6) (1 : Fin 6) 0 := by
    simpa [delay1InputWiring, delay1OutputWiring, fin6Perm] using
      routedDelay1_bypassPath (1 : Fin 6) (1 : Fin 3) (by decide)
  have p3 : Circuit.PathDelay (routedGate g2InputWiring g2OutputWiring)
      (1 : Fin 6) (0 : Fin 6) 0 := by
    simpa [g2InputWiring, g2OutputWiring, fin6Perm] using
      routedGate_bypassPath g2InputWiring g2OutputWiring (1 : Fin 6) (0 : Fin 3) (by decide)
  have p4 : Circuit.PathDelay routedDelay2 (0 : Fin 6) (0 : Fin 6) 0 := by
    simpa [delay2InputWiring, delay2OutputWiring, fin6Perm] using
      routedDelay2_bypassPath (0 : Fin 6) (0 : Fin 2) (by decide)
  have p5 : Circuit.PathDelay (routedGate g3InputWiring g3OutputWiring)
      (0 : Fin 6) (0 : Fin 6) 0 := by
    simpa [g3InputWiring, g3OutputWiring, fin6Perm] using
      routedGate_gatePath g3InputWiring g3OutputWiring (0 : Fin 6)
        (1 : Fin 3) (1 : Fin 3) (by decide)
  simpa [demuxCircuit] using Circuit.PathDelay.seq p1
    (Circuit.PathDelay.seq p2
      (Circuit.PathDelay.seq p3 (Circuit.PathDelay.seq p4 p5)))

/-- The complete six-wire term is not globally equal-path-latency. -/
theorem demuxCircuit_not_meetsPaperCombinationalTiming :
    ¬ Circuit.MeetsPaperCombinationalTiming demuxCircuit := by
  rintro ⟨latency, uniform⟩
  have argumentLatency : 2 = latency := uniform a0Y0Path
  have sourceLatency : 0 = latency := uniform zero_source_to_y0_path
  omega

end ConservativeLogic.Simulation.Demultiplexer
