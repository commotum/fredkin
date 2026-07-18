import ConservativeLogic.API

/-!
# Stage 4 balanced-circuit audit

This diagnostic module checks arity rejection, fixed-basis primitive agreement,
ordered tensor and serial semantics, active structural permutation direction,
the absence of implicit same-width copying, and the distinction between
feed-forward syntax and the paper's global equal-unit-wire-path condition. It
is intentionally not re-exported by the public API.
-/

namespace ConservativeLogic.Audit.Circuits

private def emptyState : BitState 0 := fun i => Fin.elim0 i

private def singleton (value : Bool) : BitState 1 := fun _ => value

private def pair (left right : Bool) : BitState 2 :=
  BitState.append (singleton left) (singleton right)

private def triple (control data₁ data₂ : Bool) : BitState 3 :=
  PaperFredkin.state control data₁ data₂

/-! ## Guarded arity and reindexing failures -/

#guard_msgs (drop info) in
#check_failure Circuit.seq Circuit.unitWire Circuit.fredkin

private def nonBijectiveReindex : Fin 2 → Fin 2 := fun _ => 0

#guard_msgs (drop info) in
#check_failure Circuit.permute nonBijectiveReindex

/-! ## Zero width and primitive agreement -/

example : Circuit.eval (Circuit.identity 0) emptyState = emptyState := by
  rfl

example : Circuit.PaperCombinational (Circuit.identity 0) :=
  ⟨0, Circuit.hasLatency_identity 0⟩

private def emptyWiring : WirePerm 0 := Equiv.refl _

example : Circuit.eval (Circuit.permute emptyWiring) emptyState = emptyState := by
  funext i
  exact Fin.elim0 i

example : Circuit.eval (Circuit.tensor (Circuit.identity 0) Circuit.unitWire)
    (BitState.append emptyState (singleton true)) = singleton true := by
  decide

example (input : BitState 1) :
    Circuit.eval Circuit.unitWire input = UnitWire.value input := by
  simp

example : Circuit.eval Circuit.fredkin (triple false false true) =
    triple false true false := by
  decide

/-! ## Ordered tensor, active permutation, and serial direction -/

example :
    Circuit.eval (Circuit.tensor Circuit.fredkin Circuit.unitWire)
        (BitState.append (triple false false true) (singleton true)) =
      BitState.append (triple false true false) (singleton true) := by
  decide

private def cycleThree : WirePerm 3 :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

example : Circuit.eval (Circuit.permute cycleThree) (triple true false false) =
    triple false false true := by
  decide

private def swapControlData₁ : WirePerm 3 := Equiv.swap 0 1

example :
    Circuit.eval (Circuit.seq Circuit.fredkin (Circuit.permute swapControlData₁))
        (triple false false true) = triple true false false := by
  decide

example :
    Circuit.eval (Circuit.seq (Circuit.permute swapControlData₁) Circuit.fredkin)
        (triple false false true) = triple false true false := by
  decide

/-! ## No implicit same-width copy overwrite -/

private def copyFirst (input : BitState 2) : BitState 2 :=
  fun _ => input 0

private theorem copyFirst_not_injective : ¬ Function.Injective copyFirst := by
  intro injective
  have sameOutput : copyFirst (pair false false) = copyFirst (pair false true) := by
    decide
  have distinctInputs : pair false false ≠ pair false true := by
    decide
  exact distinctInputs (injective sameOutput)

theorem eval_ne_copyFirst (circuit : Circuit 2) :
    (fun input => Circuit.eval circuit input) ≠ copyFirst := by
  intro equality
  apply copyFirst_not_injective
  intro left right sameOutput
  apply (Circuit.eval_isReversible circuit).1
  change (fun input => Circuit.eval circuit input) left =
    (fun input => Circuit.eval circuit input) right
  rw [equality]
  exact sameOutput

/-! ## Static path timing regressions -/

/-- Structural identity and unit wire agree on values but not latency. -/
example (input : BitState 1) :
    Circuit.eval (Circuit.identity 1) input = Circuit.eval Circuit.unitWire input := by
  rfl

example : Circuit.HasLatency (Circuit.identity 1) 0 :=
  Circuit.hasLatency_identity 1

example : Circuit.HasLatency Circuit.unitWire 1 :=
  Circuit.hasLatency_unitWire_one

/-- A one-wire delay beside an instantaneous identity is feed-forward but nonuniform. -/
def unequalParallel : Circuit 2 :=
  Circuit.tensor Circuit.unitWire (Circuit.identity 1)

/-- Static value semantics cannot detect `unequalParallel`'s unequal path delays. -/
theorem unequalParallel_eval_identity (input : BitState 2) :
    Circuit.eval unequalParallel input = input := by
  change BitState.append (BitState.split 1 1 input).1
      (BitState.split 1 1 input).2 = input
  exact BitState.append_split (m := 1) (n := 1) input

theorem unequalParallel_not_paperCombinational :
    ¬ Circuit.PaperCombinational unequalParallel := by
  rintro ⟨latency, uniform⟩
  have leftPath : Circuit.PathDelay unequalParallel
      (Fin.castAdd 1 (0 : Fin 1)) (Fin.castAdd 1 (0 : Fin 1)) 1 :=
    Circuit.PathDelay.tensorLeft Circuit.PathDelay.unitWire_one
  have rightPath : Circuit.PathDelay unequalParallel
      (Fin.natAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1)) 0 :=
    Circuit.PathDelay.tensorRight (Circuit.PathDelay.identity (0 : Fin 1))
  have leftLatency : 1 = latency := uniform leftPath
  have rightLatency : 0 = latency := uniform rightPath
  exact Nat.zero_ne_one (rightLatency.trans leftLatency.symm)

/-- Parallel unit wires have one globally uniform delay step. -/
def parallelUnitWires : Circuit 2 :=
  Circuit.tensor Circuit.unitWire Circuit.unitWire

theorem parallelUnitWires_hasLatency : Circuit.HasLatency parallelUnitWires 1 :=
  Circuit.HasLatency.tensor Circuit.hasLatency_unitWire_one
    Circuit.hasLatency_unitWire_one

theorem parallelUnitWires_paperCombinational :
    Circuit.PaperCombinational parallelUnitWires :=
  parallelUnitWires_hasLatency.paperCombinational

/-- Complementary branch delays compensate to one uniform total step. -/
def compensatedParallel : Circuit 2 :=
  Circuit.seq
    (Circuit.tensor Circuit.unitWire (Circuit.identity 1))
    (Circuit.tensor (Circuit.identity 1) Circuit.unitWire)

theorem compensatedParallel_hasLatency :
    Circuit.HasLatency compensatedParallel 1 := by
  exact Circuit.HasLatency.compensatedTensorSeq
    Circuit.hasLatency_unitWire_one (Circuit.hasLatency_identity 1)
    (Circuit.hasLatency_identity 1) Circuit.hasLatency_unitWire_one rfl rfl

theorem compensatedParallel_paperCombinational :
    Circuit.PaperCombinational compensatedParallel :=
  compensatedParallel_hasLatency.paperCombinational

/-- Unequal arrivals remain unequal through the instantaneous Fredkin gate. -/
def unequalIntoFredkin : Circuit 3 :=
  Circuit.seq (Circuit.tensor Circuit.unitWire (Circuit.identity 2)) Circuit.fredkin

theorem unequalIntoFredkin_not_paperCombinational :
    ¬ Circuit.PaperCombinational unequalIntoFredkin := by
  rintro ⟨latency, uniform⟩
  have delayedPath : Circuit.PathDelay unequalIntoFredkin
      (Fin.castAdd 2 (0 : Fin 1)) (0 : Fin 3) 1 :=
    Circuit.PathDelay.seq
      (first := Circuit.tensor Circuit.unitWire (Circuit.identity 2))
      (second := Circuit.fredkin)
      (Circuit.PathDelay.tensorLeft (right := Circuit.identity 2)
        Circuit.PathDelay.unitWire_one)
      (Circuit.PathDelay.fredkin (Fin.castAdd 2 (0 : Fin 1)) 0)
  have immediatePath : Circuit.PathDelay unequalIntoFredkin
      (Fin.natAdd 1 (0 : Fin 2)) (0 : Fin 3) 0 :=
    Circuit.PathDelay.seq
      (first := Circuit.tensor Circuit.unitWire (Circuit.identity 2))
      (second := Circuit.fredkin)
      (Circuit.PathDelay.tensorRight (left := Circuit.unitWire)
        (Circuit.PathDelay.identity (0 : Fin 2)))
      (Circuit.PathDelay.fredkin (Fin.natAdd 1 (0 : Fin 2)) 0)
  have delayedLatency : 1 = latency := uniform delayedPath
  have immediateLatency : 0 = latency := uniform immediatePath
  exact Nat.zero_ne_one (immediateLatency.trans delayedLatency.symm)

/-! ## Public surface and axiom footprints -/

#check Circuit
#check Circuit.identity
#check Circuit.unitWire
#check Circuit.fredkin
#check Circuit.permute
#check Circuit.seq
#check Circuit.tensor
#check Circuit.eval
#check Circuit.PathDelay
#check Circuit.HasLatency
#check Circuit.PaperCombinational
#check Circuit.TimedCircuit

#print Circuit

#print axioms Reversible.tensor_apply_append
#print axioms Conservative.tensor
#print axioms Conservative.tensor_apply_append
#print axioms Circuit.eval_identity
#print axioms Circuit.eval_unitWire
#print axioms Circuit.eval_fredkin
#print axioms Circuit.eval_permute
#print axioms Circuit.eval_seq
#print axioms Circuit.eval_tensor
#print axioms Circuit.eval_tensor_append
#print axioms Circuit.eval_isReversible
#print axioms Circuit.eval_weightPreserving
#print axioms Circuit.PathDelay.seq
#print axioms Circuit.PathDelay.tensorLeft
#print axioms Circuit.PathDelay.tensorRight
#print axioms Circuit.hasLatency_identity
#print axioms Circuit.hasLatency_unitWire_one
#print axioms Circuit.hasLatency_fredkin
#print axioms Circuit.hasLatency_permute
#print axioms Circuit.HasLatency.paperCombinational
#print axioms Circuit.HasLatency.seq
#print axioms Circuit.HasLatency.tensor
#print axioms Circuit.HasLatency.compensatedTensorSeq
#print axioms unequalParallel_not_paperCombinational
#print axioms parallelUnitWires_hasLatency
#print axioms compensatedParallel_hasLatency
#print axioms unequalIntoFredkin_not_paperCombinational
#print axioms eval_ne_copyFirst

end ConservativeLogic.Audit.Circuits
