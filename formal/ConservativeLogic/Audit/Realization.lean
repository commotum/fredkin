import ConservativeLogic.API

/-!
# Stage 5 realization audit

This diagnostic module checks exhaustive boundary accounting, fixed sources,
clean scratch restoration, explicit garbage, target-fiber information bounds,
Hamming-weight constraints, exact Figure 4/6 port routing, and constrained
FAN-OUT. It is intentionally not re-exported by the public API.
-/

namespace ConservativeLogic.Audit.Realization

open ConservativeLogic.Realization
open ConservativeLogic.Realization.Primitive

/-! ## Guarded interface failures -/

/- A source-free, garbage-free one-to-two layout cannot balance. -/
#guard_msgs (drop info) in
#check_failure ({
    sourceWidth := 0
    scratchWidth := 0
    argumentWidth := 1
    resultWidth := 2
    garbageWidth := 0
    balanced := rfl
  } : Layout)

private def argumentDependentSource : BitState 2 → BitState 1 :=
  fun argument => oneBit (argument 0)

/- `Realizes` accepts a fixed source state, not an argument-dependent source function. -/
#guard_msgs (drop info) in
#check_failure Realizes andLayout fredkinAndCircuit noBits argumentDependentSource
  andTarget andGarbage

/- A width-one circuit cannot directly return the two-bit FAN-OUT target. -/
#guard_msgs (drop info) in
#check_failure fun (circuit : Circuit 1) (argument : BitState 1) =>
  show BitState 2 from Circuit.eval circuit argument

/- The unequal-width selected target is not an equal-width reversible map. -/
#guard_msgs (drop info) in
#check_failure show Reversible 1 from fanoutTarget

/-! ## Zero widths and arbitrary clean scratch -/

private def emptyTarget (_ : BitState 0) : BitState 0 := noBits

private def emptyGarbage (_ : BitState 0) : BitState 0 := noBits

private def emptyLayout : Layout where
  sourceWidth := 0
  scratchWidth := 0
  argumentWidth := 0
  resultWidth := 0
  garbageWidth := 0
  balanced := rfl

theorem empty_identity_realizes :
    Realizes emptyLayout (Circuit.identity 0) noBits noBits emptyTarget emptyGarbage := by
  intro argument
  funext i
  exact Fin.elim0 i

private def scratchOnlyLayout (width : Nat) : Layout where
  sourceWidth := 0
  scratchWidth := width
  argumentWidth := 0
  resultWidth := 0
  garbageWidth := 0
  balanced := rfl

theorem arbitrary_scratch_identity_realizes {width : Nat} (scratch : BitState width) :
    Realizes (scratchOnlyLayout width) (Circuit.identity width)
      scratch noBits emptyTarget emptyGarbage := by
  intro argument
  change BitState 0 at argument
  have argument_eq : argument = noBits := by
    funext i
    exact Fin.elim0 i
  subst argument
  rfl

/-! ## Exact physical input routing -/

example (a b : Bool) :
    Circuit.eval (Circuit.permute andInputWiring)
        (andLayout.packInput noBits andSource (twoBits a b)) =
      PaperFredkin.state a b false := by
  cases a <;> cases b <;> decide

example (a b : Bool) :
    Circuit.eval (Circuit.permute orInputWiring)
        (orLayout.packInput noBits orSource (twoBits a b)) =
      PaperFredkin.state a true b := by
  cases a <;> cases b <;> decide

example (a : Bool) :
    Circuit.eval (Circuit.permute notFanoutInputWiring)
        (notLayout.packInput noBits notFanoutSource (oneBit a)) =
      PaperFredkin.state a true false := by
  cases a <;> decide

/-! ## Complete primitive regressions -/

example : Circuit.eval fredkinAndCircuit
    (andLayout.packInput noBits andSource (twoBits false false)) =
    andLayout.packOutput noBits (oneBit false) (twoBits false false) := by decide

example : Circuit.eval fredkinAndCircuit
    (andLayout.packInput noBits andSource (twoBits false true)) =
    andLayout.packOutput noBits (oneBit false) (twoBits false true) := by decide

example : Circuit.eval fredkinAndCircuit
    (andLayout.packInput noBits andSource (twoBits true false)) =
    andLayout.packOutput noBits (oneBit false) (twoBits true false) := by decide

example : Circuit.eval fredkinAndCircuit
    (andLayout.packInput noBits andSource (twoBits true true)) =
    andLayout.packOutput noBits (oneBit true) (twoBits true false) := by decide

example : Circuit.eval fredkinOrCircuit
    (orLayout.packInput noBits orSource (twoBits false false)) =
    orLayout.packOutput noBits (oneBit false) (twoBits false true) := by decide

example : Circuit.eval fredkinOrCircuit
    (orLayout.packInput noBits orSource (twoBits false true)) =
    orLayout.packOutput noBits (oneBit true) (twoBits false true) := by decide

example : Circuit.eval fredkinOrCircuit
    (orLayout.packInput noBits orSource (twoBits true false)) =
    orLayout.packOutput noBits (oneBit true) (twoBits true false) := by decide

example : Circuit.eval fredkinOrCircuit
    (orLayout.packInput noBits orSource (twoBits true true)) =
    orLayout.packOutput noBits (oneBit true) (twoBits true true) := by decide

/-- These two rows catch the easy-to-reverse `(1,0)` physical data-port order. -/
example : PaperFredkin.map (PaperFredkin.state false true false) =
    PaperFredkin.state false false true := by decide

example : PaperFredkin.map (PaperFredkin.state true true false) =
    PaperFredkin.state true true false := by decide

example : Circuit.eval fredkinNotCircuit
    (notLayout.packInput noBits notFanoutSource (oneBit false)) =
    notLayout.packOutput noBits (oneBit true) (twoBits false false) := by decide

example : Circuit.eval fredkinNotCircuit
    (notLayout.packInput noBits notFanoutSource (oneBit true)) =
    notLayout.packOutput noBits (oneBit false) (twoBits true true) := by decide

example : Circuit.eval fredkinFanoutCircuit
    (fanoutLayout.packInput noBits notFanoutSource (oneBit false)) =
    fanoutLayout.packOutput noBits (twoBits false false) (oneBit true) := by decide

example : Circuit.eval fredkinFanoutCircuit
    (fanoutLayout.packInput noBits notFanoutSource (oneBit true)) =
    fanoutLayout.packOutput noBits (twoBits true true) (oneBit false) := by decide

/-! ## Garbage dependence and information-capacity obstructions -/

theorem andGarbage_not_argumentIndependent : ¬ ArgumentIndependent andGarbage := by
  intro independent
  have equality := independent (twoBits false false) (twoBits false true)
  have distinct : andGarbage (twoBits false false) ≠
      andGarbage (twoBits false true) := by decide
  exact distinct equality

theorem orGarbage_not_argumentIndependent : ¬ ArgumentIndependent orGarbage := by
  intro independent
  have equality := independent (twoBits false false) (twoBits true false)
  have distinct : orGarbage (twoBits false false) ≠
      orGarbage (twoBits true false) := by decide
  exact distinct equality

theorem notGarbage_not_argumentIndependent : ¬ ArgumentIndependent notGarbage := by
  intro independent
  have equality := independent (oneBit false) (oneBit true)
  have distinct : notGarbage (oneBit false) ≠ notGarbage (oneBit true) := by decide
  exact distinct equality

theorem fanoutGarbage_not_argumentIndependent : ¬ ArgumentIndependent fanoutGarbage := by
  intro independent
  have equality := independent (oneBit false) (oneBit true)
  have distinct : fanoutGarbage (oneBit false) ≠ fanoutGarbage (oneBit true) := by decide
  exact distinct equality

private def andOneGarbageLayout : Layout where
  sourceWidth := 0
  scratchWidth := 0
  argumentWidth := 2
  resultWidth := 1
  garbageWidth := 1
  balanced := rfl

/-- AND's three-element false fiber cannot fit into one garbage bit. -/
theorem and_not_realizable_with_one_garbage
    (circuit : Circuit andOneGarbageLayout.width)
    (garbage : BitState 2 → BitState 1) :
    ¬ Realizes andOneGarbageLayout circuit noBits noBits andTarget garbage := by
  intro realizes
  have bound := realizes.fiber_card_le (oneBit false)
  have fiberCard : Fintype.card (Fiber andTarget (oneBit false)) = 3 := by decide
  have garbageCapacity : 2 ^ andOneGarbageLayout.garbageWidth = 2 := by decide
  have normalized : 3 ≤ 2 := calc
    3 = Fintype.card (Fiber andTarget (oneBit false)) := fiberCard.symm
    _ ≤ 2 ^ andOneGarbageLayout.garbageWidth := bound
    _ = 2 := garbageCapacity
  exact (by decide : ¬ 3 ≤ 2) normalized

/-- An argument-independent garbage bit cannot conceal AND's collisions. -/
theorem and_not_realizable_with_argumentIndependent_garbage
    (circuit : Circuit andOneGarbageLayout.width)
    (garbage : BitState 2 → BitState 1) (independent : ArgumentIndependent garbage) :
    ¬ Realizes andOneGarbageLayout circuit noBits noBits andTarget garbage := by
  intro realizes
  have injective := realizes.target_injective_of_argumentIndependentGarbage independent
  have sameTarget : andTarget (twoBits false false) = andTarget (twoBits false true) := by
    decide
  have distinct : twoBits false false ≠ twoBits false true := by decide
  exact distinct (injective sameTarget)

private def allZeroFanoutSource : BitState 2 := twoBits false false

/-- Two all-zero sources cannot supply the conserved token needed for FAN-OUT. -/
theorem fanout_not_realizable_from_allZeroSource
    (circuit : Circuit fanoutLayout.width)
    (garbage : BitState 1 → BitState 1) :
    ¬ Realizes fanoutLayout circuit noBits allZeroFanoutSource fanoutTarget garbage := by
  intro realizes
  have balance := realizes.weight_balance (oneBit true)
  have resultWeight : hammingWeight (fanoutTarget (oneBit true)) = 2 := by decide
  have impossible : 2 ≤ 1 := calc
    2 ≤ hammingWeight (fanoutTarget (oneBit true)) +
        hammingWeight (garbage (oneBit true)) := by
      rw [resultWeight]
      exact Nat.le_add_right 2 _
    _ = hammingWeight allZeroFanoutSource + hammingWeight (oneBit true) :=
      balance.symm
    _ = 1 := by decide
  exact (by decide : ¬ 2 ≤ 1) impossible

/-! ## Public surfaces and axiom footprints -/

#check Layout
#check Layout.width
#check Layout.packInput
#check Layout.packOutput
#check ArgumentIndependent
#check Fiber
#check Realizes
#check Realizes.targetGarbage_injective
#check Realizes.garbage_separates_collisions
#check Realizes.garbage_injectiveOn_fiber
#check Realizes.fiber_card_le
#check Realizes.card_argument_le_resultGarbage
#check Realizes.target_injective_of_resultDeterminesGarbage
#check Realizes.target_injective_of_argumentIndependentGarbage
#check Realizes.target_injective_of_noGarbage
#check Realizes.weight_balance
#check fredkinAndCircuit
#check fredkinOrCircuit
#check fredkinNotCircuit
#check fredkinFanoutCircuit
#check fredkin_realizes_and
#check fredkin_realizes_or
#check fredkin_realizes_not
#check fredkin_realizes_fanout

#print Layout
#print Realizes
#print Circuit

#print axioms hammingWeight_castState
#print axioms castState_injective
#print axioms card_bitState
#print axioms Layout.packInput_argument_injective
#print axioms Layout.packOutput_resultGarbage_injective
#print axioms Layout.hammingWeight_packInput
#print axioms Layout.hammingWeight_packOutput
#print axioms Realizes.targetGarbage_injective
#print axioms Realizes.garbage_separates_collisions
#print axioms Realizes.garbage_injectiveOn_fiber
#print axioms Realizes.fiber_card_le
#print axioms Realizes.card_argument_le_resultGarbage
#print axioms Realizes.target_injective_of_resultDeterminesGarbage
#print axioms Realizes.target_injective_of_argumentIndependentGarbage
#print axioms Realizes.target_injective_of_noGarbage
#print axioms Realizes.weight_balance
#print axioms fredkin_and_complete
#print axioms fredkin_or_complete
#print axioms fredkin_not_complete
#print axioms fredkin_fanout_complete
#print axioms fredkin_realizes_and
#print axioms fredkin_realizes_or
#print axioms fredkin_realizes_not
#print axioms fredkin_realizes_fanout
#print axioms fredkinFanoutCircuit_isReversible
#print axioms fredkinFanoutCircuit_weightPreserving
#print axioms empty_identity_realizes
#print axioms arbitrary_scratch_identity_realizes
#print axioms and_not_realizable_with_one_garbage
#print axioms and_not_realizable_with_argumentIndependent_garbage
#print axioms fanout_not_realizable_from_allZeroSource

end ConservativeLogic.Audit.Realization
