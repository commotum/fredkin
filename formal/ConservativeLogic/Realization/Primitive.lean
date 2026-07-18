import ConservativeLogic.Realization.Core

/-!
# Exact one-Fredkin realizations from Section 3

This module reconstructs Figures 4 and 6 using the paper's ordered,
zero-controlled Fredkin gate. Each theorem states the fixed source, selected
result, and every garbage output. Named active structural permutations convert
the canonical realization boundary order to physical Fredkin ports
`(u,x₁,x₂)` and return selected results first; they are not synthesized or
physical routing theorems.

NOT and FAN-OUT share the initialized physical slice
`(a,1,0) ↦ (a,a,¬a)`. NOT selects `y₂`; FAN-OUT selects `(v,y₁)`. Thus FAN-OUT
is a restricted width-three realization consuming source `(0,1)` in canonical
order, not an unrestricted copying circuit or reversible map `a ↦ (a,a)`.
-/

namespace ConservativeLogic.Realization.Primitive

/-- The unique width-zero state, used for the absent scratch block. -/
def noBits : BitState 0 := fun i => Fin.elim0 i

/-- A canonical one-bit state. -/
def oneBit (value : Bool) : BitState 1 := fun _ => value

/-- A canonical ordered two-bit state. -/
def twoBits (first second : Bool) : BitState 2 :=
  BitState.append (oneBit first) (oneBit second)

private theorem oneBit_eta (input : BitState 1) : oneBit (input 0) = input := by
  funext i
  refine Fin.cases rfl ?_ i
  intro impossible
  exact Fin.elim0 impossible

private theorem twoBits_eta (input : BitState 2) : twoBits (input 0) (input 1) = input := by
  funext i
  refine Fin.cases rfl ?_ i
  intro j
  refine Fin.cases rfl ?_ j
  intro impossible
  exact Fin.elim0 impossible

/-! ## Ordinary target functions and complete garbage functions -/

/-- Ordinary two-input AND as a one-bit result. -/
def andTarget (argument : BitState 2) : BitState 1 :=
  oneBit (argument 0 && argument 1)

/-- Ordinary two-input OR as a one-bit result. -/
def orTarget (argument : BitState 2) : BitState 1 :=
  oneBit (argument 0 || argument 1)

/-- Ordinary one-input NOT as a one-bit result. -/
def notTarget (argument : BitState 1) : BitState 1 :=
  oneBit (!argument 0)

/-- The selected two-wire FAN-OUT result; this function is not itself a circuit. -/
def fanoutTarget (argument : BitState 1) : BitState 2 :=
  twoBits (argument 0) (argument 0)

/-- AND sink order `(v,y₂) = (a,¬a∧b)`. -/
def andGarbage (argument : BitState 2) : BitState 2 :=
  twoBits (argument 0) (!argument 0 && argument 1)

/-- OR sink order `(v,y₂) = (a,¬a∨b)`. -/
def orGarbage (argument : BitState 2) : BitState 2 :=
  twoBits (argument 0) (!argument 0 || argument 1)

/-- NOT sink order `(v,y₁) = (a,a)`. -/
def notGarbage (argument : BitState 1) : BitState 2 :=
  twoBits (argument 0) (argument 0)

/-- FAN-OUT's required sink `y₂ = ¬a`. -/
def fanoutGarbage (argument : BitState 1) : BitState 1 :=
  oneBit (!argument 0)

/-! ## Exhaustive layouts and fixed sources -/

/-- AND uses one source, two arguments, one result, and two garbage wires. -/
def andLayout : Layout where
  sourceWidth := 1
  scratchWidth := 0
  argumentWidth := 2
  resultWidth := 1
  garbageWidth := 2
  balanced := rfl

/-- OR has the same block widths as AND. -/
def orLayout : Layout := andLayout

/-- NOT uses two source wires, one argument, one result, and two garbage wires. -/
def notLayout : Layout where
  sourceWidth := 2
  scratchWidth := 0
  argumentWidth := 1
  resultWidth := 1
  garbageWidth := 2
  balanced := rfl

/-- FAN-OUT uses two source wires, one argument, two results, and one garbage wire. -/
def fanoutLayout : Layout where
  sourceWidth := 2
  scratchWidth := 0
  argumentWidth := 1
  resultWidth := 2
  garbageWidth := 1
  balanced := rfl

/-- Figure 4's fixed `0` source for AND. -/
def andSource : BitState 1 := oneBit false

/-- Figure 6(a)'s fixed `1` source for OR. -/
def orSource : BitState 1 := oneBit true

/-- Canonical visual source order `(0,1)` for NOT and FAN-OUT. -/
def notFanoutSource : BitState 2 := twoBits false true

/-! ## Explicit active port routing -/

/-- Move canonical `(0,a,b)` to physical AND input `(a,b,0)`. -/
def andInputWiring : WirePerm 3 :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2)

/-- Move canonical `(1,a,b)` to physical OR input `(a,1,b)`. -/
def orInputWiring : WirePerm 3 := Equiv.swap 0 1

/-- Move canonical `(0,1,a)` to physical NOT/FAN-OUT input `(a,1,0)`. -/
def notFanoutInputWiring : WirePerm 3 := Equiv.swap 0 2

/-- Move physical `(v,y₁,y₂)` to canonical `(y₁,v,y₂)`. -/
def resultFromDataOneWiring : WirePerm 3 := Equiv.swap 0 1

/-- Move physical `(v,y₁,y₂)` to canonical `(y₂,v,y₁)`. -/
def resultFromDataTwoWiring : WirePerm 3 :=
  (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1)

/-- One Fredkin with explicit structural input and output port reindexing. -/
def routedFredkin (inputWiring outputWiring : WirePerm 3) : Circuit 3 :=
  Circuit.seq (Circuit.permute inputWiring)
    (Circuit.seq Circuit.fredkin (Circuit.permute outputWiring))

/-- Figure 4(b)'s routed one-Fredkin AND realization. -/
def fredkinAndCircuit : Circuit 3 :=
  routedFredkin andInputWiring resultFromDataOneWiring

/-- Figure 6(a)'s routed one-Fredkin OR realization. -/
def fredkinOrCircuit : Circuit 3 :=
  routedFredkin orInputWiring resultFromDataOneWiring

/-- Figure 6(b)'s routed one-Fredkin NOT realization. -/
def fredkinNotCircuit : Circuit 3 :=
  routedFredkin notFanoutInputWiring resultFromDataTwoWiring

/-- Figure 6(c)'s one-Fredkin FAN-OUT realization; raw output is already result-first. -/
def fredkinFanoutCircuit : Circuit 3 :=
  routedFredkin notFanoutInputWiring (Equiv.refl _)

/-! ## Complete initialized-slice equations -/

/-- Complete canonical AND equation, including both sink outputs. -/
theorem fredkin_and_complete (a b : Bool) :
    Circuit.eval fredkinAndCircuit
        (andLayout.packInput noBits andSource (twoBits a b)) =
      andLayout.packOutput noBits (oneBit (a && b))
        (twoBits a (!a && b)) := by
  cases a <;> cases b <;> decide

/-- Complete canonical OR equation, including both sink outputs. -/
theorem fredkin_or_complete (a b : Bool) :
    Circuit.eval fredkinOrCircuit
        (orLayout.packInput noBits orSource (twoBits a b)) =
      orLayout.packOutput noBits (oneBit (a || b))
        (twoBits a (!a || b)) := by
  cases a <;> cases b <;> decide

/-- Complete canonical NOT equation: physical `y₂` is first and `(v,y₁)` is garbage. -/
theorem fredkin_not_complete (a : Bool) :
    Circuit.eval fredkinNotCircuit
        (notLayout.packInput noBits notFanoutSource (oneBit a)) =
      notLayout.packOutput noBits (oneBit (!a)) (twoBits a a) := by
  cases a <;> decide

/-- Complete constrained FAN-OUT equation, including complement garbage. -/
theorem fredkin_fanout_complete (a : Bool) :
    Circuit.eval fredkinFanoutCircuit
        (fanoutLayout.packInput noBits notFanoutSource (oneBit a)) =
      fanoutLayout.packOutput noBits (twoBits a a) (oneBit (!a)) := by
  cases a <;> decide

/-! ## Reusable realization theorems -/

/-- The routed paper Fredkin realizes ordinary AND with source `0`. -/
theorem fredkin_realizes_and :
    Realizes andLayout fredkinAndCircuit noBits andSource andTarget andGarbage := by
  intro argument
  change BitState 2 at argument
  rw [← twoBits_eta argument]
  exact fredkin_and_complete (argument 0) (argument 1)

/-- The routed paper Fredkin realizes ordinary OR with source `1`. -/
theorem fredkin_realizes_or :
    Realizes orLayout fredkinOrCircuit noBits orSource orTarget orGarbage := by
  intro argument
  change BitState 2 at argument
  rw [← twoBits_eta argument]
  exact fredkin_or_complete (argument 0) (argument 1)

/-- The routed paper Fredkin realizes NOT from canonical source `(0,1)`. -/
theorem fredkin_realizes_not :
    Realizes notLayout fredkinNotCircuit noBits notFanoutSource notTarget notGarbage := by
  intro argument
  change BitState 1 at argument
  rw [← oneBit_eta argument]
  exact fredkin_not_complete (argument 0)

/--
The routed paper Fredkin realizes constrained FAN-OUT from canonical source
`(0,1)`, with the complement retained as explicit garbage.
-/
theorem fredkin_realizes_fanout :
    Realizes fanoutLayout fredkinFanoutCircuit noBits notFanoutSource
      fanoutTarget fanoutGarbage := by
  intro argument
  change BitState 1 at argument
  rw [← oneBit_eta argument]
  exact fredkin_fanout_complete (argument 0)

/-- The complete width-three FAN-OUT witness remains globally bijective. -/
theorem fredkinFanoutCircuit_isReversible :
    IsReversible (Circuit.eval fredkinFanoutCircuit) :=
  Circuit.eval_isReversible fredkinFanoutCircuit

/-- The complete width-three FAN-OUT witness preserves total Hamming weight. -/
theorem fredkinFanoutCircuit_weightPreserving :
    WeightPreserving (Circuit.eval fredkinFanoutCircuit) :=
  Circuit.eval_weightPreserving fredkinFanoutCircuit

end ConservativeLogic.Realization.Primitive
