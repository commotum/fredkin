import ConservativeLogic.Reversible.Core

/-!
# Explicit finite feed-forward source circuits

This module defines the conventional, generally irreversible source language
used by the finite Stage 6 replacement theorem.  Constants, discard, and
FAN-OUT are syntax: they cannot be introduced implicitly by the structural
rules.  Serial composition has matching intermediate widths and tensor gives
its two branches disjoint input blocks.

There is deliberately no constructor for an arbitrary semantic function,
delay, state, feedback, trace, or recursive wire.  Thus this syntax describes
only finite acyclic value computations; the paper's sequential simulation
claim requires a later transition-system semantics.
-/

namespace ConservativeLogic.Simulation

/--
An explicitly generated conventional feed-forward Boolean circuit language.

The width-indexed constant and discard nodes are convenient finite block
versions of repeated one-wire constants and discards.  A constant contains
only a fixed state, never a function of the circuit argument.
-/
inductive SourceCircuit : Nat → Nat → Type where
  | identity (width : Nat) : SourceCircuit width width
  | permute {width : Nat} (wiring : WirePerm width) : SourceCircuit width width
  | constant {width : Nat} (value : BitState width) : SourceCircuit 0 width
  | discard (width : Nat) : SourceCircuit width 0
  | andGate : SourceCircuit 2 1
  | orGate : SourceCircuit 2 1
  | notGate : SourceCircuit 1 1
  | fanout : SourceCircuit 1 2
  | seq {inputWidth middleWidth outputWidth : Nat}
      (first : SourceCircuit inputWidth middleWidth)
      (second : SourceCircuit middleWidth outputWidth) :
      SourceCircuit inputWidth outputWidth
  | tensor {leftInput leftOutput rightInput rightOutput : Nat}
      (left : SourceCircuit leftInput leftOutput)
      (right : SourceCircuit rightInput rightOutput) :
      SourceCircuit (leftInput + rightInput) (leftOutput + rightOutput)

namespace SourceCircuit

/-- Static value semantics of an explicitly generated source circuit. -/
def eval : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → BitState inputWidth → BitState outputWidth
  | _, _, .identity _, input => input
  | _, _, .permute wiring, input => WirePerm.onState wiring input
  | _, _, .constant value, _ => value
  | _, _, .discard _, _ => fun index => Fin.elim0 index
  | _, _, .andGate, input => fun _ => input 0 && input 1
  | _, _, .orGate, input => fun _ => input 0 || input 1
  | _, _, .notGate, input => fun _ => !input 0
  | _, _, .fanout, input => fun _ => input 0
  | _, _, .seq first second, input => eval second (eval first input)
  | _, _, .tensor left right, input =>
      BitState.append
        (eval left (BitState.split _ _ input).1)
        (eval right (BitState.split _ _ input).2)

/-- Number of conventional AND, OR, NOT, and explicit FAN-OUT nodes. -/
def logicGateCount : {inputWidth outputWidth : Nat} →
    SourceCircuit inputWidth outputWidth → Nat
  | _, _, .identity _ => 0
  | _, _, .permute _ => 0
  | _, _, .constant _ => 0
  | _, _, .discard _ => 0
  | _, _, .andGate => 1
  | _, _, .orGate => 1
  | _, _, .notGate => 1
  | _, _, .fanout => 1
  | _, _, .seq first second => logicGateCount first + logicGateCount second
  | _, _, .tensor left right => logicGateCount left + logicGateCount right

end SourceCircuit

end ConservativeLogic.Simulation
