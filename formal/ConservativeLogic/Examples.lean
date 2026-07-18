import ConservativeLogic

/-!
# Finite public-API examples

This leaf consumes only the stable finite root `ConservativeLogic`.  It shows
how the public source compiler, explicit compute-copy-uncompute construction,
and clean Fredkin completeness theorem are used without importing diagnostic,
sequential, or billiard modules.

Every example retains the library's complete resource boundary: fixed source,
returned scratch, original argument, selected result, explicit garbage, and
the exact ancillary initialization recorded by a clean realization are never
erased behind a result-only equation.
-/

namespace ConservativeLogic.Examples

/--
The conventional AND source node compiles to a balanced Fredkin circuit with
the compiler's exact zero-scratch layout, fixed source, result function, and
argument-dependent garbage function.
-/
theorem and_compile_realizes :
    Realization.Realizes
      (Simulation.SourceCircuit.simulationLayout Simulation.SourceCircuit.andGate)
      (Simulation.SourceCircuit.compile Simulation.SourceCircuit.andGate)
      Realization.Primitive.noBits
      (Simulation.SourceCircuit.sourceState Simulation.SourceCircuit.andGate)
      (Simulation.SourceCircuit.eval Simulation.SourceCircuit.andGate)
      (Simulation.SourceCircuit.garbage Simulation.SourceCircuit.andGate) :=
  Simulation.SourceCircuit.compile_realizes Simulation.SourceCircuit.andGate

/--
Run the routed one-Fredkin AND realization, copy its selected result into the
explicit `(0,1)` result register, and run the complete computation backward.
-/
def andUncompute :
    Circuit
      (Ancilla.computeCopyUncomputeWidth Realization.Primitive.andLayout) :=
  Ancilla.computeCopyUncompute Realization.Primitive.andLayout
    Realization.Primitive.fredkinAndCircuit

/--
The complete AND compute-copy-uncompute boundary restores the exact empty
scratch block, fixed zero source, and original two-bit argument.  The transient
AND garbage is absent from the final boundary, while the separate result
register contains the AND value together with its Boolean complement.
-/
theorem and_uncompute_spec (argument : BitState 2) :
    Circuit.eval andUncompute
        (BitState.append
          (Realization.Primitive.andLayout.packInput
            Realization.Primitive.noBits Realization.Primitive.andSource argument)
          (Ancilla.resultRegisterInput
            Realization.Primitive.andLayout.resultWidth)) =
      BitState.append
        (Realization.Primitive.andLayout.packInput
          Realization.Primitive.noBits Realization.Primitive.andSource argument)
        (Ancilla.resultRegisterOutput
          (Realization.Primitive.andTarget argument)) := by
  exact Ancilla.compute_copy_uncompute_spec
    Realization.Primitive.fredkin_realizes_and argument

/--
The paper-convention Fredkin permutation has a finite clean realization.  The
witness type exposes its selected ancillary width and exact, possibly mixed
initialization, the complete fixed-basis circuit, exact restoration equation,
structural-basis certificate, and zero-latency certificate.
-/
theorem paperFredkin_clean_realizable :
    Nonempty (CleanFredkinRealization PaperFredkin.conservative.toEquiv) :=
  fredkin_complete_conservative PaperFredkin.conservative

end ConservativeLogic.Examples
