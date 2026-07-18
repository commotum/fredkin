import ConservativeLogic.Reversible.Core

/-!
# The paper's unit wire

The unit wire has two deliberately separate pieces of data here. `value` is
the static identity map on one Boolean wire, while `delay` records the paper's
one-step latency. The latter is metadata only: this module does not yet define
traces, timed composition, a backward-time dynamics, or time-reversal
invariance. In particular, the identity of the carried value must not be read
as a claim that input and output occur at the same time.
-/

namespace ConservativeLogic.UnitWire

/-- Static value semantics of a unit wire: the carried bit is unchanged. -/
def value : Conservative 1 := Conservative.identity 1

/-- The unit wire's latency in the paper's discrete time steps. -/
def delay : Nat := 1

/--
A unit wire carries its input value unchanged. This equality concerns values
only and deliberately contains no assertion about their observation times.
-/
@[simp]
theorem value_apply (input : BitState 1) : value input = input := rfl

/-- The static value map is reversible, independently of its delay metadata. -/
theorem value_isReversible : IsReversible value :=
  Conservative.isReversible value

/-- The static value map preserves Hamming weight. -/
theorem value_weightPreserving : WeightPreserving value :=
  value.weight_preserving

/--
The paper assigns one time step of delay to a unit wire. This fact is metadata,
not a theorem about timed traces or time reversal.
-/
@[simp]
theorem delay_eq_one : delay = 1 := rfl

end ConservativeLogic.UnitWire

