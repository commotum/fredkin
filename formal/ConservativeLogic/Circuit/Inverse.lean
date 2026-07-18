import ConservativeLogic.Circuit.Semantics
import ConservativeLogic.Circuit.Timed

/-!
# Structural inverse of balanced feed-forward circuits

Every `Circuit n` is already a balanced feed-forward expression assembled from
bijective primitives and bijective structural reindexings.  Its syntactic
inverse therefore has the same width: reverse serial order, invert active wire
permutations, and retain the declared left-to-right order of disjoint tensor
blocks.  Identity, the unit wire's static value map, and the paper-convention
Fredkin gate are self-inverse.

The semantic result is equality with the inverse complete conservative
equivalence.  Separately, grammar-induced paths reverse their endpoints while
retaining their nonnegative unit-wire count.  These are static boundary-value
and path-counting theorems for the existing feed-forward grammar.  They do not
define feedback reversal, an oriented execution semantics, negative delay,
`t ↦ -t`, or physical time-reversal invariance.
-/

namespace ConservativeLogic.Circuit

/-! ## Structural inversion -/

/--
The width-preserving structural inverse of a balanced feed-forward circuit.

Serial order reverses because static function-composition order reverses.
Tensor block order is retained: mirroring exchanges each block's endpoints but
does not exchange the declared adjacent left and right interfaces.
-/
def inverse : {n : Nat} → Circuit n → Circuit n
  | _, .identity n => .identity n
  | _, .unitWire => .unitWire
  | _, .fredkin => .fredkin
  | _, .permute wiring => .permute wiring.symm
  | _, .seq first second => .seq (inverse second) (inverse first)
  | _, .tensor left right => .tensor (inverse left) (inverse right)

/-- Structural identity is its own circuit inverse. -/
@[simp]
theorem inverse_identity (n : Nat) : inverse (.identity n) = .identity n :=
  rfl

/-- The static unit-wire syntax is reused with its one-step path metadata. -/
@[simp]
theorem inverse_unitWire : inverse .unitWire = .unitWire :=
  rfl

/-- The paper-convention Fredkin primitive is self-inverse. -/
@[simp]
theorem inverse_fredkin : inverse .fredkin = .fredkin :=
  rfl

/-- Inverting active structural reindexing uses the inverse wire permutation. -/
@[simp]
theorem inverse_permute {n : Nat} (wiring : WirePerm n) :
    inverse (.permute wiring) = .permute wiring.symm :=
  rfl

/-- Syntactic inversion reverses serial order. -/
@[simp]
theorem inverse_seq {n : Nat} (first second : Circuit n) :
    inverse (.seq first second) = .seq (inverse second) (inverse first) :=
  rfl

/-- Syntactic inversion acts componentwise without exchanging tensor blocks. -/
@[simp]
theorem inverse_tensor {m n : Nat} (left : Circuit m) (right : Circuit n) :
    inverse (.tensor left right) = .tensor (inverse left) (inverse right) :=
  rfl

/-- Applying the structural inverse operation twice recovers the exact syntax. -/
@[simp]
theorem inverse_inverse {n : Nat} (circuit : Circuit n) :
    inverse (inverse circuit) = circuit := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => rfl
  | permute wiring => simp
  | seq first second firstIH secondIH => simp [firstIH, secondIH]
  | tensor left right leftIH rightIH => simp [leftIH, rightIH]

/-- Structural circuit inversion is an involution at every fixed width. -/
theorem inverse_involutive {n : Nat} :
    Function.Involutive (inverse : Circuit n → Circuit n) :=
  fun circuit => inverse_inverse circuit

/-! ## Complete static semantic inverse -/

/--
Internal structural cancellation proof used to identify the selected inverse
equivalence without relying on proof-field definitional equality.
-/
private theorem eval_inverse_eval_structural {n : Nat} (circuit : Circuit n)
    (input : BitState n) :
    eval (inverse circuit) (eval circuit input) = input := by
  induction circuit with
  | identity width => rfl
  | unitWire => rfl
  | fredkin => exact PaperFredkin.map_involutive input
  | permute wiring =>
      change WirePerm.onState wiring.symm (WirePerm.onState wiring input) = input
      exact (WirePerm.onState wiring).symm_apply_apply input
  | seq first second firstIH secondIH =>
      simp only [inverse_seq, eval_seq]
      rw [secondIH, firstIH]
  | tensor left right leftIH rightIH =>
      simp only [inverse_tensor, eval_tensor]
      rw [BitState.split_append, leftIH, rightIH]
      exact BitState.append_split input

/--
Evaluation of the syntactic inverse is the inverse complete conservative
equivalence, with no timing hypothesis required.
-/
@[simp]
theorem inverse_eval {n : Nat} (circuit : Circuit n) :
    eval (inverse circuit) = Conservative.inverse (eval circuit) := by
  apply Conservative.ext
  apply Equiv.ext
  intro input
  let original := eval circuit
  have represented : original (original.toEquiv.symm input) = input :=
    original.toEquiv.apply_symm_apply input
  calc
    eval (inverse circuit) input =
        eval (inverse circuit) (original (original.toEquiv.symm input)) := by
          rw [represented]
    _ = original.toEquiv.symm input :=
      eval_inverse_eval_structural circuit (original.toEquiv.symm input)
    _ = Conservative.inverse original input := rfl

/-- Evaluating a circuit and then its inverse restores the complete input. -/
@[simp]
theorem eval_inverse_eval {n : Nat} (circuit : Circuit n)
    (input : BitState n) :
    eval (inverse circuit) (eval circuit input) = input := by
  rw [inverse_eval]
  exact (eval circuit).toEquiv.symm_apply_apply input

/-- Evaluating an inverse circuit and then the original restores the complete input. -/
@[simp]
theorem eval_eval_inverse {n : Nat} (circuit : Circuit n)
    (input : BitState n) :
    eval circuit (eval (inverse circuit) input) = input := by
  rw [inverse_eval]
  exact (eval circuit).toEquiv.apply_symm_apply input

/-! ## Exact reversal of grammar-induced paths -/

namespace PathDelay

/--
Every grammar-induced path reverses its endpoints under syntactic inversion
without changing its explicit unit-wire count.
-/
theorem inverse {n : Nat} (circuit : Circuit n)
    {input output : Fin n} {delay : Nat}
    (path : PathDelay circuit input output delay) :
    PathDelay (Circuit.inverse circuit) output input delay := by
  induction circuit generalizing delay with
  | identity width =>
      rcases path with ⟨rfl, rfl⟩
      exact identity input
  | unitWire => exact path
  | fredkin => exact path
  | permute wiring =>
      rcases path with ⟨rfl, rfl⟩
      exact ⟨by simp, rfl⟩
  | seq first second firstIH secondIH =>
      rcases path with
        ⟨middle, firstDelay, secondDelay, firstPath, secondPath, rfl⟩
      simpa [Nat.add_comm] using
        PathDelay.seq (secondIH secondPath) (firstIH firstPath)
  | tensor left right leftIH rightIH =>
      rcases path with
        ⟨leftInput, leftOutput, rfl, rfl, leftPath⟩ |
        ⟨rightInput, rightOutput, rfl, rfl, rightPath⟩
      · exact tensorLeft (leftIH leftPath)
      · exact tensorRight (rightIH rightPath)

end PathDelay

/-- Exact path reversal is an equivalence because structural inversion is involutive. -/
@[simp]
theorem pathDelay_inverse_iff {n : Nat} (circuit : Circuit n)
    {input output : Fin n} {delay : Nat} :
    PathDelay (inverse circuit) output input delay ↔
      PathDelay circuit input output delay := by
  constructor
  · intro path
    have reversed := PathDelay.inverse (inverse circuit) path
    simpa using reversed
  · exact PathDelay.inverse circuit

/-! ## Uniform latency and paper-combinational timing -/

namespace HasLatency

/-- Syntactic inversion preserves every common boundary-path latency. -/
theorem inverse {n latency : Nat} {circuit : Circuit n}
    (timed : HasLatency circuit latency) :
    HasLatency (Circuit.inverse circuit) latency := by
  intro input output actual path
  exact timed ((pathDelay_inverse_iff circuit).mp path)

/--
A circuit followed by its inverse has the sum of the two pass latencies; delay
does not cancel when static values do.
-/
theorem seq_inverse {n latency : Nat} {circuit : Circuit n}
    (timed : HasLatency circuit latency) :
    HasLatency (.seq circuit (Circuit.inverse circuit)) (latency + latency) :=
  HasLatency.seq timed timed.inverse

/-- The inverse-first round trip has the same doubled path latency. -/
theorem inverse_seq {n latency : Nat} {circuit : Circuit n}
    (timed : HasLatency circuit latency) :
    HasLatency (.seq (Circuit.inverse circuit) circuit) (latency + latency) :=
  HasLatency.seq timed.inverse timed

end HasLatency

/-- A circuit and its structural inverse have exactly the same uniform latencies. -/
@[simp]
theorem hasLatency_inverse_iff {n latency : Nat} (circuit : Circuit n) :
    HasLatency (inverse circuit) latency ↔ HasLatency circuit latency := by
  constructor
  · intro timed input output actual path
    exact timed (PathDelay.inverse circuit path)
  · exact HasLatency.inverse

namespace MeetsPaperCombinationalTiming

/--
The corrected feed-forward inverse preserves the paper's global equal-path
timing condition.
-/
theorem inverse {n : Nat} {circuit : Circuit n}
    (timed : MeetsPaperCombinationalTiming circuit) :
    MeetsPaperCombinationalTiming (Circuit.inverse circuit) := by
  rcases timed with ⟨latency, uniform⟩
  exact ⟨latency, uniform.inverse⟩

end MeetsPaperCombinationalTiming

/-- Paper-combinational timing holds for an inverse exactly when it holds forward. -/
@[simp]
theorem meetsPaperCombinationalTiming_inverse_iff {n : Nat}
    (circuit : Circuit n) :
    MeetsPaperCombinationalTiming (inverse circuit) ↔
      MeetsPaperCombinationalTiming circuit := by
  constructor
  · intro timed
    have reinverted :=
      MeetsPaperCombinationalTiming.inverse (circuit := inverse circuit) timed
    simpa using reinverted
  · exact MeetsPaperCombinationalTiming.inverse

namespace UniformLatencyCircuit

/-- A proof-only uniform-latency certificate for the structural inverse. -/
def inverse {n latency : Nat} (circuit : UniformLatencyCircuit n latency) :
    UniformLatencyCircuit n latency :=
  ⟨Circuit.inverse circuit.toCircuit,
    HasLatency.inverse circuit.hasLatency⟩

end UniformLatencyCircuit

end ConservativeLogic.Circuit
