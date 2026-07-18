import ConservativeLogic.Circuit.Syntax
import ConservativeLogic.Gate.UnitWire

/-!
# Static path timing for feed-forward circuits

This module counts explicit unit-wire constructors along directed boundary
paths. Fredkin gates, structural identities, and structural permutations are
instantaneous; serial paths add delays; tensor paths stay inside their ordered
block. The resulting predicate captures the equal-unit-wire-path condition in
§7.1 of Fredkin and Toffoli for this corrected feed-forward grammar.

This is not a tick, trace, stream, transition, feedback, or oriented
time-reversal semantics. Every `Circuit` term is feed-forward by construction,
but only a term satisfying `MeetsPaperCombinationalTiming` meets the paper's
additional global equal-path-latency condition.
-/

namespace ConservativeLogic.Circuit

/--
`PathDelay circuit input output delay` means that one grammar-induced directed
boundary route from `input` to `output` traverses exactly `delay` explicit unit
wires.

For the instantaneous Fredkin node, every input port has a zero-wire path to
every output port. This is the chosen primitive-node connectivity convention,
not Boolean functional dependence or a proved graph correspondence. The
relation is structurally recursive so tensor's `m + n` index can be eliminated
without dependent-inductive transport.
-/
def PathDelay : {n : Nat} → Circuit n → Fin n → Fin n → Nat → Prop
  | _, .identity _, input, output, delay => input = output ∧ delay = 0
  | _, .unitWire, _, _, delay => delay = UnitWire.delay
  | _, .fredkin, _, _, delay => delay = 0
  | _, .permute wiring, input, output, delay => output = wiring input ∧ delay = 0
  | _, .seq first second, input, output, delay =>
      ∃ middle firstDelay secondDelay,
        PathDelay first input middle firstDelay ∧
        PathDelay second middle output secondDelay ∧
        delay = firstDelay + secondDelay
  | _, .tensor left right, input, output, delay =>
      (∃ leftInput leftOutput,
        input = Fin.castAdd _ leftInput ∧
        output = Fin.castAdd _ leftOutput ∧
        PathDelay left leftInput leftOutput delay) ∨
      (∃ rightInput rightOutput,
        input = Fin.natAdd _ rightInput ∧
        output = Fin.natAdd _ rightOutput ∧
        PathDelay right rightInput rightOutput delay)

namespace PathDelay

/-- Structural identity has a zero-delay path from each port to itself. -/
theorem identity {n : Nat} (i : Fin n) : PathDelay (.identity n) i i 0 :=
  ⟨rfl, rfl⟩

/-- The unit-wire path carries exactly the Stage 3 delay metadata. -/
theorem unitWire :
    PathDelay .unitWire (0 : Fin 1) (0 : Fin 1) UnitWire.delay :=
  rfl

/-- Exact numeral form of the unit-wire path delay. -/
theorem unitWire_one : PathDelay .unitWire (0 : Fin 1) (0 : Fin 1) 1 := by
  simpa using unitWire

/-- Every grammar-induced route through the instantaneous Fredkin node has delay zero. -/
theorem fredkin (input output : Fin 3) : PathDelay .fredkin input output 0 :=
  rfl

/-- Structural reindexing moves old port `i` to new port `wiring i` at zero delay. -/
theorem permute {n : Nat} (wiring : WirePerm n) (i : Fin n) :
    PathDelay (.permute wiring) i (wiring i) 0 :=
  ⟨rfl, rfl⟩

/-- Serial paths join at one middle port and add their unit-wire delays. -/
theorem seq {n : Nat} {first second : Circuit n} {input middle output : Fin n}
    {firstDelay secondDelay : Nat}
    (firstPath : PathDelay first input middle firstDelay)
    (secondPath : PathDelay second middle output secondDelay) :
    PathDelay (.seq first second) input output (firstDelay + secondDelay) :=
  ⟨middle, firstDelay, secondDelay, firstPath, secondPath, rfl⟩

/-- A left-block path embeds into tensor without changing delay. -/
theorem tensorLeft {m n : Nat} {left : Circuit m} {right : Circuit n}
    {input output : Fin m} {delay : Nat}
    (path : PathDelay left input output delay) :
    PathDelay (.tensor left right) (Fin.castAdd n input) (Fin.castAdd n output) delay :=
  Or.inl ⟨input, output, rfl, rfl, path⟩

/-- A right-block path embeds into tensor without changing delay. -/
theorem tensorRight {m n : Nat} {left : Circuit m} {right : Circuit n}
    {input output : Fin n} {delay : Nat}
    (path : PathDelay right input output delay) :
    PathDelay (.tensor left right) (Fin.natAdd m input) (Fin.natAdd m output) delay :=
  Or.inr ⟨input, output, rfl, rfl, path⟩

end PathDelay

/-- Every existing boundary path of `circuit` has exactly the given latency. -/
def HasLatency {n : Nat} (circuit : Circuit n) (latency : Nat) : Prop :=
  ∀ {input output actual}, PathDelay circuit input output actual → actual = latency

/--
The equal-path part of the paper's combinational timing criterion on this
already-feed-forward syntax: there is one latency shared by every existing
external boundary path. This does not assert that the term is a literal paper
graph. At width zero, latency zero is a canonical witness, but uniqueness is
not claimed.
-/
def MeetsPaperCombinationalTiming {n : Nat} (circuit : Circuit n) : Prop :=
  ∃ latency, HasLatency circuit latency

/-- A uniform-latency certificate implies the selected paper timing criterion. -/
theorem HasLatency.meetsPaperCombinationalTiming
    {n latency : Nat} {circuit : Circuit n}
    (uniform : HasLatency circuit latency) : MeetsPaperCombinationalTiming circuit :=
  ⟨latency, uniform⟩

/-- Structural identity has uniform latency zero, including at width zero. -/
theorem hasLatency_identity (n : Nat) : HasLatency (.identity n) 0 := by
  intro input output actual path
  exact path.2

/-- The unit wire has exactly its Stage 3 latency metadata. -/
theorem hasLatency_unitWire : HasLatency .unitWire UnitWire.delay := by
  intro input output actual path
  exact path

/-- Exact numeral form of unit-wire uniform latency. -/
theorem hasLatency_unitWire_one : HasLatency .unitWire 1 := by
  intro input output actual path
  exact path.trans UnitWire.delay_eq_one

/-- The instantaneous Fredkin gate has uniform latency zero. -/
theorem hasLatency_fredkin : HasLatency .fredkin 0 := by
  intro input output actual path
  exact path

/-- Structural boundary reindexing has uniform latency zero. -/
theorem hasLatency_permute {n : Nat} (wiring : WirePerm n) :
    HasLatency (.permute wiring) 0 := by
  intro input output actual path
  exact path.2

/-- Uniform serial latencies add. -/
theorem HasLatency.seq {n firstLatency secondLatency : Nat}
    {first second : Circuit n} (hfirst : HasLatency first firstLatency)
    (hsecond : HasLatency second secondLatency) :
    HasLatency (.seq first second) (firstLatency + secondLatency) := by
  intro input output actual path
  rcases path with ⟨middle, actualFirst, actualSecond, firstPath, secondPath, rfl⟩
  exact congrArg₂ Nat.add (hfirst firstPath) (hsecond secondPath)

/-- Tensor has a uniform latency when both disjoint blocks have that latency. -/
theorem HasLatency.tensor {m n latency : Nat} {left : Circuit m} {right : Circuit n}
    (hleft : HasLatency left latency) (hright : HasLatency right latency) :
    HasLatency (.tensor left right) latency := by
  intro input output actual path
  rcases path with ⟨leftInput, leftOutput, rfl, rfl, leftPath⟩ |
    ⟨rightInput, rightOutput, rfl, rfl, rightPath⟩
  · exact hleft leftPath
  · exact hright rightPath

private theorem castAdd_ne_natAdd {m n : Nat} (left : Fin m) (right : Fin n) :
    Fin.castAdd n left ≠ Fin.natAdd m right := by
  intro equality
  have impossible : (Sum.inl left : Fin m ⊕ Fin n) = Sum.inr right :=
    finSumFinEquiv.injective (by simpa using equality)
  cases impossible

/--
Two blockwise tensor stages have uniform total latency when each block's two
stage delays compensate to the same total. Neither intermediate tensor must
itself have uniform latency.
-/
theorem HasLatency.compensatedTensorSeq
    {m n leftFirstLatency leftSecondLatency rightFirstLatency rightSecondLatency
      total : Nat}
    {leftFirst leftSecond : Circuit m} {rightFirst rightSecond : Circuit n}
    (hLeftFirst : HasLatency leftFirst leftFirstLatency)
    (hLeftSecond : HasLatency leftSecond leftSecondLatency)
    (hRightFirst : HasLatency rightFirst rightFirstLatency)
    (hRightSecond : HasLatency rightSecond rightSecondLatency)
    (hLeftTotal : leftFirstLatency + leftSecondLatency = total)
    (hRightTotal : rightFirstLatency + rightSecondLatency = total) :
    HasLatency
      (.seq (.tensor leftFirst rightFirst) (.tensor leftSecond rightSecond)) total := by
  intro input output actual path
  rcases path with
    ⟨middle, actualFirst, actualSecond, firstPath, secondPath, rfl⟩
  rcases firstPath with
    ⟨leftInput₁, leftMiddle, inputLeft, middleLeft, leftFirstPath⟩ |
    ⟨rightInput₁, rightMiddle, inputRight, middleRight, rightFirstPath⟩
  · rcases secondPath with
      ⟨leftInput₂, leftOutput, middleLeft', outputLeft, leftSecondPath⟩ |
      ⟨rightInput₂, rightOutput, middleRight', outputRight, rightSecondPath⟩
    · exact (congrArg₂ Nat.add (hLeftFirst leftFirstPath)
        (hLeftSecond leftSecondPath)).trans hLeftTotal
    · exact (castAdd_ne_natAdd leftMiddle rightInput₂
        (middleLeft.symm.trans middleRight')).elim
  · rcases secondPath with
      ⟨leftInput₂, leftOutput, middleLeft', outputLeft, leftSecondPath⟩ |
      ⟨rightInput₂, rightOutput, middleRight', outputRight, rightSecondPath⟩
    · exact (castAdd_ne_natAdd leftInput₂ rightMiddle
        (middleLeft'.symm.trans middleRight)).elim
    · exact (congrArg₂ Nat.add (hRightFirst rightFirstPath)
        (hRightSecond rightSecondPath)).trans hRightTotal

/-- A circuit paired only with a static proof of one uniform boundary-path latency. -/
structure UniformLatencyCircuit (n latency : Nat) where
  toCircuit : Circuit n
  hasLatency : HasLatency toCircuit latency

namespace UniformLatencyCircuit

/-- Certified zero-delay structural identity. -/
def identity (n : Nat) : UniformLatencyCircuit n 0 :=
  ⟨.identity n, hasLatency_identity n⟩

/-- Certified delay-one unit wire. -/
def unitWire : UniformLatencyCircuit 1 UnitWire.delay :=
  ⟨.unitWire, hasLatency_unitWire⟩

/-- Certified instantaneous Fredkin gate. -/
def fredkin : UniformLatencyCircuit 3 0 :=
  ⟨.fredkin, hasLatency_fredkin⟩

/-- Certified zero-delay structural port reindexing. -/
def permute {n : Nat} (wiring : WirePerm n) : UniformLatencyCircuit n 0 :=
  ⟨.permute wiring, hasLatency_permute wiring⟩

/-- Serial composition of timing certificates adds latencies. -/
def seq {n firstLatency secondLatency : Nat}
    (first : UniformLatencyCircuit n firstLatency)
    (second : UniformLatencyCircuit n secondLatency) :
    UniformLatencyCircuit n (firstLatency + secondLatency) :=
  ⟨.seq first.toCircuit second.toCircuit,
    HasLatency.seq first.hasLatency second.hasLatency⟩

/-- Parallel timing certificates compose when both blocks have equal latency. -/
def tensor {m n latency : Nat} (left : UniformLatencyCircuit m latency)
    (right : UniformLatencyCircuit n latency) :
    UniformLatencyCircuit (m + n) latency :=
  ⟨.tensor left.toCircuit right.toCircuit,
    HasLatency.tensor left.hasLatency right.hasLatency⟩

end UniformLatencyCircuit

end ConservativeLogic.Circuit
