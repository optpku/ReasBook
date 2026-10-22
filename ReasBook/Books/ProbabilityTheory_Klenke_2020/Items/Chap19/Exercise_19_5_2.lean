/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_32
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- Helper for Exercise 19.5.2: the event that the trajectory `X` first hits `insert y A` at the
state `y`, allowing the hit to occur already at time `0`. -/
private def firstHitAtStateEvent {E : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- Helper for Exercise 19.5.2: `F_A P X A x y` is the probability that the first hit of
`insert y A` occurs at `y`, possibly already at time `0`. -/
def F_A {E : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

end ProbabilityTheory

namespace ProbabilityTheory.DiscreteMarkovChain

/-
`source-facing`: the two-hexagon honeycomb graph together with the distinguished vertices
`one`, `zero`, and `start = x`.
`core/canonical`: the Chapter 19 graph-walk owner `IsSimpleRandomWalk`, the discrete-kernel owner
`discreteMatrixKernel`, and the first-hit owner `F_A`.
`bridge/view`: the concrete transition matrix `honeycombTransitionMatrix`, obtained from the unit
conductances of the honeycomb graph.
-/

/-- The ten vertices of the two-hexagon honeycomb graph from Exercise 19.5.2, with distinguished
vertices `one`, `zero`, and `start = x`. -/
inductive HoneycombVertex
  | one
  | leftUpper
  | sharedUpper
  | start
  | lowerMiddle
  | leftLower
  | rightUpperLeft
  | rightUpperRight
  | zero
  | rightLower
  deriving DecidableEq, Fintype, Nonempty

open HoneycombVertex

/-- The finite honeycomb state space carries the discrete measurable structure. -/
instance : MeasurableSpace HoneycombVertex := ⊤

/-- The measurable structure on the honeycomb state space is discrete. -/
instance : DiscreteMeasurableSpace HoneycombVertex := by
  infer_instance

/-- The undirected edges of the two-hexagon honeycomb graph, listed once each. -/
private def honeycombEdges : Finset (HoneycombVertex × HoneycombVertex) :=
  { (one, leftUpper),
    (one, leftLower),
    (leftUpper, sharedUpper),
    (sharedUpper, start),
    (sharedUpper, rightUpperLeft),
    (start, lowerMiddle),
    (start, rightLower),
    (lowerMiddle, leftLower),
    (rightUpperLeft, rightUpperRight),
    (rightUpperRight, zero),
    (zero, rightLower) }

/-- The adjacency relation of the two-hexagon honeycomb graph. -/
private def honeycombAdj (x y : HoneycombVertex) : Prop :=
  (x, y) ∈ honeycombEdges ∨ (y, x) ∈ honeycombEdges

private theorem honeycombAdj_symm : Symmetric honeycombAdj := by
  intro x y hxy
  simpa [honeycombAdj, or_comm] using hxy

private theorem honeycombAdj_irrefl : Std.Irrefl honeycombAdj := by
  exact ⟨fun x ↦ by
    cases x <;> simp [honeycombAdj, honeycombEdges]⟩

/-- The two-hexagon honeycomb graph from Exercise 19.5.2. -/
def honeycombGraph : SimpleGraph HoneycombVertex where
  Adj := honeycombAdj
  symm := honeycombAdj_symm
  loopless := honeycombAdj_irrefl

/-- The unit conductance family of the honeycomb graph. -/
def honeycombConductance : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  simpleGraphWeights honeycombGraph

/-- Helper for Exercise 19.5.2: the transition matrix obtained by normalizing a conductance family
rowwise. -/
private def conductanceTransitionMatrix
    {E : Type*} (C : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  C x y / conductance C x

/-- Helper for Exercise 19.5.2: `conductanceTransitionMatrix C x y` is the quotient
`C x y / conductance C x`. -/
@[simp] private theorem conductanceTransitionMatrix_apply
    {E : Type*} (C : E → E → ℝ≥0∞) (x y : E) :
    conductanceTransitionMatrix C x y = C x y / conductance C x :=
  rfl

/-- Helper for Exercise 19.5.2: the normalized conductance matrix is stochastic when every row has
finite positive total conductance. -/
private theorem conductanceTransitionMatrix_isStochastic
    {E : Type*} {C : E → E → ℝ≥0∞}
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsStochasticMatrix (conductanceTransitionMatrix C) := by
  intro x
  calc
    ∑' y : E, conductanceTransitionMatrix C x y
        = ∑' y : E, C x y * (conductance C x)⁻¹ := by
            simp_rw [conductanceTransitionMatrix_apply, div_eq_mul_inv]
    _ = (∑' y : E, C x y) * (conductance C x)⁻¹ := ENNReal.tsum_mul_right
    _ = conductance C x * (conductance C x)⁻¹ := by rw [← conductance]
    _ = 1 := ENNReal.mul_inv_cancel (ne_of_gt (hC_pos x)) (ne_of_lt (hC_finite x))

/-- Helper for Exercise 19.5.2: normalizing a symmetric conductance family gives the associated
random walk with weights. -/
private theorem conductanceTransitionMatrix_isRandomWalkWithWeights
    {E : Type*} {C : E → E → ℝ≥0∞}
    (hC_symm : ∀ x y : E, C x y = C y x)
    (hC_finite : ∀ x : E, conductance C x < ∞)
    (hC_pos : ∀ x : E, 0 < conductance C x) :
    IsRandomWalkWithWeights (conductanceTransitionMatrix C) C where
  isStochastic := conductanceTransitionMatrix_isStochastic hC_finite hC_pos
  symmetric := hC_symm
  transition_eq := conductanceTransitionMatrix_apply C

/-- The simple random-walk transition matrix on the honeycomb graph. -/
def honeycombTransitionMatrix : HoneycombVertex → HoneycombVertex → ℝ≥0∞ :=
  conductanceTransitionMatrix honeycombConductance

/-- Helper for Exercise 19.5.2: the total conductance at each honeycomb vertex is its graph
degree, namely `3` at `sharedUpper` and `start`, and `2` elsewhere. -/
theorem honeycombConductance_vertexWeight (x : HoneycombVertex) :
    conductance honeycombConductance x =
      if x = sharedUpper ∨ x = start then 3 else 2 := by
  -- Proof comment: this is a finite row sum of unit edge weights, so enumerating the ten
  -- vertices leaves exactly the graph degree of `x`.
  rw [conductance, tsum_fintype]
  cases x <;>
    norm_num [honeycombConductance, simpleGraphWeights, honeycombGraph, honeycombAdj, honeycombEdges] <;>
    exact_mod_cast (by decide : _)

-- Proof sketch: each honeycomb vertex has degree `2` or `3`, so the normalized unit-conductance
-- walk on `honeycombGraph` is exactly the simple random walk on that graph.
/-- The honeycomb transition matrix is the Chapter 19 simple-random-walk owner on
`honeycombGraph`. -/
theorem honeycombTransitionMatrix_isSimpleRandomWalk :
    IsSimpleRandomWalk honeycombTransitionMatrix honeycombGraph := by
  -- Proof comment: the walk is exactly the unit-conductance random walk once the row sums are
  -- identified with the vertex degrees from `honeycombConductance_vertexWeight`.
  refine conductanceTransitionMatrix_isRandomWalkWithWeights ?_ ?_ ?_
  · simpa [honeycombConductance] using simpleGraphWeights_symmetric honeycombGraph
  · intro x
    rw [honeycombConductance_vertexWeight]
    split_ifs <;> simp
  · intro x
    rw [honeycombConductance_vertexWeight]
    split_ifs <;> simp

/-- The honeycomb transition matrix is stochastic. -/
theorem honeycombTransitionMatrix_isStochastic :
    IsStochasticMatrix honeycombTransitionMatrix :=
  IsRandomWalkWithWeights.isStochasticMatrix honeycombTransitionMatrix_isSimpleRandomWalk

/-- The discrete kernel associated with `honeycombTransitionMatrix` is Markov. -/
instance : IsMarkovKernel (discreteMatrixKernel honeycombTransitionMatrix) :=
  discreteMatrixKernel_isMarkovKernel _ honeycombTransitionMatrix_isStochastic

/-- Helper for Exercise 19.5.2: the absorbing boundary for the first-hit problem is
`{one, zero}`. -/
private def honeycombBoundary : Set HoneycombVertex :=
  ({HoneycombVertex.one, zero} : Set HoneycombVertex)

section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : HoneycombVertex → ProbabilityMeasure Ω}
variable {X : ℕ → Ω → HoneycombVertex}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel honeycombTransitionMatrix ^ n) P X]

/-- Helper for Exercise 19.5.2: summing over `HoneycombVertex` expands into the ten explicit
vertices of the honeycomb graph. -/
private lemma sum_honeycombVertex {α : Type*} [AddCommMonoid α] (f : HoneycombVertex → α) :
    ∑ y : HoneycombVertex, f y =
      f HoneycombVertex.one + f leftUpper + f sharedUpper + f start + f lowerMiddle +
        f leftLower + f rightUpperLeft + f rightUpperRight + f zero + f rightLower := by
  rw [show (Finset.univ : Finset HoneycombVertex) =
      { HoneycombVertex.one, leftUpper, sharedUpper, start, lowerMiddle, leftLower,
        rightUpperLeft, rightUpperRight, zero, rightLower } by decide]
  simp [add_assoc]

/-- Helper for Exercise 19.5.2: the explicit unit-boundary voltage on the honeycomb graph, with
value `1` at `one`, value `0` at `zero`, and the harmonic interpolation values on the interior
vertices. -/
private def honeycombVoltage : HoneycombVertex → ℝ
  | HoneycombVertex.one => 1
  | leftUpper => 13 / 17
  | sharedUpper => 9 / 17
  | start => 8 / 17
  | lowerMiddle => 11 / 17
  | leftLower => 14 / 17
  | rightUpperLeft => 6 / 17
  | rightUpperRight => 3 / 17
  | zero => 0
  | rightLower => 4 / 17

/-- Helper for Exercise 19.5.2: the explicit honeycomb voltage satisfies Kirchhoff's law off the
boundary `{one, zero}`. -/
private theorem honeycombVoltage_isElectricalPotential :
    IsElectricalPotential honeycombConductance honeycombBoundary honeycombVoltage := by
  refine
    { antisymm := ?_
      netFlowAt_eq_zero := ?_ }
  · intro x y
    rw [electricalCurrent_apply, electricalCurrent_apply, honeycombConductance,
      simpleGraphWeights_symmetric honeycombGraph x y]
    ring
  · intro x hx
    cases x with
    | one =>
        exact False.elim (hx (by simp [honeycombBoundary]))
    | leftUpper =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | sharedUpper =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | start =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | lowerMiddle =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | leftLower =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | rightUpperLeft =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | rightUpperRight =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num
    | zero =>
        exact False.elim (hx (by simp [honeycombBoundary]))
    | rightLower =>
        rw [netFlowAt, sum_honeycombVertex]
        simp [electricalCurrent_apply, honeycombConductance, honeycombVoltage, honeycombGraph,
          honeycombAdj, honeycombEdges, simpleGraphWeights]
        norm_num

/-- Helper for Exercise 19.5.2: the explicit honeycomb voltage matches the boundary datum
`1` at `one` and `0` at `zero`. -/
private theorem honeycombVoltage_eqOn_boundary :
    Set.EqOn honeycombVoltage
      (fun z : HoneycombVertex ↦ if z = HoneycombVertex.one then (1 : ℝ) else 0)
      honeycombBoundary := by
  intro z hz
  rcases (by
      simpa [honeycombBoundary, Set.mem_insert_iff, Set.mem_singleton_iff] using hz) with rfl | rfl
  · simp [honeycombVoltage]
  · simp [honeycombVoltage]

/-- Helper for Exercise 19.5.2: every honeycomb vertex is connected to `start` in the honeycomb
graph. -/
private theorem honeycombReachableToStart (x : HoneycombVertex) :
    honeycombGraph.Reachable x start := by
  cases x with
  | one =>
      exact
        (show honeycombGraph.Adj one leftUpper by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj leftUpper sharedUpper by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj sharedUpper start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | leftUpper =>
      exact
        (show honeycombGraph.Adj leftUpper sharedUpper by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj sharedUpper start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | sharedUpper =>
      exact
        (show honeycombGraph.Adj sharedUpper start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | start =>
      simp
  | lowerMiddle =>
      exact
        (show honeycombGraph.Adj lowerMiddle start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | leftLower =>
      exact
        (show honeycombGraph.Adj leftLower lowerMiddle by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj lowerMiddle start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | rightUpperLeft =>
      exact
        (show honeycombGraph.Adj rightUpperLeft sharedUpper by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj sharedUpper start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | rightUpperRight =>
      exact
        (show honeycombGraph.Adj rightUpperRight rightUpperLeft by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj rightUpperLeft sharedUpper by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj sharedUpper start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | zero =>
      exact
        (show honeycombGraph.Adj zero rightLower by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable.trans <|
        (show honeycombGraph.Adj rightLower start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable
  | rightLower =>
      exact
        (show honeycombGraph.Adj rightLower start by
          simp [honeycombGraph, honeycombAdj, honeycombEdges]).reachable

/-- Helper for Exercise 19.5.2: the honeycomb graph is connected. -/
private theorem honeycombReachable (x y : HoneycombVertex) :
    honeycombGraph.Reachable x y := by
  exact (honeycombReachableToStart x).trans (honeycombReachableToStart y).symm

/-- Helper for Exercise 19.5.2: an adjacent honeycomb edge carries positive one-step transition
mass for the simple random walk kernel. -/
private lemma honeycombKernel_singleton_pos_of_adj {x y : HoneycombVertex}
    (hxy : honeycombGraph.Adj x y) :
    0 < (discreteMatrixKernel honeycombTransitionMatrix) x ({y} : Set HoneycombVertex) := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [honeycombTransitionMatrix_isSimpleRandomWalk.transition_eq]
  refine (ENNReal.div_pos_iff).2 ?_
  refine ⟨?_, ne_of_lt (honeycombTransitionMatrix_isSimpleRandomWalk.conductance_lt_top x)⟩
  simp [simpleGraphWeights, hxy]

/-- Helper for Exercise 19.5.2: composing a positive first-step singleton mass with a positive
`n`-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private lemma honeycombKernel_singleton_pos_succ {x y z : HoneycombVertex} {n : ℕ}
    (hxy : 0 < (discreteMatrixKernel honeycombTransitionMatrix) x ({y} : Set HoneycombVertex))
    (hyz :
      0 < ((discreteMatrixKernel honeycombTransitionMatrix) ^ n) y ({z} : Set HoneycombVertex)) :
    0 < ((discreteMatrixKernel honeycombTransitionMatrix) ^ (n + 1)) x
      ({z} : Set HoneycombVertex) := by
  let κ := discreteMatrixKernel honeycombTransitionMatrix
  have hmeas :
      Measurable fun w : HoneycombVertex ↦ (κ ^ n) w ({z} : Set HoneycombVertex) :=
    Kernel.measurable_coe (κ ^ n) (MeasurableSet.singleton z)
  have hySupport :
      y ∈ Function.support fun w : HoneycombVertex ↦ (κ ^ n) w ({z} : Set HoneycombVertex) := by
    simpa [Function.support] using hyz.ne'
  have hsupportPos :
      0 < (κ x)
        (Function.support fun w : HoneycombVertex ↦ (κ ^ n) w ({z} : Set HoneycombVertex)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  have hcomp : 0 < (((κ ^ n) ∘ₖ κ) x) ({z} : Set HoneycombVertex) := by
    rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton z)]
    rw [MeasureTheory.lintegral_pos_iff_support hmeas]
    exact hsupportPos
  simpa [pow_succ] using hcomp

/-- Helper for Exercise 19.5.2: every honeycomb walk yields positive singleton transition mass
after the corresponding number of steps. -/
private lemma honeycombPositiveSingletonReachabilityOfWalk {x y : HoneycombVertex}
    (w : honeycombGraph.Walk x y) :
    ∃ n : ℕ,
      0 < ((discreteMatrixKernel honeycombTransitionMatrix) ^ n) x ({y} : Set HoneycombVertex) := by
  induction w with
  | @nil x =>
      refine ⟨0, ?_⟩
      have hself (v : HoneycombVertex) :
          0 < ((1 : Kernel HoneycombVertex HoneycombVertex) v) ({v} : Set HoneycombVertex) := by
        change 0 < (Measure.dirac v) ({v} : Set HoneycombVertex)
        simp
      simpa [pow_zero] using hself x
  | @cons x y z hxy w ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, honeycombKernel_singleton_pos_succ ?_ hn⟩
      exact honeycombKernel_singleton_pos_of_adj hxy

/-- Helper for Exercise 19.5.2: every pair of honeycomb vertices communicates with positive mass
after finitely many steps. -/
private lemma honeycombPositiveSingletonReachability (x y : HoneycombVertex) :
    ∃ n : ℕ,
      0 < ((discreteMatrixKernel honeycombTransitionMatrix) ^ n) x ({y} : Set HoneycombVertex) := by
  exact honeycombPositiveSingletonReachabilityOfWalk (Classical.choice (honeycombReachable x y))

/-- Helper for Exercise 19.5.2: the honeycomb simple random walk kernel is irreducible with
respect to counting measure. -/
private instance honeycombKernel_isIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure HoneycombVertex)
      (discreteMatrixKernel honeycombTransitionMatrix) where
  irreducible A _hA hApos x := by
    obtain ⟨y, hyA⟩ : A.Nonempty := by
      exact MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
    rcases honeycombPositiveSingletonReachability x y with ⟨n, hn⟩
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    exact measure_mono (Set.singleton_subset_iff.mpr hyA)

/-- Exercise 19.5.2: for the simple random walk on the two-hexagon honeycomb graph, started at the
distinguished vertex `x`, the probability of visiting `1` before `0` is `8 / 17`; this is the
value the exercise asks to recover both by network reduction and by matrix inversion. -/
theorem honeycomb_start_hittingProbability_one_before_zero :
    F_A P X ({zero} : Set HoneycombVertex) start HoneycombVertex.one = (8 : ℝ) / 17 := by
  letI : IsRandomWalkWithWeights honeycombTransitionMatrix honeycombConductance :=
    honeycombTransitionMatrix_isSimpleRandomWalk
  have hPotential :
      IsElectricalPotential honeycombConductance ({zero, HoneycombVertex.one} : Set HoneycombVertex)
        honeycombVoltage := by
    simpa [honeycombBoundary, Set.pair_comm] using honeycombVoltage_isElectricalPotential
  have hVoltageEq :
      honeycombVoltage start =
        F_A P X ({zero} : Set HoneycombVertex) start HoneycombVertex.one := by
    -- Proof comment: this is the generic finite-network voltage formula specialized to the
    -- honeycomb graph and the boundary `{zero, one}`.
    exact
      ProbabilityTheory.voltage_eq_probability_hit_one_before_zero
        (p := honeycombTransitionMatrix) (C := honeycombConductance)
        (P := P) (X := X) (u := honeycombVoltage)
        (zeroVertex := zero) (oneVertex := HoneycombVertex.one) (x := start)
        hPotential
        (by
          classical
          intro z hz
          rcases (by
              simpa [Set.mem_insert_iff, Set.mem_singleton_iff, Set.pair_comm] using hz) with
            rfl | rfl
          · simp [honeycombVoltage]
          · simp [honeycombVoltage])
  simpa [honeycombVoltage] using hVoltageEq.symm

end

end ProbabilityTheory.DiscreteMarkovChain
