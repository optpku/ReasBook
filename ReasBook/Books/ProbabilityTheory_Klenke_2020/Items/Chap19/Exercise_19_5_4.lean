/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Exercise_19_5_LadderGraphs
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_51
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Corollary_19_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/- Domain-style sampling for Exercise 19.5.4:
- `source-facing`: the crossed ladder graph of Fig. 19.16 with the distinguished vertices `a` and
  `z`.
- Inspected owner declarations:
  `SimpleLadderVertex`,
  `simpleLadderA`,
  `simpleLadderZ`,
  `effectiveConductance`,
  `escapeToSetProbability`.
- Best owner abstraction: the concrete Fig. 19.16 graph on the shared ladder carrier from
  `Exercise_19_5_LadderGraphs`, with the source quantities expressed through the Chapter 19 owners
  `effectiveConductance` and `escapeToSetProbability`.
- Primitive data: the graph of Fig. 19.16 itself. The carrier and marked vertices are reused from
  `Exercise_19_5_LadderGraphs` rather than duplicated.
  Derived API: the effective conductance between `a` and `z` and the hit-before-return probability
  for simple random walk on that graph.
- Source/core/bridge triage: this file is `source-facing`; it models the concrete graph from the
  figure, while the conductance and hitting-probability expressions are the existing canonical
  Chapter 19 bridge/view owners. -/

/- The concrete proof interface for Exercise 19.5.4 is the explicit unit-voltage potential that
is `0` at `a`, `1` at `z`, and `1 / 2` everywhere else. The crossed-ladder symmetry is then
captured by finite case-splitting rather than by a separate abstract symmetry API. -/

/-- Helper for Exercise 19.5.4: the explicit unit-voltage potential on the crossed ladder, with
boundary values `0` at `a`, `1` at `z`, and `1 / 2` on every other vertex. -/
private def crossedLadderVoltage : SimpleLadderVertex → ℝ :=
  fun x ↦
    if x = simpleLadderA then
      0
    else if x = simpleLadderZ then
      1
    else
      (1 / 2 : ℝ)

/-- Helper for Exercise 19.5.4: the explicit crossed-ladder voltage satisfies Kirchhoff's law off
the boundary `{a, z}`. -/
private theorem crossedLadderVoltage_isElectricalPotential :
    IsElectricalPotential (simpleGraphWeights crossedLadderGraph)
      ({simpleLadderA, simpleLadderZ} : Set SimpleLadderVertex) crossedLadderVoltage := by
  refine
    { antisymm := ?_
      netFlowAt_eq_zero := ?_ }
  · -- Proof comment: Ohm-law currents are antisymmetric because the conductance family is
    -- symmetric and the voltage drop changes sign when the edge orientation is reversed.
    intro x y
    rw [electricalCurrent_apply, electricalCurrent_apply,
      simpleGraphWeights_symmetric crossedLadderGraph x y]
    ring
  · intro x hx
    -- Proof comment: away from `a` and `z`, every crossed-ladder vertex either only sees the
    -- constant value `1 / 2`, or sees both boundary values symmetrically, so the net flow is `0`.
    rcases x with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp at hx <;>
      simp <;>
      rw [netFlowAt_def, Fintype.sum_prod_type] <;>
      repeat rw [Fin.sum_univ_succ] <;>
      repeat rw [Fin.sum_univ_zero] <;>
      simp [simpleLadderA, simpleLadderZ] <;>
      norm_num [electricalCurrent_apply, crossedLadderVoltage,
        crossedLadderGraph, simpleGraphWeights, pathGraph_adj]

/-- Helper for Exercise 19.5.4: the current induced by the explicit crossed-ladder voltage emits
total boundary flow `3` through the terminal vertex `z`. -/
private theorem crossedLadderBoundaryCurrent_eq_three :
    netFlowOnSet (electricalCurrent (simpleGraphWeights crossedLadderGraph) crossedLadderVoltage)
      ({simpleLadderZ} : Set SimpleLadderVertex) = 3 := by
  let leftBottom : SimpleLadderVertex := (⟨2, by decide⟩, ⟨0, by decide⟩)
  let leftTop : SimpleLadderVertex := (⟨2, by decide⟩, ⟨1, by decide⟩)
  let rightBottom : SimpleLadderVertex := (⟨4, by decide⟩, ⟨0, by decide⟩)
  let rightTop : SimpleLadderVertex := (⟨4, by decide⟩, ⟨1, by decide⟩)
  let s : Finset SimpleLadderVertex :=
    {simpleLadderA, leftBottom, leftTop, rightBottom, rightTop}
  have hzero :
      ∀ y ∉ s,
        electricalCurrent (simpleGraphWeights crossedLadderGraph) crossedLadderVoltage
          simpleLadderZ y = 0 := by
    intro y hy
    rcases y with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [s, leftBottom, leftTop, rightBottom, rightTop, simpleLadderA, simpleLadderZ,
        electricalCurrent_apply, crossedLadderVoltage, crossedLadderGraph, simpleGraphWeights,
        pathGraph_adj] at hy ⊢
  rw [netFlowOnSet_def]
  simp
  let f : SimpleLadderVertex → ℝ :=
    fun y ↦
      electricalCurrent (simpleGraphWeights crossedLadderGraph) crossedLadderVoltage
        simpleLadderZ y
  have hsum :
      (∑ y : SimpleLadderVertex, f y) = Finset.sum s f := by
    classical
    simpa only [f] using
      (Finset.sum_subset (s₁ := s) (s₂ := (Finset.univ : Finset SimpleLadderVertex))
        (by intro y hy; simp)
        (by
          intro y _ hy
          exact hzero y (by simpa [s] using hy))).symm
  calc
    ∑ y : SimpleLadderVertex, f y = Finset.sum s f := hsum
    _ = 3 := by
          norm_num [f, s, leftBottom, leftTop, rightBottom, rightTop, simpleLadderA,
            simpleLadderZ, electricalCurrent_apply, crossedLadderVoltage, crossedLadderGraph,
            simpleGraphWeights, pathGraph_adj]

/-- Helper for Exercise 19.5.4: the marked vertex `a` has total conductance `5` in the crossed
ladder graph. -/
private theorem crossedLadderConductance_at_a_eq_five :
    conductance (simpleGraphWeights crossedLadderGraph) simpleLadderA = 5 := by
  let leftBottom : SimpleLadderVertex := (⟨2, by decide⟩, ⟨0, by decide⟩)
  let leftTop : SimpleLadderVertex := (⟨2, by decide⟩, ⟨1, by decide⟩)
  let rightBottom : SimpleLadderVertex := (⟨4, by decide⟩, ⟨0, by decide⟩)
  let rightTop : SimpleLadderVertex := (⟨4, by decide⟩, ⟨1, by decide⟩)
  let s : Finset SimpleLadderVertex :=
    {simpleLadderZ, leftBottom, leftTop, rightBottom, rightTop}
  have hzero :
      ∀ y ∉ s, simpleGraphWeights crossedLadderGraph simpleLadderA y = 0 := by
    intro y hy
    rcases y with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [s, leftBottom, leftTop, rightBottom, rightTop, simpleLadderA, simpleLadderZ,
        crossedLadderGraph, simpleGraphWeights, pathGraph_adj] at hy ⊢
  rw [conductance, tsum_eq_sum hzero]
  have hone :
      ∀ y ∈ s, simpleGraphWeights crossedLadderGraph simpleLadderA y = 1 := by
    intro y hy
    rcases y with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [s, leftBottom, leftTop, rightBottom, rightTop, simpleLadderA, simpleLadderZ,
        crossedLadderGraph, simpleGraphWeights, pathGraph_adj] at hy ⊢
  calc
    Finset.sum s (fun y ↦ simpleGraphWeights crossedLadderGraph simpleLadderA y)
        = Finset.sum s (fun _ ↦ (1 : ℝ≥0∞)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hone y hy
    _ = 5 := by
          norm_num [s, leftBottom, leftTop, rightBottom, rightTop]

-- Proof sketch: by reflection symmetry across the horizontal midline and across the middle
-- column, every non-boundary column has potential `1 / 2` on both vertices in the unit boundary
-- value problem with `u(a) = 1` and `u(z) = 0`. The emitted current from `a` is therefore
-- `1 + 4 * (1 / 2) = 3`.
/-- Exercise 19.5.4 (1): for the crossed ladder graph of Fig. 19.16, the effective conductance
between `a` and `z` is `3`. -/
theorem crossedLadder_effectiveConductance_between_a_z_eq_three :
    effectiveConductance (simpleGraphWeights crossedLadderGraph)
      ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex) = 3 :=
  by
    have hA : ({simpleLadderA} : Set SimpleLadderVertex).Nonempty := ⟨simpleLadderA, by simp⟩
    have hZ : ({simpleLadderZ} : Set SimpleLadderVertex).Nonempty := ⟨simpleLadderZ, by simp⟩
    have hdisj :
        Disjoint ({simpleLadderA} : Set SimpleLadderVertex)
          ({simpleLadderZ} : Set SimpleLadderVertex) := by
      simp [simpleLadderA, simpleLadderZ]
    have hA0 :
        Set.EqOn crossedLadderVoltage (fun _ : SimpleLadderVertex ↦ 0)
          ({simpleLadderA} : Set SimpleLadderVertex) := by
      -- Proof comment: the chosen voltage is normalized to be `0` at the source boundary.
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [crossedLadderVoltage]
    have hZ1 :
        Set.EqOn crossedLadderVoltage (fun _ : SimpleLadderVertex ↦ 1)
          ({simpleLadderZ} : Set SimpleLadderVertex) := by
      -- Proof comment: the same normalization gives boundary value `1` at the terminal vertex.
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [crossedLadderVoltage]
    -- Route correction: close the theorem through Theorem 19.19 rather than by unfolding the
    -- infimum definition of `effectiveConductance`.
    calc
      effectiveConductance (simpleGraphWeights crossedLadderGraph)
          ({simpleLadderA} : Set SimpleLadderVertex) ({simpleLadderZ} : Set SimpleLadderVertex)
          =
            netFlowOnSet
              (electricalCurrent (simpleGraphWeights crossedLadderGraph) crossedLadderVoltage)
              ({simpleLadderZ} : Set SimpleLadderVertex) := by
                exact
                  effectiveConductance_eq_netFlowOnSet_electricalCurrent
                    hA hZ hdisj crossedLadderVoltage_isElectricalPotential hA0 hZ1
      _ = 3 := crossedLadderBoundaryCurrent_eq_three

/-- Helper for Exercise 19.5.4: the event that the first hit of `insert y A` occurs at the state
`y`, allowing the hit already at time `0`. -/
private def firstHitAtStateEvent {E : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- Helper for Exercise 19.5.4: `F_A P X A x y` is the probability that the first hit of
`insert y A` occurs at the state `y`. -/
private def F_A {E : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

section ProbabilisticBridge

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : SimpleLadderVertex → SimpleLadderVertex → ℝ≥0∞}
variable (P : SimpleLadderVertex → ProbabilityMeasure Ω) (X : ℕ → Ω → SimpleLadderVertex)
variable [IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph)]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Exercise 19.5.4: the explicit crossed-ladder voltage vanishes at `a`. -/
private theorem crossedLadderVoltage_at_a :
    crossedLadderVoltage simpleLadderA = 0 := by
  simp [crossedLadderVoltage]

/-- Helper for Exercise 19.5.4: the explicit crossed-ladder voltage is `1` at `z`. -/
private theorem crossedLadderVoltage_at_z :
    crossedLadderVoltage simpleLadderZ = 1 := by
  simp [crossedLadderVoltage, simpleLadderA, simpleLadderZ]

/-- Helper for Exercise 19.5.4: away from the boundary `{a, z}`, the explicit crossed-ladder
voltage takes the constant value `1 / 2`. -/
private theorem crossedLadderVoltage_eq_half_of_not_mem_boundary {x : SimpleLadderVertex}
    (hx : x ∉ simpleLadderBoundary) :
    crossedLadderVoltage x = (1 / 2 : ℝ) := by
  have hxa : x ≠ simpleLadderA := by
    intro h
    exact hx (by simpa [simpleLadderBoundary, h])
  have hxz : x ≠ simpleLadderZ := by
    intro h
    exact hx (by simpa [simpleLadderBoundary, h])
  simp [crossedLadderVoltage, hxa, hxz]

/-- Helper for Exercise 19.5.4: the ordinary ladder graph sits inside the crossed ladder. -/
private theorem simpleLadderGraph_le_crossedLadderGraph :
    simpleLadderGraph ≤ crossedLadderGraph := by
  intro x y hxy
  have hxy' : (pathGraph 7 □ pathGraph 2).Adj x y := by
    simpa [simpleLadderGraph] using hxy
  rcases (boxProd_adj.mp hxy') with hcol | hrow
  · exact Or.inl hcol.1
  · exact Or.inr ⟨hrow.2, hrow.1⟩

/-- Helper for Exercise 19.5.4: the crossed ladder is connected because it contains the connected
simple ladder graph. -/
private theorem crossedLadder_connected :
    crossedLadderGraph.Connected := by
  have hsimple : simpleLadderGraph.Connected := by
    simpa [simpleLadderGraph] using
      (connected_boxProd).2
        ⟨by simpa using (pathGraph_connected 6),
          by simpa using (pathGraph_connected 1)⟩
  exact hsimple.mono simpleLadderGraph_le_crossedLadderGraph

/-- Helper for Exercise 19.5.4: any two crossed-ladder vertices are joined by a graph walk. -/
private theorem crossedLadderReachable (x y : SimpleLadderVertex) :
    crossedLadderGraph.Reachable x y :=
  crossedLadder_connected x y

/-- Helper for Exercise 19.5.4: an adjacent crossed-ladder edge carries positive one-step mass for
the simple random walk kernel. -/
private lemma crossedLadderKernel_singleton_pos_of_adj {x y : SimpleLadderVertex}
    (hxy : crossedLadderGraph.Adj x y) :
    0 < (discreteMatrixKernel p) x ({y} : Set SimpleLadderVertex) := by
  have hp_xy : 0 < p x y := by
    rw [IsRandomWalkWithWeights.transition_eq
      (p := p) (C := simpleGraphWeights crossedLadderGraph) x y]
    refine (ENNReal.div_pos_iff).2 ?_
    refine ⟨by simpa [simpleGraphWeights] using hxy, ?_⟩
    exact ne_of_lt
      ((inferInstance :
        IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph)).conductance_lt_top x)
  rw [discreteMatrixKernel_apply_singleton]
  exact hp_xy

/-- Helper for Exercise 19.5.4: composing a positive first-step singleton mass with a positive
`n`-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private lemma crossedLadderKernel_singleton_pos_succ {x y z : SimpleLadderVertex} {n : ℕ}
    (hxy : 0 < (discreteMatrixKernel p) x ({y} : Set SimpleLadderVertex))
    (hyz : 0 < ((discreteMatrixKernel p) ^ n) y ({z} : Set SimpleLadderVertex)) :
    0 < ((discreteMatrixKernel p) ^ (n + 1)) x ({z} : Set SimpleLadderVertex) := by
  let κ := discreteMatrixKernel p
  have hmeas : Measurable fun w : SimpleLadderVertex ↦ (κ ^ n) w ({z} : Set SimpleLadderVertex) :=
    Kernel.measurable_coe (κ ^ n) (MeasurableSet.singleton z)
  have hySupport :
      y ∈ Function.support fun w : SimpleLadderVertex ↦ (κ ^ n) w ({z} : Set SimpleLadderVertex) := by
    simpa [Function.support] using hyz.ne'
  have hsupportPos :
      0 < (κ x)
        (Function.support fun w : SimpleLadderVertex ↦ (κ ^ n) w ({z} : Set SimpleLadderVertex)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the support of the `n`-step tail already contains `y`, so the composed kernel
  -- keeps positive mass on `z`.
  have hcomp :
      0 < (((κ ^ n) ∘ₖ κ) x) ({z} : Set SimpleLadderVertex) := by
    rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton z)]
    rw [MeasureTheory.lintegral_pos_iff_support hmeas]
    exact hsupportPos
  simpa [pow_succ] using hcomp

/-- Helper for Exercise 19.5.4: every crossed-ladder walk yields positive singleton transition
mass after the corresponding number of steps. -/
private lemma crossedLadderPositiveSingletonReachabilityOfWalk {x y : SimpleLadderVertex}
    (w : crossedLadderGraph.Walk x y) :
    ∃ n : ℕ,
      0 < ((discreteMatrixKernel p) ^ n) x ({y} : Set SimpleLadderVertex) := by
  induction w with
  | @nil x =>
      -- Proof comment: the zero-step kernel is the identity kernel.
      refine ⟨0, ?_⟩
      have hself (v : SimpleLadderVertex) :
          0 < ((1 : Kernel SimpleLadderVertex SimpleLadderVertex) v) ({v} : Set SimpleLadderVertex) := by
        change 0 < (Measure.dirac v) ({v} : Set SimpleLadderVertex)
        simp
      simpa [pow_zero] using hself x
  | @cons x y z hxy w ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, crossedLadderKernel_singleton_pos_succ (p := p) ?_ hn⟩
      exact crossedLadderKernel_singleton_pos_of_adj (p := p) hxy

/-- Helper for Exercise 19.5.4: every pair of crossed-ladder vertices communicates with positive
mass after finitely many steps. -/
private lemma crossedLadderPositiveSingletonReachability (x y : SimpleLadderVertex) :
    ∃ n : ℕ,
      0 < ((discreteMatrixKernel p) ^ n) x ({y} : Set SimpleLadderVertex) := by
  exact
    crossedLadderPositiveSingletonReachabilityOfWalk
      (p := p) (Classical.choice (crossedLadderReachable x y))

/-- Helper for Exercise 19.5.4: the crossed-ladder walk is irreducible with respect to counting
measure. -/
private instance crossedLadderKernel_isIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure SimpleLadderVertex) (discreteMatrixKernel p) where
  irreducible A _hA hApos x := by
    obtain ⟨y, hyA⟩ : A.Nonempty := by
      exact MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
    rcases crossedLadderPositiveSingletonReachability (p := p) x y with ⟨n, hn⟩
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    exact measure_mono (Set.singleton_subset_iff.mpr hyA)
/-- Helper for Exercise 19.5.4: the explicit crossed-ladder voltage matches the Dirichlet boundary
data `0` at `a` and `1` at `z`. -/
private theorem crossedLadderVoltage_eqOn_boundary :
    Set.EqOn crossedLadderVoltage
      (fun z : SimpleLadderVertex ↦ if z = simpleLadderZ then (1 : ℝ) else 0)
      ({simpleLadderA, simpleLadderZ} : Set SimpleLadderVertex) := by
  -- Proof comment: the boundary has only the two marked vertices, whose voltage values are known.
  intro z hz
  rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz with rfl | rfl
  · simp [crossedLadderVoltage_at_a]
  · simp [crossedLadderVoltage_at_z]

include p

/-- Helper for Exercise 19.5.4: under `P x`, the time-`0` state is `x` with probability `1`. -/
private theorem initialState_prob_eq_one (x : SimpleLadderVertex) :
    (P x : Measure Ω) {ω | X 0 ω = x} = 1 := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hpreimage : {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set SimpleLadderVertex) := by
    ext ω
    simp
  rw [hpreimage]
  rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)]
  rw [hReal.initial_eq x]
  simp

/-- Helper for Exercise 19.5.4: under `P x`, the realized crossed-ladder walk starts from `x`
almost surely. -/
private theorem initialState_ae_eq_start (x : SimpleLadderVertex) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hmeas : MeasurableSet {ω | X 0 ω = x} := by
    have hmeas' : MeasurableSet (X 0 ⁻¹' ({x} : Set SimpleLadderVertex)) :=
      hReal.measurable_process 0 (MeasurableSet.singleton x)
    simpa [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set SimpleLadderVertex) by
      ext ω
      simp] using hmeas'
  have hprob : (P x : Measure Ω) {ω | X 0 ω = x} = 1 := initialState_prob_eq_one
    (p := p) (P := P) (X := X) x
  -- Proof comment: once the time-`0` singleton event has probability `1`, `mem_ae_iff_prob_eq_one`
  -- upgrades it to the required almost-sure start statement.
  exact (mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Exercise 19.5.4: coordinatewise measurability makes the realized walk adapted to
its natural filtration. -/
private theorem adapted_processFiltration_of_measurable
    (hX_meas : ∀ n : ℕ, Measurable (X n)) :
    Adapted (processFiltration X) X := by
  intro n
  -- Proof comment: the coordinate map `X n` is one of the generators of the natural filtration
  -- `processFiltration X n`.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
    refine le_iSup_of_le n ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Exercise 19.5.4: the event that `hittingAfter X A 1` is finite is measurable. -/
private theorem hittingAfter_one_lt_top_measurableSet
    (hX_meas : ∀ n : ℕ, Measurable (X n)) (A : Set SimpleLadderVertex) :
    MeasurableSet {ω | hittingAfter X A 1 ω < ⊤} := by
  have hEq : {ω | hittingAfter X A 1 ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
      have hm_ne_top : hittingAfter X A 1 ω ≠ ⊤ := by
        rw [← hm]
        simp
      have hm_idx : (hittingAfter X A 1 ω).untopA = m := by
        rw [← hm, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hm_mem : X m ω ∈ A := by
        -- Proof comment: any finite first entrance time lands inside the target set.
        simpa [hm_idx] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hm_ne_top
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
          le_hittingAfter (u := X) (s := A) (n := 1) ω
        have hm_ge_one : 1 ≤ m := by
          have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
            exact le_of_le_of_eq hm_pos_top hm.symm
          exact_mod_cast hge_m
        exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm_ge_one)) hm_zero
      rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
      exact Set.mem_iUnion.2 ⟨n, by simpa [Set.mem_preimage] using hm_mem⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      have hn_mem : X n.succ ω ∈ A := by
        simpa [Set.mem_preimage] using hn
      have hle :
          hittingAfter X A 1 ω ≤ n.succ := by
        exact hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω)
          (Nat.succ_le_succ (Nat.zero_le n)) hn_mem
      exact lt_of_le_of_lt hle (by simp)
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  exact (hX_meas n.succ) MeasurableSet.of_discrete

/-- Helper for Exercise 19.5.4: if the start state lies outside `A`, then the entrance times
searched from `0` and from `1` coincide. -/
private theorem hittingAfter_zero_eq_one_of_not_mem_initial
    {A : Set SimpleLadderVertex} {ω : Ω} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  -- Proof comment: since `X 0 ω ∉ A`, the time-`0` search cannot stop at index `0`.
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      -- Proof comment: a finite entrance time always lands in the target set.
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Exercise 19.5.4: the positive-time first-return event
`{ω | (τ_[X, x]^1) ω < ⊤}` is measurable. -/
private theorem measurableSet_positiveFirstReturnTimeFinite
    {κ : ℕ → Kernel SimpleLadderVertex SimpleLadderVertex}
    [IsMarkovProcessRealization κ P X] (x : SimpleLadderVertex) :
    MeasurableSet {ω | (τ_[X, x]^1) ω < ⊤} := by
  have hEq :
      {ω | (τ_[X, x]^1) ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' ({x} : Set SimpleLadderVertex) := by
    ext ω
    constructor
    · intro hω
      rcases (hittingAfter_singleton_lt_top_iff X x ω).1 (by
          simpa [iteratedEntranceTime_one] using hω) with ⟨n, hn, hnx⟩
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
      exact Set.mem_iUnion.2
        ⟨m, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hnx⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      exact (hittingAfter_singleton_lt_top_iff X x ω).2
        ⟨n.succ, Nat.succ_pos _, by
          simpa [Set.mem_preimage, Set.mem_singleton_iff] using hn⟩
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  have hReal : IsMarkovProcessRealization κ P X := inferInstance
  exact (hReal.measurable_process n.succ) (measurableSet_singleton x)

/-- Helper for Exercise 19.5.4: finite expected first return time forces recurrence of the
starting state. -/
private theorem recurrentState_of_positiveRecurrentState
    {κ : ℕ → Kernel SimpleLadderVertex SimpleLadderVertex}
    [IsMarkovProcessRealization κ P X] {x : SimpleLadderVertex}
    (hx : IsPositiveRecurrentState P X x) :
    IsRecurrentState P X x := by
  let A : Set Ω := {ω | (τ_[X, x]^1) ω < ⊤}
  have hA_meas : MeasurableSet A := by
    simpa [A] using
      measurableSet_positiveFirstReturnTimeFinite
        (p := p) (κ := κ) (P := P) (X := X) x
  have hAc_zero : (P x : Measure Ω) Aᶜ = 0 := by
    by_contra hAc_zero
    have hindicator_top :
        ∫⁻ ω,
          Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) = ∞ := by
      have hmeas :
          AEMeasurable (Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞))) (P x : Measure Ω) :=
        (measurable_const.indicator hA_meas.compl).aemeasurable
      have hset :
          (P x : Measure Ω)
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} ≠ 0 := by
        have hEq :
            {ω | Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω = ∞} = Aᶜ := by
          ext ω
          by_cases hω : ω ∈ Aᶜ
          · have hnotA : ω ∉ A := hω
            simp [Set.indicator, hω, hnotA]
          · have hA : ω ∈ A := by simpa using hω
            simp [Set.indicator, hω, hA]
        simpa [hEq] using hAc_zero
      exact lintegral_eq_top_of_measure_eq_top_ne_zero hmeas hset
    have hdom :
        ∫⁻ ω, Set.indicator Aᶜ (fun _ ↦ (∞ : ℝ≥0∞)) ω ∂(P x : Measure Ω) ≤
          expectedFirstReturnTime P X x := by
      rw [expectedFirstReturnTime]
      refine lintegral_mono fun ω ↦ ?_
      by_cases hω : ω ∈ Aᶜ
      · have hτ : (τ_[X, x]^1) ω = ⊤ := by
          have hτne : ¬ (τ_[X, x]^1) ω ≠ ⊤ := by
            simpa [A, Set.mem_setOf_eq, lt_top_iff_ne_top] using hω
          exact not_not.mp hτne
        simp [Set.indicator, hω, hτ]
      · simp [Set.indicator, hω]
    have htop : expectedFirstReturnTime P X x = ∞ := by
      simpa [hindicator_top] using hdom
    exact (ne_of_lt hx) htop
  have hA_prob : (P x : Measure Ω) A = 1 := by
    have hA_le : (P x : Measure Ω) A ≤ 1 := by
      calc
        (P x : Measure Ω) A ≤ (P x : Measure Ω) Set.univ := by
          exact measure_mono (show A ⊆ Set.univ by intro ω _; simp)
        _ = 1 := by simp
    have hA_ge : 1 ≤ (P x : Measure Ω) A := by
      have hunion : A ∪ Aᶜ = Set.univ := by
        ext ω
        simp [A]
      have hUnion_le :
          (P x : Measure Ω) (A ∪ Aᶜ) ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ :=
        measure_union_le A Aᶜ
      calc
        1 = (P x : Measure Ω) Set.univ := by simp
        _ ≤ (P x : Measure Ω) A + (P x : Measure Ω) Aᶜ := by
              simpa [hunion] using hUnion_le
        _ = (P x : Measure Ω) A := by rw [hAc_zero, add_zero]
    exact le_antisymm hA_le hA_ge
  have hhit :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = 1 := by
    have hEq : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = A := by
      ext ω
      simpa [A, iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X x ω).symm
    rw [hEq]
    exact hA_prob
  -- Proof comment: recurrence is exactly the statement that the positive-time return probability
  -- equals one.
  rw [IsRecurrentState, everHitsProbability_def]
  exact (ENNReal.toReal_eq_one_iff _).2 hhit

/-- Helper for Exercise 19.5.4: every vertex of a weighted random walk has positive total
conductance. -/
private theorem crossedLadderConductance_ne_zero_at (x : SimpleLadderVertex) :
    conductance (simpleGraphWeights crossedLadderGraph) x ≠ 0 := by
  intro hx0
  have hC_zero : ∀ y : SimpleLadderVertex, simpleGraphWeights crossedLadderGraph x y = 0 := by
    intro y
    have hle :
        simpleGraphWeights crossedLadderGraph x y ≤
          conductance (simpleGraphWeights crossedLadderGraph) x := by
      simpa [conductance] using
        (ENNReal.le_tsum y :
          simpleGraphWeights crossedLadderGraph x y ≤
            ∑' z : SimpleLadderVertex, simpleGraphWeights crossedLadderGraph x z)
    rw [hx0] at hle
    exact le_antisymm hle bot_le
  have hp_zero : ∀ y : SimpleLadderVertex, p x y = 0 := by
    intro y
    rw [IsRandomWalkWithWeights.transition_eq
      (p := p) (C := simpleGraphWeights crossedLadderGraph) x y, hC_zero y, hx0]
    simp
  have hsum_zero : ∑ y : SimpleLadderVertex, p x y = 0 := by
    simp [hp_zero]
  have hstochastic : ∑' y : SimpleLadderVertex, p x y = 1 := by
    exact (inferInstance : IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph)).isStochasticMatrix x
  have hstochastic' : ∑ y : SimpleLadderVertex, p x y = 1 := by
    simpa using hstochastic
  rw [hsum_zero] at hstochastic'
  simp at hstochastic'

/-- Helper for Exercise 19.5.4: kernel irreducibility of the crossed-ladder walk yields the
source-facing irreducibility predicate for the realized chain. -/
private theorem crossedLadderIrreducibleMarkovChain :
    IsIrreducibleMarkovChain P X := by
  have hgreen :
      ∀ ⦃x y : SimpleLadderVertex⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure SimpleLadderVertex) ({y} : Set SimpleLadderVertex) := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure SimpleLadderVertex)
        (discreteMatrixKernel p)).irreducible
        (A := ({y} : Set SimpleLadderVertex)) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set SimpleLadderVertex) = 0 := by
        change (Kernel.id x) ({y} : Set SimpleLadderVertex) = 0
        simp [Kernel.id_apply, hxy]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    -- Proof comment: irreducibility gives a positive finite-step singleton mass, which is exactly
    -- the input needed for the positive-time Green-function bridge.
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hnpos hn
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen

/-- Helper for Exercise 19.5.4: in a finite irreducible random walk with weights, the normalized
conductance measure gives an invariant distribution, so the chain is recurrent. -/
private theorem recurrentMarkovChainOfFiniteIrreducibleRandomWalk
    (x0 : SimpleLadderVertex) :
    IsRecurrentMarkovChain P X := by
  let hWalk : IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph) := inferInstance
  let hirr : IsIrreducibleMarkovChain P X :=
    crossedLadderIrreducibleMarkovChain (p := p) (P := P) (X := X)
  have hmass_ne_zero :
      conductanceMeasure (simpleGraphWeights crossedLadderGraph) Set.univ ≠ 0 := by
    intro hmass_zero
    have hvertex_zero :
        conductanceMeasure (simpleGraphWeights crossedLadderGraph) ({x0} : Set SimpleLadderVertex) = 0 := by
      simpa [hmass_zero] using
        (measure_mono_null (show ({x0} : Set SimpleLadderVertex) ⊆ Set.univ by simp) hmass_zero)
    have hcond_zero : conductance (simpleGraphWeights crossedLadderGraph) x0 = 0 := by
      simpa [conductanceMeasure_apply_singleton] using hvertex_zero
    exact crossedLadderConductance_ne_zero_at (p := p) x0 hcond_zero
  have hmass_lt_top :
      conductanceMeasure (simpleGraphWeights crossedLadderGraph) Set.univ < ∞ := by
    rw [conductanceMeasure]
    rw [Measure.sum_apply _ MeasurableSet.univ]
    rw [tsum_fintype]
    have hterm :
        ∀ x : SimpleLadderVertex,
          (conductance (simpleGraphWeights crossedLadderGraph) x • Measure.dirac x) Set.univ =
            conductance (simpleGraphWeights crossedLadderGraph) x := by
      intro x
      simp [Measure.smul_apply]
    simp_rw [hterm]
    simp only [ENNReal.sum_lt_top, Finset.mem_univ, forall_true_left]
    intro x
    exact hWalk.conductance_lt_top x
  let πMeasure : Measure SimpleLadderVertex :=
    (conductanceMeasure (simpleGraphWeights crossedLadderGraph) Set.univ)⁻¹ •
      conductanceMeasure (simpleGraphWeights crossedLadderGraph)
  have hπ_prob : IsProbabilityMeasure πMeasure := by
    refine isProbabilityMeasure_iff.2 ?_
    rw [Measure.smul_apply]
    exact ENNReal.inv_mul_cancel hmass_ne_zero (ne_of_lt hmass_lt_top)
  let π : ProbabilityMeasure SimpleLadderVertex := ⟨πMeasure, hπ_prob⟩
  have hμ_inv_conductance :
      Kernel.Invariant
        (discreteMatrixKernel
          (conductanceTransitionMatrix (simpleGraphWeights crossedLadderGraph)))
        (conductanceMeasure (simpleGraphWeights crossedLadderGraph)) := by
    letI :
        IsMarkovKernel
          (discreteMatrixKernel
            (conductanceTransitionMatrix (simpleGraphWeights crossedLadderGraph))) :=
      discreteMatrixKernel_isMarkovKernel _
        (conductanceTransitionMatrix_isStochastic
          (C := simpleGraphWeights crossedLadderGraph)
          (fun x ↦ hWalk.conductance_lt_top x)
          (fun x ↦ bot_lt_iff_ne_bot.mpr <| crossedLadderConductance_ne_zero_at (p := p) x))
    -- Proof comment: reversibility of the conductance kernel supplies the invariant measure.
    exact
      (conductanceKernel_isReversible
        (C := simpleGraphWeights crossedLadderGraph)
        hWalk.symmetric
        (fun x ↦ hWalk.conductance_lt_top x)
        (fun x ↦ bot_lt_iff_ne_bot.mpr <| crossedLadderConductance_ne_zero_at (p := p) x)).invariant
  have hp_eq : p = conductanceTransitionMatrix (simpleGraphWeights crossedLadderGraph) := by
    funext x y
    exact hWalk.transition_eq x y
  have hμ_inv :
      Kernel.Invariant (discreteMatrixKernel p)
        (conductanceMeasure (simpleGraphWeights crossedLadderGraph)) := by
    simpa [hp_eq] using hμ_inv_conductance
  have hπ_inv : Kernel.Invariant (discreteMatrixKernel p) (π : Measure SimpleLadderVertex) := by
    have hscaled :
        Kernel.Invariant
          (discreteMatrixKernel p)
          ((conductanceMeasure (simpleGraphWeights crossedLadderGraph) Set.univ)⁻¹ •
            conductanceMeasure (simpleGraphWeights crossedLadderGraph)) :=
      kernelInvariant_smul
        (κ := fun _ : ℕ ↦ discreteMatrixKernel p)
        (a := (conductanceMeasure (simpleGraphWeights crossedLadderGraph) Set.univ)⁻¹) hμ_inv
    simpa [π, πMeasure] using hscaled
  have hπ_mem : π ∈ invariantDistributions (discreteMatrixKernel p) := by
    exact (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπ_inv
  have hpositive : IsPositiveRecurrentMarkovChain P X := by
    refine
      (isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
        (p := p) (P := P) (X := X) hirr).2 ?_
    intro hEmpty
    have : π ∈ (∅ : Set (ProbabilityMeasure SimpleLadderVertex)) := by
      simpa [hEmpty] using hπ_mem
    simpa using this
  -- Proof comment: positive recurrence upgrades every state of the finite irreducible chain to
  -- recurrence.
  intro x
  exact recurrentState_of_positiveRecurrentState
    (p := p) (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X)
    (x := x) (hpositive x)

/-- Helper for Exercise 19.5.4: away from `{a, z}`, the time-`1` boundary-hit event landing at
`z` matches the local first-hit owner `F_A`. -/
private theorem crossedLadderBoundaryHitDistribution_eq_F_A_of_not_mem_boundary
    {x : SimpleLadderVertex} (hx : x ∉ simpleLadderBoundary) :
    ((P x : Measure Ω)
      {ω | hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ}).toReal =
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) x simpleLadderZ := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hEventAE :
      {ω | hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ} =ᵐ[μ]
        firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
      initialState_ae_eq_start (p := p) (P := P) (X := X) x
    filter_upwards [hstart] with ω hω
    have hx0 : X 0 ω ∉ simpleLadderBoundary := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X simpleLadderBoundary 0 ω = hittingAfter X simpleLadderBoundary 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial
        (p := p) (X := X) (A := simpleLadderBoundary) (ω := ω) hx0
    have hboundary :
        simpleLadderBoundary =
          insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex) := by
      ext ξ
      simp [simpleLadderBoundary, Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
    have hτeq' :
        hittingAfter X
            (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0 ω =
          hittingAfter X
            (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1 ω := by
      simpa [hboundary] using hτeq
    have hleft :
        {ω | hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ} ω ↔
          {ω | hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1 ω < ⊤ ∧
              stoppedValue X
                  (hittingAfter X
                    (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1) ω =
                simpleLadderZ} ω := by
      simpa [hboundary]
    have hright :
        {ω | hittingAfter X
              (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1 ω < ⊤ ∧
            stoppedValue X
                (hittingAfter X
                  (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1) ω =
              simpleLadderZ} ω ↔
          {ω | hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0 ω < ⊤ ∧
              stoppedValue X
                (hittingAfter X
                  (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0) ω =
                simpleLadderZ} ω := by
      have hstopEq :
          stoppedValue X
              (hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0) ω =
            stoppedValue X
              (hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 1) ω := by
        rw [stoppedValue, hτeq']
        rfl
      constructor
      · intro h
        rcases h with ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.trans hstop
      · intro h
        rcases h with ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.symm.trans hstop
    -- Proof comment: away from the boundary, the descriptions starting at times `0` and `1`
    -- coincide, so the stopped boundary-hit event is exactly the owner event defining `F_A`.
    exact propext (hleft.trans hright)
  rw [measure_congr hEventAE]
  simp [F_A, Measure.real_def, μ]

/-- Helper for Exercise 19.5.4: starting away from `{a, z}`, the crossed-ladder walk hits that
boundary almost surely. -/
private theorem crossedLadderBoundaryHit_prob_eq_one_of_not_mem_boundary
    {x : SimpleLadderVertex} (hx : x ∉ simpleLadderBoundary) :
    (P x : Measure Ω) {ω | hittingAfter X simpleLadderBoundary 1 ω < ⊤} = 1 := by
  let hirr : IsIrreducibleMarkovChain P X := crossedLadderIrreducibleMarkovChain
    (p := p) (P := P) (X := X)
  let hrec : IsRecurrentMarkovChain P X :=
    recurrentMarkovChainOfFiniteIrreducibleRandomWalk
      (p := p) (P := P) (X := X) x
  let Ezero : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = simpleLadderA}
  let H : Set Ω := {ω | hittingAfter X simpleLadderBoundary 1 ω < ⊤}
  have hzeroHit : (F[P, X]) x simpleLadderA = 1 := by
    exact
      everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := P) (X := X)
        (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (x := x) (y := simpleLadderA) (hrec x) (hirr x simpleLadderA)
  have hEzero_le_one : (P x : Measure Ω) Ezero ≤ 1 := by
    calc
      (P x : Measure Ω) Ezero ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hEzero : (P x : Measure Ω) Ezero = 1 := by
    exact
      (ENNReal.toReal_eq_one_iff ((P x : Measure Ω) Ezero)).mp <|
        by simpa [Ezero, everHitsProbability_def, Measure.real_def] using hzeroHit
  have hsubset : Ezero ⊆ H := by
    intro ω hω
    rcases hω with ⟨n, hn, hXn⟩
    have hmem : X n ω ∈ simpleLadderBoundary := by
      simp [simpleLadderBoundary, Set.mem_insert_iff, Set.mem_singleton_iff, hXn]
    exact lt_of_le_of_lt
      (hittingAfter_le_of_mem (u := X) (s := simpleLadderBoundary) (n := 1)
        (ω := ω) hn hmem)
      (by simp)
  have hH_le_one : (P x : Measure Ω) H ≤ 1 := by
    calc
      (P x : Measure Ω) H ≤ (P x : Measure Ω) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hH_ge_one : 1 ≤ (P x : Measure Ω) H := by
    calc
      1 = (P x : Measure Ω) Ezero := hEzero.symm
      _ ≤ (P x : Measure Ω) H := measure_mono hsubset
  -- Proof comment: recurrence gives almost-sure positive-time return to the specific boundary
  -- vertex `a`, and that event is contained in the first-hit event for the full boundary.
  exact le_antisymm hH_le_one hH_ge_one

/-- Helper for Exercise 19.5.4: on the boundary `{a, z}`, the local first-hit owner already
matches the boundary datum `0/1`. -/
private theorem crossedLadderFA_eq_boundaryDatum_on_boundary {x : SimpleLadderVertex}
    (hx : x ∈ simpleLadderBoundary) :
    F_A P X ({simpleLadderA} : Set SimpleLadderVertex) x simpleLadderZ =
      if x = simpleLadderZ then (1 : ℝ) else 0 := by
  by_cases hZ : x = simpleLadderZ
  · subst hZ
    let μ : Measure Ω := (P simpleLadderZ : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = simpleLadderZ}
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one (p := p) (P := P) (X := X) simpleLadderZ
    have hSubset :
        S ⊆ firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ := by
      intro ω hω
      have hτ0 :
          hittingAfter X
              (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0 ω = 0 := by
        refine le_antisymm ?_
          (le_hittingAfter (u := X)
            (s := insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) (n := 0) ω)
        have hmem :
            X 0 ω ∈ insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex) := by
          have hωz : X 0 ω = simpleLadderZ := by simpa [S] using hω
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hωz]
        exact hittingAfter_le_of_mem
          (u := X) (s := insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex))
          (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X
              (hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0) ω =
            X 0 ω := by
        simp [stoppedValue, hτ0]
      constructor
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0]
      · simpa [firstHitAtStateEvent, Set.mem_insert_iff, Set.mem_singleton_iff, hτ0] using
          hstop.trans hω
    have hEvent :
        μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ) = 1 := by
      refine le_antisymm ?_ ?_
      · calc
          μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ)
            ≤ μ Set.univ := by
                exact measure_mono (by intro ω hω; simp)
          _ = 1 := by simp [μ]
      · calc
          1 = μ S := hStart.symm
          _ ≤ μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ) :=
              measure_mono hSubset
    have hEventReal :
        (μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ)).toReal =
          1 := by
      rw [hEvent]
      norm_num
    -- Proof comment: starting at `z` forces the first boundary hit to occur at `z` immediately.
    simpa [F_A, Measure.real_def, μ] using hEventReal
  · have hA : x = simpleLadderA := by
      rcases (by
          simpa [simpleLadderBoundary, Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
        hA | hZ'
      · exact hA
      · exact False.elim (hZ hZ')
    subst hA
    have hAZ : simpleLadderA ≠ simpleLadderZ := hZ
    let μ : Measure Ω := (P simpleLadderA : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = simpleLadderA}
    have hSubset :
        firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ ⊆ Sᶜ := by
      intro ω hω
      simp only [Set.mem_compl_iff, S]
      intro hSω
      have hτ0 :
          hittingAfter X
              (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0 ω = 0 := by
        refine le_antisymm ?_
          (le_hittingAfter (u := X)
            (s := insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) (n := 0) ω)
        have hmem :
            X 0 ω ∈ insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex) := by
          have hA0 : X 0 ω = simpleLadderA := by simpa [S] using hSω
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hA0]
        exact hittingAfter_le_of_mem
          (u := X) (s := insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex))
          (n := 0) (ω := ω) (by simp) hmem
      have hstopA :
          stoppedValue X
              (hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0) ω =
            simpleLadderA := by
        calc
          stoppedValue X
              (hittingAfter X
                (insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)) 0) ω
              = X 0 ω := by simp [stoppedValue, hτ0]
          _ = simpleLadderA := hSω
      have : simpleLadderA = simpleLadderZ := hstopA.symm.trans hω.2
      exact hAZ this
    have hStart : μ S = 1 := by
      simpa [μ, S] using initialState_prob_eq_one (p := p) (P := P) (X := X) simpleLadderA
    have hSComplZero : μ Sᶜ = 0 := by
      let hReal :
          IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
      rw [measure_compl (by
        rw [show S = X 0 ⁻¹' ({simpleLadderA} : Set SimpleLadderVertex) by
          ext ω
          simp [S]]
        exact hReal.measurable_process 0 (MeasurableSet.singleton simpleLadderA))
        (by rw [hStart]; simp), hStart]
      norm_num
    have hEventZero :
        μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ) = 0 := by
      exact measure_mono_null hSubset hSComplZero
    have hEventReal :
        (μ (firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ)).toReal =
          0 := by
      rw [hEventZero]
      simp
    -- Proof comment: on the almost-sure start-at-`a` event, the time-`0` boundary hit is `a`,
    -- so the first-hit event at `z` has probability zero.
    simpa [F_A, Measure.real_def, μ, hZ] using hEventReal

/-- Helper for Exercise 19.5.4: away from the boundary `{a, z}`, the local first-hit owner
toward `z` agrees with the explicit crossed-ladder voltage. -/
private theorem crossedLadderVoltage_eq_F_A_of_not_mem_boundary {x : SimpleLadderVertex}
    (hx : x ∉ simpleLadderBoundary) :
    crossedLadderVoltage x = F_A P X ({simpleLadderA} : Set SimpleLadderVertex) x simpleLadderZ := by
  let A : Set SimpleLadderVertex := simpleLadderBoundary
  let B : Set Ω :=
    {ω | hittingAfter X A 1 ω < ⊤ ∧
        stoppedValue X (hittingAfter X A 1) ω = simpleLadderZ}
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hτ : μ {ω | hittingAfter X A 1 ω < ⊤} = 1 := by
    -- Proof comment: the recurrence bridge already shows that every interior start hits the
    -- boundary `{a, z}` almost surely.
    simpa [A, μ] using
      crossedLadderBoundaryHit_prob_eq_one_of_not_mem_boundary
        (p := p) (P := P) (X := X) hx
  let hX_adapted : Adapted (processFiltration X) X :=
    adapted_processFiltration_of_measurable (p := p) (X := X) hReal.measurable_process
  have hτ_stop : IsStoppingTime (processFiltration X) (hittingAfter X A 1) := by
    simpa [A] using
      Adapted.isStoppingTime_hittingAfter
        (u := X) (s := A) (n := 1) hX_adapted MeasurableSet.of_discrete
  have hHitMeas : MeasurableSet {ω | hittingAfter X A 1 ω < ⊤} :=
    hittingAfter_one_lt_top_measurableSet (p := p) (X := X) hReal.measurable_process A
  have hB_eq :
      B = ⋃ n : ℕ, {ω | hittingAfter X A 1 ω = n.succ} ∩ {ω | X n.succ ω = simpleLadderZ} := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω.1
      lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
          le_hittingAfter (u := X) (s := A) (n := 1) ω
        have hm_ge_one : 1 ≤ m := by
          have hge_m : (1 : ℕ∞) ≤ (m : ℕ∞) := by
            exact le_of_le_of_eq hm_pos_top hm.symm
          exact_mod_cast hge_m
        exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm_ge_one)) hm_zero
      rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
      have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
        rw [← hm, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hstop :
          stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
        rw [stoppedValue, hτ_idx]
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      constructor
      · exact hm.symm
      · simpa [B, hstop] using hω.2
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hωn⟩
      rcases hωn with ⟨hτn, hXn⟩
      have hτ' : hittingAfter X A 1 ω = n.succ := by
        simpa using hτn
      have hlt : hittingAfter X A 1 ω < ⊤ := by
        simpa [hτ']
      have hτ_idx : (hittingAfter X A 1 ω).untopA = n.succ := by
        rw [hτ', WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hstop :
          stoppedValue X (hittingAfter X A 1) ω = X n.succ ω := by
        rw [stoppedValue, hτ_idx]
      constructor
      · exact hlt
      · simpa [B, hstop] using hXn
  have hBMeas : MeasurableSet B := by
    rw [hB_eq]
    refine MeasurableSet.iUnion fun n ↦ ?_
    have hτn_meas :
        MeasurableSet[processFiltration X n.succ] {ω | hittingAfter X A 1 ω = n.succ} :=
      hτ_stop.measurableSet_eq n.succ
    have hXn_meas :
        MeasurableSet[processFiltration X n.succ] {ω | X n.succ ω = simpleLadderZ} := by
      simpa [Set.preimage] using hX_adapted n.succ (MeasurableSet.singleton simpleLadderZ)
    exact
      (show processFiltration X n.succ ≤ ‹MeasurableSpace Ω› from inf_le_left) _
        (hτn_meas.inter hXn_meas)
  have hHitAE : ∀ᵐ ω ∂μ, hittingAfter X A 1 ω < ⊤ := (mem_ae_iff_prob_eq_one hHitMeas).2 hτ
  have hValueAE :
      (fun ω ↦ crossedLadderVoltage (stoppedValue X (hittingAfter X A 1) ω)) =ᵐ[μ]
        Set.indicator B (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hHitAE] with ω hω
    have hmem :
        stoppedValue X (hittingAfter X A 1) ω ∈ A := by
      simpa [A] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hω.ne
    have hboundaryValue :
        crossedLadderVoltage (stoppedValue X (hittingAfter X A 1) ω) =
          if stoppedValue X (hittingAfter X A 1) ω = simpleLadderZ then (1 : ℝ) else 0 := by
      have hmem' :
          stoppedValue X (hittingAfter X A 1) ω ∈
            ({simpleLadderA, simpleLadderZ} : Set SimpleLadderVertex) := by
        simpa [A, simpleLadderBoundary] using hmem
      exact crossedLadderVoltage_eqOn_boundary hmem'
    by_cases hone : stoppedValue X (hittingAfter X A 1) ω = simpleLadderZ
    · have honeValue :
          crossedLadderVoltage (stoppedValue X (hittingAfter X A 1) ω) = 1 := by
        simpa [hone] using hboundaryValue
      simpa [B, hω, hone] using honeValue
    · have hnotOneValue :
          crossedLadderVoltage (stoppedValue X (hittingAfter X A 1) ω) = 0 := by
        simpa [hone] using hboundaryValue
      simpa [B, hω, hone] using hnotOneValue
  -- Proof comment: Corollary 19.16 turns the electrical potential into a stopped boundary value,
  -- then the stopped boundary value is rewritten as the indicator of landing at `z`.
  calc
    crossedLadderVoltage x =
        ∫ ω, crossedLadderVoltage (stoppedValue X (hittingAfter X A 1) ω) ∂μ := by
          have hu :
              IsElectricalPotential (simpleGraphWeights crossedLadderGraph) A crossedLadderVoltage := by
            simpa [A, simpleLadderBoundary] using crossedLadderVoltage_isElectricalPotential
          simpa [A, μ] using
            electricalPotential_eq_expectation_at_firstEntrance
              (P := P) (X := X) (p := p) (C := simpleGraphWeights crossedLadderGraph)
              (A := A) (u := crossedLadderVoltage) (x := x) hu hx hτ
    _ = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) ω ∂μ := by
          exact integral_congr_ae hValueAE
    _ = (μ B).toReal := by
          simpa [B, μ, Measure.real_def] using integral_indicator_one (μ := μ) (s := B) hBMeas
    _ = F_A P X ({simpleLadderA} : Set SimpleLadderVertex) x simpleLadderZ := by
          simpa [A, B, μ] using
            crossedLadderBoundaryHitDistribution_eq_F_A_of_not_mem_boundary
              (p := p) (P := P) (X := X) hx

/-- Helper for Exercise 19.5.4: the shifted future path hits `z` before `a` if some coordinate
reaches `z` while all earlier coordinates avoid `a`. -/
private def crossedLadderHitZBeforeAPathEvent : Set (ℕ → SimpleLadderVertex) :=
  {ξ | ∃ n : ℕ, ξ n = simpleLadderZ ∧ ∀ m : ℕ, m ≤ n → ξ m ≠ simpleLadderA}

/-- Helper for Exercise 19.5.4: the discrete-time future path after `k` steps. -/
private def crossedLadderFuturePath
    (Y : ℕ → Ω → SimpleLadderVertex) (k : ℕ) : Ω → ℕ → SimpleLadderVertex :=
  fun ω n ↦ Y (n + k) ω

/-- Helper for Exercise 19.5.4: the finite history of the crossed-ladder walk up to time `k`. -/
private def crossedLadderPastPath
    (Y : ℕ → Ω → SimpleLadderVertex) (k : ℕ) : Ω → Fin (k + 1) → SimpleLadderVertex :=
  fun ω i ↦ Y i ω

/-- Helper for Exercise 19.5.4: the finite crossed-ladder history map is measurable when the walk
coordinates are measurable. -/
private theorem crossedLadderPastPath_measurable
    {Y : ℕ → Ω → SimpleLadderVertex} (hY_meas : ∀ n, Measurable (Y n)) (k : ℕ) :
    Measurable (crossedLadderPastPath Y k) := by
  -- Proof comment: measurability on the finite product is checked coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [crossedLadderPastPath] using hY_meas i

/-- Helper for Exercise 19.5.4: the shifted crossed-ladder path map is measurable when the walk
coordinates are measurable. -/
private theorem crossedLadderFuturePath_measurable
    {Y : ℕ → Ω → SimpleLadderVertex} (hY_meas : ∀ n, Measurable (Y n)) (k : ℕ) :
    Measurable (crossedLadderFuturePath Y k) := by
  -- Proof comment: each shifted coordinate is just the measurable slice `Y (n + k)`.
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [crossedLadderFuturePath, add_comm] using hY_meas (n + k)

/-- Helper for Exercise 19.5.4: at time `k`, the generated filtration of the crossed-ladder walk
is the pullback sigma-algebra of the finite history map. -/
private theorem generatedFiltrationSpace_eq_crossedLadderPastPath_comap
    (Y : ℕ → Ω → SimpleLadderVertex) (k : ℕ) :
    generatedFiltrationSpace Y k =
      MeasurableSpace.comap (crossedLadderPastPath Y k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (crossedLadderPastPath Y k) inferInstance ≤
        generatedFiltrationSpace Y k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace Y k] (fun ω ↦ fun i : Fin (k + 1) ↦ Y i ω) := by
      -- Proof comment: every coordinate of the length-`k + 1` history is already measurable at
      -- time `k`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact
        le_iSup_of_le i <|
          le_iSup_of_le (show (i : ℕ) ≤ k from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace Y k ≤
        MeasurableSpace.comap (crossedLadderPastPath Y k) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (crossedLadderPastPath Y k) inferInstance]
          (fun ω ↦ crossedLadderPastPath Y k ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (crossedLadderPastPath Y k))
    simpa [crossedLadderPastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Exercise 19.5.4: finite prefix-avoidance of `a` on path space is measurable. -/
private theorem crossedLadderAvoidBeforePathEvent_measurable :
    ∀ n : ℕ, MeasurableSet {ξ : ℕ → SimpleLadderVertex | ∀ m < n, ξ m ≠ simpleLadderA}
  | 0 => by
      simp
  | n + 1 => by
      have hEq :
          {ξ : ℕ → SimpleLadderVertex | ∀ m < n + 1, ξ m ≠ simpleLadderA} =
            {ξ : ℕ → SimpleLadderVertex | ∀ m < n, ξ m ≠ simpleLadderA} ∩
              {ξ : ℕ → SimpleLadderVertex | ξ n ≠ simpleLadderA} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.lt_succ_of_lt hm)
          · exact hξ n (Nat.lt_succ_self n)
        · intro hξ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact hξ.1 m hm
          · exact hξ.2
      -- Proof comment: the length-`n + 1` avoidance event splits into the shorter prefix
      -- avoidance event together with the singleton constraint at the last coordinate.
      rw [hEq]
      refine (crossedLadderAvoidBeforePathEvent_measurable n).inter ?_
      change MeasurableSet (((fun ξ : ℕ → SimpleLadderVertex ↦ ξ n) ⁻¹' ({simpleLadderA} : Set _))ᶜ)
      exact ((measurable_pi_apply n) (MeasurableSet.singleton simpleLadderA)).compl

/-- Helper for Exercise 19.5.4: avoiding `a` through time `n` is a measurable finite-coordinate
path event. -/
private theorem crossedLadderAvoidThroughPathEvent_measurable
    (n : ℕ) :
    MeasurableSet {ξ : ℕ → SimpleLadderVertex | ∀ m ≤ n, ξ m ≠ simpleLadderA} := by
  have hEq :
      {ξ : ℕ → SimpleLadderVertex | ∀ m ≤ n, ξ m ≠ simpleLadderA} =
        {ξ : ℕ → SimpleLadderVertex | ∀ m < n + 1, ξ m ≠ simpleLadderA} := by
    ext ξ
    simp
  -- Proof comment: "through time `n`" is the same finite prefix condition as "before time
  -- `n + 1`", so the recursive measurability lemma applies directly.
  rw [hEq]
  exact crossedLadderAvoidBeforePathEvent_measurable (p := p) (n + 1)

/-- Helper for Exercise 19.5.4: the finite cylinder where the shifted path first witnesses the
`z`-before-`a` pattern at time `n`. -/
private def crossedLadderHitZBeforeAPathCylinder (n : ℕ) : Set (ℕ → SimpleLadderVertex) :=
  {ξ | ξ n = simpleLadderZ ∧ ∀ m ≤ n, ξ m ≠ simpleLadderA}

/-- Helper for Exercise 19.5.4: each finite `z`-before-`a` cylinder is measurable on path space.
-/
private theorem crossedLadderHitZBeforeAPathCylinder_measurable
    (n : ℕ) :
    MeasurableSet (crossedLadderHitZBeforeAPathCylinder n) := by
  -- Proof comment: this cylinder is the intersection of the singleton constraint at time `n`
  -- with the finite prefix-avoidance event through time `n`.
  exact
    ((measurable_pi_apply n) (MeasurableSet.singleton simpleLadderZ)).inter
      (crossedLadderAvoidThroughPathEvent_measurable (p := p) n)

/-- Helper for Exercise 19.5.4: the full shifted path event is the union of its finite cylinders.
-/
private theorem crossedLadderHitZBeforeAPathEvent_eq_iUnion_cylinders :
    crossedLadderHitZBeforeAPathEvent = ⋃ n : ℕ, crossedLadderHitZBeforeAPathCylinder n := by
  -- Proof comment: a path hits `z` before `a` exactly when some first witnessing time `n`
  -- satisfies the finite cylinder conditions.
  ext ξ
  constructor
  · rintro ⟨n, hnz, havoid⟩
    exact Set.mem_iUnion.2 ⟨n, ⟨hnz, havoid⟩⟩
  · intro hξ
    rcases Set.mem_iUnion.1 hξ with ⟨n, hn⟩
    exact ⟨n, hn.1, hn.2⟩

/-- Helper for Exercise 19.5.4: the shifted future-path event "hit `z` before `a`" is measurable
on path space. -/
private theorem crossedLadderHitZBeforeAPathEvent_measurable :
    MeasurableSet crossedLadderHitZBeforeAPathEvent := by
  -- Proof comment: the path event is the countable union of finite-coordinate cylinders indexed
  -- by the first time that the shifted path reaches `z`.
  rw [crossedLadderHitZBeforeAPathEvent_eq_iUnion_cylinders (p := p)]
  refine MeasurableSet.iUnion ?_
  exact crossedLadderHitZBeforeAPathCylinder_measurable (p := p)

/-- Helper for Exercise 19.5.4: from time `k`, first hitting `{a,z}` at `z` is equivalent to
reaching `z` at some time `n ≥ k` while avoiding `a` throughout that interval. -/
private theorem crossedLadderBoundaryHitAtZ_fromTime_iff_exists
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → SimpleLadderVertex)
    (k : ℕ) (ω : Ω') :
    (hittingAfter u simpleLadderBoundary k ω < ⊤ ∧
        stoppedValue u (hittingAfter u simpleLadderBoundary k) ω = simpleLadderZ) ↔
      ∃ n : ℕ, k ≤ n ∧ u n ω = simpleLadderZ ∧
        ∀ m : ℕ, k ≤ m → m ≤ n → u m ω ≠ simpleLadderA := by
  let s : Set SimpleLadderVertex :=
    insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex)
  have hAZ : simpleLadderA ≠ simpleLadderZ := by
    decide
  have hs : simpleLadderBoundary = s := by
    ext x
    simp [s, simpleLadderBoundary, Set.mem_insert_iff, Set.mem_singleton_iff,
      or_left_comm, or_comm]
  -- Proof comment: this is the same first-hit pathwise bridge as in Exercise 19.5.3, specialized
  -- to the crossed-ladder boundary `{a, z}`.
  have hMain :
      (hittingAfter u s k ω < ⊤ ∧
          stoppedValue u (hittingAfter u s k) ω = simpleLadderZ) ↔
        ∃ n : ℕ, k ≤ n ∧ u n ω = simpleLadderZ ∧
          ∀ m : ℕ, k ≤ m → m ≤ n → u m ω ≠ simpleLadderA := by
    constructor
    · rintro ⟨hfin, hstop⟩
      have hne_top : hittingAfter u s k ω ≠ ⊤ := ne_of_lt hfin
      lift hittingAfter u s k ω to ℕ using hne_top with n hn
      have hidx : (hittingAfter u s k ω).untopA = n := by
        rw [← hn, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hk : k ≤ n := by
        have hk' := le_hittingAfter (u := u) (s := s) (n := k) ω
        rw [← hn] at hk'
        exact_mod_cast hk'
      have hz : u n ω = simpleLadderZ := by
        change stoppedValue u (hittingAfter u s k) ω = simpleLadderZ at hstop
        rw [stoppedValue, hidx] at hstop
        exact hstop
      refine ⟨n, hk, hz, ?_⟩
      intro m hkm hmn hmA
      have hτ_le_m :
          hittingAfter u s k ω ≤ m :=
        hittingAfter_le_of_mem (u := u) (s := s) (n := k) (i := m) (ω := ω) hkm <| by
          simp [s, hmA]
      have hn_le_m : n ≤ m := by
        rw [← hn] at hτ_le_m
        simpa using hτ_le_m
      have hm_eq : m = n := le_antisymm hmn hn_le_m
      have : simpleLadderA = simpleLadderZ := by
        exact ((hm_eq ▸ hmA).symm.trans hz)
      exact hAZ this
    · rintro ⟨n, hkn, hnz, havoid⟩
      have hτ_le_n :
          hittingAfter u s k ω ≤ n :=
        hittingAfter_le_of_mem (u := u) (s := s) (n := k) (i := n) (ω := ω) hkn <| by
          simp [s, hnz]
      have hne_top0 :
          hittingAfter u s k ω ≠ ⊤ := by
        intro htop
        simpa [htop] using hτ_le_n
      lift hittingAfter u s k ω to ℕ using hne_top0 with t ht
      have hidx : (hittingAfter u s k ω).untopA = t := by
        rw [← ht, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hkt : k ≤ t := by
        have hkt' := le_hittingAfter (u := u) (s := s) (n := k) ω
        rw [← ht] at hkt'
        exact_mod_cast hkt'
      have htn : t ≤ n := by
        simpa using hτ_le_n
      have hne_top : hittingAfter u s k ω ≠ ⊤ := by
        intro htop
        simpa [htop] using ht
      have ht_mem : u t ω ∈ s := by
        simpa [hidx] using
          hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := k) (ω := ω) hne_top
      have ht_not_a : u t ω ≠ simpleLadderA :=
        havoid t hkt htn
      have htz : u t ω = simpleLadderZ := by
        rcases (by simpa [s, Set.mem_insert_iff, Set.mem_singleton_iff] using ht_mem) with
          htz | hta
        · exact htz
        · exact False.elim (ht_not_a hta)
      have hltop : hittingAfter u s k ω < ⊤ := by
        exact lt_of_le_of_ne le_top hne_top
      refine ⟨by simpa [ht] using hltop, ?_⟩
      -- Proof comment: the finite hit cannot land at `a`, so the stopped value is forced to be
      -- the other boundary point `z`.
      change stoppedValue u (hittingAfter u s k) ω = simpleLadderZ
      rw [stoppedValue, hidx]
      exact htz
  simpa [hs] using hMain

/-- Helper for Exercise 19.5.4: on the time-`1` shifted future path, hitting `z` before `a` is
exactly the positive-time boundary-hit event landing at `z`. -/
private theorem futurePath_mem_crossedLadderHitZBeforeAPathEvent_iff {ω : Ω} :
    crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent ↔
      hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
        stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ := by
  have hshift :
      crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent ↔
        ∃ n : ℕ, 1 ≤ n ∧ X n ω = simpleLadderZ ∧
          ∀ m : ℕ, 1 ≤ m → m ≤ n → X m ω ≠ simpleLadderA := by
    constructor
    · rintro ⟨j, hjz, hjavoid⟩
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · simpa [crossedLadderFuturePath] using hjz
      · intro m hm1 hmn
        have hm_pos : 0 < m := lt_of_lt_of_le (by omega) hm1
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
        have hrj : r ≤ j := by omega
        simpa [crossedLadderFuturePath] using hjavoid r hrj
    · rintro ⟨n, hn1, hnz, havoid⟩
      have hn_pos : 0 < n := lt_of_lt_of_le (by omega) hn1
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
      refine ⟨j, ?_, ?_⟩
      · simpa [crossedLadderFuturePath] using hnz
      · intro m hmj
        have hm1 : 1 ≤ m + 1 := by omega
        have hmn : m + 1 ≤ j + 1 := by omega
        simpa [crossedLadderFuturePath] using havoid (m + 1) hm1 hmn
  -- Proof comment: rewrite the shifted path event into the time-`1` version of the generic
  -- first-hit description, then invoke the boundary-hit pathwise bridge.
  calc
    crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent
        ↔ ∃ n : ℕ, 1 ≤ n ∧ X n ω = simpleLadderZ ∧
            ∀ m : ℕ, 1 ≤ m → m ≤ n → X m ω ≠ simpleLadderA := hshift
    _ ↔
        hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ := by
            simpa using
              (crossedLadderBoundaryHitAtZ_fromTime_iff_exists
                (p := p) (u := X) (k := 1) (ω := ω)).symm

/-- Helper for Exercise 19.5.4: the path-law kernel attached to the realization `(P, X)`. -/
private def crossedLadderRealizationPathKernel : Kernel SimpleLadderVertex (ℕ → SimpleLadderVertex) :=
  Kernel.ofFunOfCountable fun y ↦
    (P y : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)

/-- Helper for Exercise 19.5.4: each row of the realized path-law kernel is the pushforward of
`P y` along the trajectory map. -/
@[simp] private theorem crossedLadderRealizationPathKernel_apply
    (y : SimpleLadderVertex) :
    crossedLadderRealizationPathKernel (P := P) (X := X) y =
      (P y : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := rfl

/-- Helper for Exercise 19.5.4: the theorem-local realized path kernel starts from the input state
with probability `1` at time `0`. -/
private theorem crossedLadderRealizationPathKernel_initialState_prob_eq_one
    (x : SimpleLadderVertex) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set SimpleLadderVertex)) = 1 := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX0_meas : MeasurableSet (X 0 ⁻¹' ({x} : Set SimpleLadderVertex)) := by
    simpa [Set.preimage] using hReal.measurable_process 0 (measurableSet_singleton x)
  -- Proof comment: convert the already established almost-sure start-state identity into the
  -- preimage form required by the path-kernel future-path interface.
  exact
    (mem_ae_iff_prob_eq_one hX0_meas).1 <|
      by simpa [Set.preimage] using
        initialState_ae_eq_start (p := p) (P := P) (X := X) x

/-- Helper for Exercise 19.5.4: the time-`n` marginal of the path-law kernel is the `n`-step
transition row. -/
private theorem crossedLadderRealizationPathKernel_transition
    (x : SimpleLadderVertex) (n : ℕ) :
    transitionKernel (crossedLadderRealizationPathKernel (P := P) (X := X)) n x =
      (discreteMatrixKernel p ^ n) x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: unfold the explicit path-law kernel and read the time-`n` marginal through
  -- the realization field `transition_eq`.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → SimpleLadderVertex ↦ ξ n)
      ((P x : Measure Ω).map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_pi_lambda _ fun m ↦ hReal.measurable_process m

/-- Helper for Exercise 19.5.4: the path-law kernel makes the realization into a discrete-time
time-homogeneous Markov process on path space. -/
private theorem crossedLadderRealizationPathKernel_isTimeHomogeneousMarkovProcess :
    IsTimeHomogeneousMarkovProcess X P
      (crossedLadderRealizationPathKernel (P := P) (X := X)) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := crossedLadderRealizationPathKernel_initialState_prob_eq_one
        (p := p) (P := P) (X := X)
      path_law := ?_
      markov_property := ?_ }
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the owner transition kernel in the Markov property through the
    -- explicit path-law marginal just established.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [crossedLadderRealizationPathKernel_transition (p := p) (P := P) (X := X)
      (x := X s ω) (n := t)]

/-- Helper for Exercise 19.5.4: the path-event indicator used in the restart step is measurable.
-/
private theorem crossedLadderHitZBeforeAPathIndicator_measurable :
    Measurable
      (Set.indicator crossedLadderHitZBeforeAPathEvent
        (fun _ : ℕ → SimpleLadderVertex ↦ (1 : ℝ))) := by
  -- Proof comment: the indicator is measurable because the path event is already measurable.
  exact
    Measurable.indicator measurable_const
      (crossedLadderHitZBeforeAPathEvent_measurable (p := p))

/-- Helper for Exercise 19.5.4: the restart path-event indicator has bounded range `{0, 1}`. -/
private theorem crossedLadderHitZBeforeAPathIndicator_bounded :
    Bornology.IsBounded
      (Set.range
        (Set.indicator crossedLadderHitZBeforeAPathEvent
          (fun _ : ℕ → SimpleLadderVertex ↦ (1 : ℝ)))) := by
  -- Proof comment: the indicator of a measurable event can only take the two values `0` and `1`.
  simpa using isBounded_range_indicator_one crossedLadderHitZBeforeAPathEvent

/-- Helper for Exercise 19.5.4: evaluating a composed kernel against a restricted pushforward is
the same as integrating the kernel row over the restricted source event. -/
private theorem crossedLadderKernelComp_restrictMap_real_eq_setIntegral
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel SimpleLadderVertex F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → SimpleLadderVertex} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure SimpleLadderVertex := ((μ.restrict B).map Y)
  have hkernel_int :
      Integrable (fun y : SimpleLadderVertex ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : SimpleLadderVertex ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict B).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Exercise 19.5.4: under the path-law kernel started from `y`, the shifted path event
has mass `F_A({a}, y, z)`. -/
private theorem crossedLadderHitZBeforeAPathIntegral_eq_F_A (y : SimpleLadderVertex) :
    ∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
      ∂crossedLadderRealizationPathKernel (P := P) (X := X) y =
        F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y simpleLadderZ := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let path : Ω → ℕ → SimpleLadderVertex := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    -- Proof comment: the realized full-path map is measurable because every coordinate of `X`
    -- is measurable.
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact hReal.measurable_process n
  have hpreimage :
      path ⁻¹' crossedLadderHitZBeforeAPathEvent =
        firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ := by
    ext ω
    have hboundary :
        simpleLadderBoundary =
          insert simpleLadderZ ({simpleLadderA} : Set SimpleLadderVertex) := by
      ext x
      simp [simpleLadderBoundary, Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
    have hiff0 :
        crossedLadderHitZBeforeAPathEvent (path ω) ↔
          ∃ n : ℕ, 0 ≤ n ∧ X n ω = simpleLadderZ ∧
            ∀ m : ℕ, 0 ≤ m → m ≤ n → X m ω ≠ simpleLadderA := by
      constructor
      · rintro ⟨n, hnz, havoid⟩
        exact ⟨n, Nat.zero_le n, hnz, fun m _ hm ↦ havoid m hm⟩
      · rintro ⟨n, _, hnz, havoid⟩
        exact ⟨n, hnz, fun m hm ↦ havoid m (Nat.zero_le m) hm⟩
    -- Proof comment: the full-path event is exactly the time-`0` first-hit event defining
    -- `F_A`, after rewriting the crossed-ladder boundary as `insert z {a}`.
    calc
      crossedLadderHitZBeforeAPathEvent (path ω)
          ↔ ∃ n : ℕ, 0 ≤ n ∧ X n ω = simpleLadderZ ∧
              ∀ m : ℕ, 0 ≤ m → m ≤ n → X m ω ≠ simpleLadderA := hiff0
      _ ↔
          hittingAfter X simpleLadderBoundary 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X simpleLadderBoundary 0) ω = simpleLadderZ := by
              simpa using
                (crossedLadderBoundaryHitAtZ_fromTime_iff_exists
                  (p := p) (u := X) (k := 0) (ω := ω)).symm
      _ ↔ firstHitAtStateEvent X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ ω := by
            rw [firstHitAtStateEvent, hboundary]
            exact Iff.rfl
  calc
    ∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
        ∂crossedLadderRealizationPathKernel (P := P) (X := X) y
        = (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
            crossedLadderHitZBeforeAPathEvent := by
              exact
                MeasureTheory.integral_indicator_one
                  (μ := crossedLadderRealizationPathKernel (P := P) (X := X) y)
                  (s := crossedLadderHitZBeforeAPathEvent)
                  (crossedLadderHitZBeforeAPathEvent_measurable (p := p))
    _ = (((P y : Measure Ω).map path).real crossedLadderHitZBeforeAPathEvent) := by
          rfl
    _ = (P y : Measure Ω).real (path ⁻¹' crossedLadderHitZBeforeAPathEvent) := by
          simpa using
            (MeasureTheory.map_measureReal_apply
              (μ := (P y : Measure Ω)) (f := path) hpath_meas
              (crossedLadderHitZBeforeAPathEvent_measurable (p := p)))
    _ = F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y simpleLadderZ := by
          simpa [F_A, hpreimage]

/-- Helper for Exercise 19.5.4: the realized path-kernel row mass of the event "hit `z` before
`a`" is exactly the continuation value `F_A({a}, y, z)`. -/
private theorem crossedLadderHitZBeforeAPathKernelReal_eq_F_A (y : SimpleLadderVertex) :
    (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
        crossedLadderHitZBeforeAPathEvent =
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y simpleLadderZ := by
  -- Proof comment: rewrite the row mass as the integral of the indicator of the path event, then
  -- invoke the already identified `F_A` formula for that integral.
  calc
    (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
        crossedLadderHitZBeforeAPathEvent
        =
          ∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
            ∂crossedLadderRealizationPathKernel (P := P) (X := X) y := by
              symm
              exact
                MeasureTheory.integral_indicator_one
                  (μ := crossedLadderRealizationPathKernel (P := P) (X := X) y)
                  (s := crossedLadderHitZBeforeAPathEvent)
                  (crossedLadderHitZBeforeAPathEvent_measurable (p := p))
    _ = F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y simpleLadderZ :=
          crossedLadderHitZBeforeAPathIntegral_eq_F_A (p := p) (P := P) (X := X) y

/-- Helper for Exercise 19.5.4: the escape event from `a` to `z` before returning to `a` is the
shifted path-space event "hit `z` before `a`" integrated as an indicator. -/
private theorem crossedLadderEscape_eq_shiftedPathIndicatorIntegral :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      ENNReal.ofReal
        (∫ ω, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
          (crossedLadderFuturePath X 1 ω) ∂(P simpleLadderA : Measure Ω)) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hEvent :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω ∈ ({simpleLadderZ} : Set SimpleLadderVertex) ∧
          ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ simpleLadderA} =
        (crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnz, havoid⟩
      have hHitZ :
          hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ := by
        -- Proof comment: the explicit positive-time escape event is exactly the time-`1`
        -- boundary-hit event at `z`.
        refine
          (crossedLadderBoundaryHitAtZ_fromTime_iff_exists
            (p := p) (u := X) (k := 1) (ω := ω)).2 ?_
        refine ⟨n, Nat.succ_le_of_lt hn, ?_, ?_⟩
        · simpa [Set.mem_singleton_iff] using hnz
        · intro m hm1 hmn
          exact havoid m (lt_of_lt_of_le (by omega) hm1) hmn
      -- Proof comment: rewrite the boundary-hit event into the shifted future-path owner event.
      exact
        (futurePath_mem_crossedLadderHitZBeforeAPathEvent_iff
          (p := p) (X := X) (ω := ω)).2 hHitZ
    · intro hω
      have hHitZ :
          hittingAfter X simpleLadderBoundary 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X simpleLadderBoundary 1) ω = simpleLadderZ :=
        (futurePath_mem_crossedLadderHitZBeforeAPathEvent_iff
          (p := p) (X := X) (ω := ω)).1 hω
      rcases
          (crossedLadderBoundaryHitAtZ_fromTime_iff_exists
            (p := p) (u := X) (k := 1) (ω := ω)).1 hHitZ with
        ⟨n, hn1, hnz, havoid⟩
      -- Proof comment: converting back from the boundary-hit formulation restores the explicit
      -- positive-time witness required by `escapeToSetProbability_def`.
      refine ⟨n, Nat.succ_le_iff.mp hn1, ?_, ?_⟩
      · simpa [Set.mem_singleton_iff] using hnz
      · intro m hm hmn
        exact havoid m (Nat.succ_le_of_lt hm) hmn
  have hfuture_meas : Measurable (crossedLadderFuturePath X 1) := by
    -- Proof comment: the shifted future path is measurable because the realized process has
    -- measurable coordinates.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa [crossedLadderFuturePath, add_comm] using hReal.measurable_process (n + 1)
  have hEventMeas :
      MeasurableSet ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent) := by
    exact (crossedLadderHitZBeforeAPathEvent_measurable (p := p)).preimage hfuture_meas
  have hIndicatorEq :
      (fun ω ↦
        Set.indicator ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
          (fun _ ↦ (1 : ℝ)) ω) =
        fun ω ↦
          Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
            (crossedLadderFuturePath X 1 ω) := by
    funext ω
    by_cases hω : crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent <;>
      simp [Set.indicator, hω]
  calc
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex)
        = (P simpleLadderA : Measure Ω)
            ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent) := by
              rw [escapeToSetProbability_def, hEvent]
    _ = ENNReal.ofReal
          (((P simpleLadderA : Measure Ω).real
            ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent))) := by
          simp [Measure.real_def]
    _ = ENNReal.ofReal
          (∫ ω, Set.indicator ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
            (fun _ ↦ (1 : ℝ)) ω ∂(P simpleLadderA : Measure Ω)) := by
              congr 1
              symm
              exact
                MeasureTheory.integral_indicator_one
                  (μ := (P simpleLadderA : Measure Ω))
                  (s := (crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
                  hEventMeas
    _ = ENNReal.ofReal
          (∫ ω, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
            (crossedLadderFuturePath X 1 ω) ∂(P simpleLadderA : Measure Ω)) := by
              rw [hIndicatorEq]

/-- Helper for Exercise 19.5.4: the one-step kernel row at `a` is the uniform average over `z`
and the four interior neighbors adjacent to `a`. -/
private theorem crossedLadderKernelIntegral_eq_neighborAverage_at_a
    (g : SimpleLadderVertex → ℝ) :
    ∫ y, g y ∂discreteMatrixKernel p simpleLadderA =
      (g simpleLadderZ + g (⟨2, by decide⟩, ⟨0, by decide⟩) +
          g (⟨2, by decide⟩, ⟨1, by decide⟩) + g (⟨4, by decide⟩, ⟨0, by decide⟩) +
          g (⟨4, by decide⟩, ⟨1, by decide⟩)) / 5 := by
  let leftBottom : SimpleLadderVertex := (⟨2, by decide⟩, ⟨0, by decide⟩)
  let leftTop : SimpleLadderVertex := (⟨2, by decide⟩, ⟨1, by decide⟩)
  let rightBottom : SimpleLadderVertex := (⟨4, by decide⟩, ⟨0, by decide⟩)
  let rightTop : SimpleLadderVertex := (⟨4, by decide⟩, ⟨1, by decide⟩)
  have hp : IsStochasticMatrix p :=
    (inferInstance : IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph)).isStochasticMatrix
  have hrow :
      ∫ y, g y ∂discreteMatrixKernel p simpleLadderA =
        ∑ y : SimpleLadderVertex, (p simpleLadderA y).toReal * g y := by
    have hsum : Summable (fun y : SimpleLadderVertex ↦ (p simpleLadderA y).toReal * ‖g y‖) :=
      Summable.of_finite
    simpa using integral_discreteMatrixKernel_eq_tsum p hp g simpleLadderA hsum
  have hweight :
      ∀ y : SimpleLadderVertex,
        (p simpleLadderA y).toReal =
          if y = simpleLadderZ ∨ y = leftBottom ∨ y = leftTop ∨ y = rightBottom ∨ y = rightTop then
            (1 / 5 : ℝ)
          else 0 := by
    intro y
    rw [(inferInstance : IsRandomWalkWithWeights p (simpleGraphWeights crossedLadderGraph)).transition_eq
      simpleLadderA y, ENNReal.toReal_div]
    rw [crossedLadderConductance_at_a_eq_five]
    rcases y with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [leftBottom, leftTop, rightBottom, rightTop, simpleLadderA, simpleLadderZ,
        crossedLadderGraph, simpleGraphWeights, pathGraph_adj]
  -- Proof comment: convert the kernel integral into the finite row sum, then use the explicit
  -- five-neighbor transition weights from `a`.
  calc
    ∫ y, g y ∂discreteMatrixKernel p simpleLadderA
        = ∑ y : SimpleLadderVertex, (p simpleLadderA y).toReal * g y := hrow
    _ = ∑ y : SimpleLadderVertex,
          (if y = simpleLadderZ ∨ y = leftBottom ∨ y = leftTop ∨ y = rightBottom ∨ y = rightTop then
            (1 / 5 : ℝ)
          else 0) * g y := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hweight y]
    _ = (g simpleLadderZ + g leftBottom + g leftTop + g rightBottom + g rightTop) / 5 := by
          rw [Fintype.sum_prod_type]
          repeat rw [Fin.sum_univ_succ]
          repeat rw [Fin.sum_univ_zero]
          simp [leftBottom, leftTop, rightBottom, rightTop, simpleLadderZ]
          ring

/-- Helper for Exercise 19.5.4: bounded measurable functionals of the crossed-ladder future path
admit the standard deterministic-time Markov conditional-expectation formula. -/
private theorem crossedLadderFuturePathCondExp
    (x : SimpleLadderVertex) (k : ℕ) (g : (ℕ → SimpleLadderVertex) → ℝ)
    (hg_meas : Measurable g) (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (crossedLadderFuturePath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦
        ∫ ξ, g ξ ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X k ω) := by
  let κ : Kernel SimpleLadderVertex (ℕ → SimpleLadderVertex) :=
    crossedLadderRealizationPathKernel (P := P) (X := X)
  let hMarkov : IsTimeHomogeneousMarkovProcess X P κ :=
    crossedLadderRealizationPathKernel_isTimeHomogeneousMarkovProcess
      (p := p) (P := P) (X := X)
  let Iℕ : AddSubmonoid NNReal := {
    carrier := {r | ∃ n : ℕ, ((n : ℕ) : NNReal) = r}
    zero_mem' := by
      exact ⟨0, by simp⟩
    add_mem' := by
      intro a b ha hb
      rcases ha with ⟨m, hm⟩
      rcases hb with ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      simpa [hm, hn] }
  let natTime : ℕ → Iℕ := fun n ↦
    ⟨n, by
      exact ⟨n, rfl⟩⟩
  let natIndex : Iℕ → ℕ := fun s ↦
    Classical.choose (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  let Xnat : Iℕ → Ω → SimpleLadderVertex := fun s ω ↦ X (natIndex s) ω
  let reindexPath : (ℕ → SimpleLadderVertex) → Iℕ → SimpleLadderVertex := fun y s ↦ y (natIndex s)
  let κnat : Kernel SimpleLadderVertex (Iℕ → SimpleLadderVertex) := κ.map reindexPath
  let gnat : (Iℕ → SimpleLadderVertex) → ℝ := fun y ↦ g (fun n ↦ y (natTime n))
  have hnatIndex_spec : ∀ s : Iℕ, ((natIndex s : ℕ) : NNReal) = s.1 := by
    intro s
    exact Classical.choose_spec (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  have hnatIndex_natTime : ∀ n : ℕ, natIndex (natTime n) = n := by
    intro n
    have hcast : (((natIndex (natTime n) : ℕ) : ℕ) : NNReal) = n := by
      simpa [natTime] using hnatIndex_spec (natTime n)
    exact_mod_cast hcast
  have hnatTime_natIndex : ∀ s : Iℕ, natTime (natIndex s) = s := by
    intro s
    apply Subtype.ext
    exact hnatIndex_spec s
  have hnatIndex_add : ∀ s u : Iℕ, natIndex (s + u) = natIndex s + natIndex u := by
    intro s u
    have hcast :
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) =
          ((natIndex s + natIndex u : ℕ) : NNReal) := by
      calc
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) = (s + u).1 := hnatIndex_spec (s + u)
        _ = s.1 + u.1 := rfl
        _ = (((natIndex s : ℕ) : ℕ) : NNReal) + (((natIndex u : ℕ) : ℕ) : NNReal) := by
              rw [hnatIndex_spec s, hnatIndex_spec u]
        _ = ((natIndex s + natIndex u : ℕ) : NNReal) := by simp
    exact_mod_cast hcast
  have hnatTime_le_iff : ∀ {n l : ℕ}, natTime n ≤ natTime l ↔ n ≤ l := by
    intro n l
    change ((n : NNReal) ≤ (l : NNReal)) ↔ n ≤ l
    norm_num
  have hsub : ∀ ⦃s u : Iℕ⦄, s ≤ u → u.1 - s.1 ∈ Iℕ := by
    intro s u hsu
    change ∃ n : ℕ, ((n : ℕ) : NNReal) = u.1 - s.1
    refine ⟨natIndex u - natIndex s, ?_⟩
    have hle : natIndex s ≤ natIndex u := by
      have : natTime (natIndex s) ≤ natTime (natIndex u) := by
        simpa [hnatTime_natIndex] using hsu
      exact hnatTime_le_iff.mp this
    calc
      (((natIndex u - natIndex s : ℕ) : ℕ) : NNReal)
          = ((natIndex u : ℕ) : NNReal) - ((natIndex s : ℕ) : NNReal) := by
              simpa [Nat.cast_sub hle]
      _ = u.1 - s.1 := by rw [hnatIndex_spec u, hnatIndex_spec s]
  have hreindex_meas : Measurable reindexPath := by
    -- Proof comment: the transport from `Iℕ`-indexed paths back to `ℕ`-indexed paths is just
    -- coordinate evaluation at the chosen natural representative of each submonoid time.
    refine measurable_pi_lambda _ fun s ↦ ?_
    exact measurable_pi_apply (natIndex s)
  have hgenerated :
      ∀ n : ℕ, generatedFiltrationSpace Xnat (natTime n) = generatedFiltrationSpace X n := by
    intro n
    rw [generatedFiltrationSpace, generatedFiltrationSpace]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun s hs ↦ ?_
      have hs' : natIndex s ≤ n := by
        have : natTime (natIndex s) ≤ natTime n := by
          simpa [hnatTime_natIndex] using hs
        exact hnatTime_le_iff.mp this
      have hcomap :
          MeasurableSpace.comap (X (natIndex s)) inferInstance ≤ generatedFiltrationSpace X n := by
        exact le_iSup_of_le (natIndex s) <| le_iSup_of_le hs' le_rfl
      simpa [Xnat] using hcomap
    · refine iSup₂_le fun r hr ↦ ?_
      have hr' : natTime r ≤ natTime n := hnatTime_le_iff.mpr hr
      have hcomap :
          MeasurableSpace.comap (Xnat (natTime r)) inferInstance ≤
            generatedFiltrationSpace Xnat (natTime n) := by
        exact le_iSup_of_le (natTime r) <| le_iSup_of_le hr' le_rfl
      simpa [Xnat, hnatIndex_natTime] using hcomap
  have hgenerated' :
      ∀ s : Iℕ, generatedFiltrationSpace Xnat s = generatedFiltrationSpace X (natIndex s) := by
    intro s
    calc
      generatedFiltrationSpace Xnat s
          = generatedFiltrationSpace Xnat (natTime (natIndex s)) := by
              rw [hnatTime_natIndex s]
      _ = generatedFiltrationSpace X (natIndex s) := hgenerated (natIndex s)
  have htransition : ∀ s : Iℕ, transitionKernel κnat s = transitionKernel κ (natIndex s) := by
    intro s
    ext z A hA
    rw [transitionKernel_apply, transitionKernel_apply]
    have hrow : κnat z = (κ z).map reindexPath := by
      simpa [κnat] using Kernel.map_apply κ hreindex_meas z
    rw [hrow]
    rw [Measure.map_map (μ := κ z) (f := reindexPath) (g := fun y : Iℕ → SimpleLadderVertex ↦ y s)
      (measurable_pi_apply s) hreindex_meas]
    rfl
  letI : IsTimeHomogeneousMarkovProcess Xnat P κnat := by
    refine
      { measurable_process := fun s ↦ by simpa [Xnat] using hMarkov.measurable_process (natIndex s)
        initial_state := ?_
        path_law := ?_
        markov_property := ?_ }
    · intro y
      have hzero : natIndex (0 : Iℕ) = 0 := by
        have : (0 : Iℕ) = natTime 0 := by
          apply Subtype.ext
          simp [natTime]
        simpa [this] using hnatIndex_natTime 0
      -- Proof comment: time `0` is preserved by the transport from `ℕ` to `Iℕ`.
      simpa [Xnat, hzero] using hMarkov.initial_state y
    · intro y
      -- Proof comment: the transported path kernel is still the pushforward of `P y` along the
      -- transported trajectory map.
      calc
        κnat y = (κ y).map reindexPath := by
              simpa [κnat] using Kernel.map_apply κ hreindex_meas y
        _ = (((P y : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)).map reindexPath) := by
              rw [hMarkov.path_law y]
        _ = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
              rw [Measure.map_map hreindex_meas]
              · rfl
              · exact measurable_pi_lambda _ fun n ↦ hMarkov.measurable_process n
    · intro y A hA s u
      have hsum : Xnat (u + s) ⁻¹' A = X (natIndex u + natIndex s) ⁻¹' A := by
        ext ω
        simp [Xnat, hnatIndex_add]
      have hright :
          (fun ω ↦ ((transitionKernel κnat u) (Xnat s ω)).real A) =
            fun ω ↦ ((transitionKernel κ (natIndex u)) (X (natIndex s) ω)).real A := by
        funext ω
        rw [htransition u]
      -- Proof comment: after rewriting the transported time arithmetic and filtration, the
      -- Markov property is exactly the original one.
      simpa [hsum, hgenerated' s, hright] using
        (hMarkov.markov_property y hA (natIndex s) (natIndex u))
  have hFuture :
      HasFuturePathConditionalExpectationFormula Xnat P κnat := by
    have hX0nat : ∀ y, (P y : Measure Ω) (Xnat 0 ⁻¹' ({y} : Set SimpleLadderVertex)) = 1 := by
      intro y
      have hzero : natIndex (0 : Iℕ) = 0 := by
        have : (0 : Iℕ) = natTime 0 := by
          apply Subtype.ext
          simp [natTime]
        simpa [this] using hnatIndex_natTime 0
      simpa [Xnat, hzero] using hMarkov.initial_state y
    have hpathnat :
        ∀ y, κnat y = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
      intro y
      calc
        κnat y = (κ y).map reindexPath := by
              simpa [κnat] using Kernel.map_apply κ hreindex_meas y
        _ = (((P y : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)).map reindexPath) := by
              rw [hMarkov.path_law y]
        _ = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
              rw [Measure.map_map hreindex_meas]
              · rfl
              · exact measurable_pi_lambda _ fun n ↦ hMarkov.measurable_process n
    -- Proof comment: the Chapter 17 fixed-kernel theorem now applies on the transported
    -- submonoid-valued time parameter.
    exact
      (isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_fixedPathKernel
        Xnat P κnat
        (fun s ↦ by simpa [Xnat] using hMarkov.measurable_process (natIndex s))
        hX0nat hpathnat hsub).mp inferInstance
  have hgnat_meas : Measurable gnat := by
    -- Proof comment: compose `g` with the measurable reindexing from `Iℕ`-paths back to
    -- `ℕ`-paths.
    refine hg_meas.comp ?_
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact measurable_pi_apply (natTime n)
  have hgnat_bdd : Bornology.IsBounded (Set.range gnat) := by
    -- Proof comment: the transported path functional still takes values inside the original
    -- bounded range of `g`.
    refine hg_bdd.subset ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    exact ⟨fun n ↦ y (natTime n), rfl⟩
  have hk_nonneg : 0 ≤ natTime k := by
    show (0 : NNReal) ≤ ((natTime k : Iℕ) : NNReal)
    exact zero_le _
  have hAE_nat :
      ((P x : Measure Ω)[fun ω ↦ gnat (futurePath Xnat (natTime k) ω) |
          generatedFiltrationSpace Xnat (natTime k)]) =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, gnat y ∂κnat (Xnat (natTime k) ω) := by
    exact hFuture hgnat_meas hgnat_bdd (natTime k) x hk_nonneg
  have hleft :
      (fun ω ↦ gnat (futurePath Xnat (natTime k) ω)) =
        fun ω ↦ g (crossedLadderFuturePath X k ω) := by
    -- Proof comment: after reindexing the transported future path back along `natTime`, one
    -- recovers the local shifted future path `n ↦ X (n + k)`.
    funext ω
    dsimp [gnat]
    have hpath :
        (fun n ↦ futurePath Xnat (natTime k) ω (natTime n)) =
          crossedLadderFuturePath X k ω := by
      funext n
      simp [futurePath, Xnat, natTime, crossedLadderFuturePath, hnatIndex_add,
        hnatIndex_natTime]
    rw [hpath]
  have hright :
      (fun ω ↦ ∫ y, gnat y ∂κnat (Xnat (natTime k) ω)) =
        fun ω ↦ ∫ ξ, g ξ ∂κ (X k ω) := by
    -- Proof comment: the transported path-kernel row is just the original row seen through the
    -- path reindexing `natTime`.
    funext ω
    have hrow : κnat (Xnat (natTime k) ω) = (κ (X k ω)).map reindexPath := by
      rw [show Xnat (natTime k) ω = X k ω by simp [Xnat, hnatIndex_natTime]]
      simpa [κnat] using Kernel.map_apply κ hreindex_meas (X k ω)
    rw [hrow]
    rw [MeasureTheory.integral_map hreindex_meas.aemeasurable hgnat_meas.aestronglyMeasurable]
    congr 1
    funext y
    simp [gnat, reindexPath, hnatIndex_natTime]
  calc
    ((P x : Measure Ω)[fun ω ↦ g (crossedLadderFuturePath X k ω) | generatedFiltrationSpace X k])
        =ᵐ[(P x : Measure Ω)]
          ((P x : Measure Ω)[fun ω ↦ gnat (futurePath Xnat (natTime k) ω) |
            generatedFiltrationSpace Xnat (natTime k)]) := by
              rw [hgenerated k]
              exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hleft.symm)
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, gnat y ∂κnat (Xnat (natTime k) ω) := hAE_nat
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ ξ, g ξ ∂κ (X k ω) := Filter.EventuallyEq.of_eq hright
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦
        ∫ ξ, g ξ ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X k ω) := by
          rfl

/-- Helper for Exercise 19.5.4: the time-`1` conditional expectation of the shifted path-event
indicator is the realized path-kernel mass started from the present state. -/
private theorem crossedLadderFuturePathEvent_setIntegral_eq_rowMass_timeOne
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X 1] B) :
    ∫ ω in B,
      Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
        (crossedLadderFuturePath X 1 ω) ∂(P simpleLadderA : Measure Ω) =
      ∫ ω in B,
        (∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
          ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X 1 ω))
        ∂(P simpleLadderA : Measure Ω) := by
  let μ : Measure Ω := (P simpleLadderA : Measure Ω)
  let g : (ℕ → SimpleLadderVertex) → ℝ :=
    Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
  let futureIndicator : Ω → ℝ := fun ω ↦ g (crossedLadderFuturePath X 1 ω)
  let kernelIndicator : Ω → ℝ := fun ω ↦ ∫ ξ, g ξ ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X 1 ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hgenerated_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_crossedLadderPastPath_comap (p := p) (Y := X) 1]
    exact (crossedLadderPastPath_measurable (p := p) (Y := X) hReal.measurable_process 1).comap_le
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: the shifted future indicator is measurable because both the path event and
    -- the shifted future path are measurable.
    exact
      (crossedLadderHitZBeforeAPathIndicator_measurable (p := p)).comp
        (crossedLadderFuturePath_measurable (p := p) (Y := X) hReal.measurable_process 1)
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the indicator is pointwise bounded by `1`, so it is integrable on the
    -- probability space `(Ω, P a)`.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent
      · simp [futureIndicator, g, hω]
      · simp [futureIndicator, g, hω]
  have hAE :
      (MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator) =ᵐ[μ]
        kernelIndicator := by
    -- Proof comment: this is the theorem-local deterministic-time future-path bridge specialized
    -- to the restart-event indicator.
    simpa [μ, g, futureIndicator, kernelIndicator] using
      crossedLadderFuturePathCondExp (p := p) (P := P) (X := X)
        simpleLadderA 1 g
        (crossedLadderHitZBeforeAPathIndicator_measurable (p := p))
        (crossedLadderHitZBeforeAPathIndicator_bounded (p := p))
  calc
    ∫ ω in B, futureIndicator ω ∂μ
        = ∫ ω in B,
            MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator ω ∂μ := by
            symm
            exact MeasureTheory.setIntegral_condExp hgenerated_le hfuture_int hB
    _ = ∫ ω in B, kernelIndicator ω ∂μ := by
          exact integral_congr_ae hAE.restrict
    _ =
        ∫ ω in B,
          (∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
            ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X 1 ω))
          ∂(P simpleLadderA : Measure Ω) := by
            rfl

/-- Helper for Exercise 19.5.4: the time-`1` conditional expectation of the shifted path-event
indicator is the realized path-kernel mass started from the present state. -/
private theorem crossedLadderFuturePathIndicator_condExp_timeOne :
    ((P simpleLadderA : Measure Ω)[fun ω ↦
        Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
          (crossedLadderFuturePath X 1 ω)
      | generatedFiltrationSpace X 1]) =ᵐ[(P simpleLadderA : Measure Ω)]
        fun ω ↦
          ∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
            ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X 1 ω) := by
  let g : (ℕ → SimpleLadderVertex) → ℝ :=
    Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
  -- Proof comment: this is the deterministic-time future-path formula specialized to the restart
  -- event indicator.
  simpa [g, MeasureTheory.integral_indicator_one, crossedLadderHitZBeforeAPathEvent_measurable]
    using
      crossedLadderFuturePathCondExp (p := p) (P := P) (X := X)
        simpleLadderA 1 g
        (crossedLadderHitZBeforeAPathIndicator_measurable (p := p))
        (crossedLadderHitZBeforeAPathIndicator_bounded (p := p))

/-- Helper for Exercise 19.5.4: the shifted future-path event has real mass equal to the one-step
average of the realized path-kernel row masses. -/
private theorem crossedLadderFuturePathEvent_real_eq_pathKernelAverageTimeOne :
    (P simpleLadderA : Measure Ω).real
        ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent) =
      ∫ y,
        (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
          crossedLadderHitZBeforeAPathEvent
        ∂discreteMatrixKernel p simpleLadderA := by
  let μ : Measure Ω := (P simpleLadderA : Measure Ω)
  let futureIndicator : Ω → ℝ := fun ω ↦
    Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
      (crossedLadderFuturePath X 1 ω)
  let rowMass : SimpleLadderVertex → ℝ := fun y ↦
    (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
      crossedLadderHitZBeforeAPathEvent
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hfuturePath_meas : Measurable (crossedLadderFuturePath X 1) := by
    exact crossedLadderFuturePath_measurable (p := p) (Y := X) hReal.measurable_process 1
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: the shifted-path indicator is measurable because both the path event and the
    -- future-path map are measurable.
    exact
      (crossedLadderHitZBeforeAPathIndicator_measurable (p := p)).comp hfuturePath_meas
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the indicator is bounded by `1`, so it is integrable under the start law.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  have hgenerated_le : generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun j hj ↦ ?_
    exact (hReal.measurable_process j).comap_le
  let condFuture : Ω → ℝ :=
    MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω, condFuture ω ∂μ := by
              symm
              exact integral_condExp hgenerated_le
      _ = ∫ ω,
            (∫ ξ, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ)) ξ
              ∂crossedLadderRealizationPathKernel (P := P) (X := X) (X 1 ω)) ∂μ := by
            -- Proof comment: invoke the time-`1` future-path conditional-expectation bridge.
            exact integral_congr_ae <| by
              simpa [condFuture, μ, futureIndicator] using
                crossedLadderFuturePathIndicator_condExp_timeOne (p := p) (P := P) (X := X)
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            -- Proof comment: each kernel integral is just the corresponding row mass of the path
            -- event.
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simp [rowMass, MeasureTheory.integral_indicator_one,
              crossedLadderHitZBeforeAPathEvent_measurable (p := p)]
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ y, rowMass y ∂discreteMatrixKernel p simpleLadderA := by
    -- Proof comment: push the present-state observable through the one-step marginal law at `a`.
    have hmap :
        ∫ y, rowMass y ∂((P simpleLadderA : Measure Ω).map (X 1)) =
          ∫ ω, rowMass (X 1 ω) ∂μ := by
            simpa [μ] using
              (MeasureTheory.integral_map
                (hReal.measurable_process 1).aemeasurable
                Measurable.of_discrete.aestronglyMeasurable)
    calc
      ∫ ω, rowMass (X 1 ω) ∂μ
          = ∫ y, rowMass y ∂((P simpleLadderA : Measure Ω).map (X 1)) := by
              exact hmap.symm
      _ = ∫ y, rowMass y ∂((discreteMatrixKernel p ^ 1) simpleLadderA) := by
            rw [hReal.transition_eq simpleLadderA 1]
      _ = ∫ y, rowMass y ∂discreteMatrixKernel p simpleLadderA := by
            simp
  calc
    (P simpleLadderA : Measure Ω).real
        ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
        = ∫ ω, futureIndicator ω ∂μ := by
            -- Proof comment: rewrite the real mass of the shifted future-path event as the
            -- integral of its indicator.
            symm
            simpa [μ, futureIndicator] using
              (MeasureTheory.integral_indicator_one
                (μ := μ)
                (s := (crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
                ((crossedLadderHitZBeforeAPathEvent_measurable (p := p)).preimage hfuturePath_meas))
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ y, rowMass y ∂discreteMatrixKernel p simpleLadderA := htransitionIntegral
    _ =
        ∫ y,
          (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
            crossedLadderHitZBeforeAPathEvent
          ∂discreteMatrixKernel p simpleLadderA := by
            rfl

/-- Helper for Exercise 19.5.4: escaping from `a` to `z` before the first positive return to `a`
is the direct first-step average of the continuation values at the five neighbors of `a`. -/
private theorem crossedLadderEscape_eq_neighborAverage_ofFAAtA :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      ENNReal.ofReal
        ((F_A P X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ simpleLadderZ +
            F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
              (⟨2, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
            F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
              (⟨2, by decide⟩, ⟨1, by decide⟩) simpleLadderZ +
            F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
              (⟨4, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
            F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
              (⟨4, by decide⟩, ⟨1, by decide⟩) simpleLadderZ) / 5) := by
  let μ : Measure Ω := (P simpleLadderA : Measure Ω)
  let rowMass : SimpleLadderVertex → ℝ := fun y ↦
    (crossedLadderRealizationPathKernel (P := P) (X := X) y).real
      crossedLadderHitZBeforeAPathEvent
  have hfuturePath_meas : Measurable (crossedLadderFuturePath X 1) := by
    let hReal :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    exact crossedLadderFuturePath_measurable (p := p) (Y := X) hReal.measurable_process 1
  have hIndicatorEq :
      (fun ω ↦
        Set.indicator ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
          (fun _ ↦ (1 : ℝ)) ω) =
        fun ω ↦
          Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
            (crossedLadderFuturePath X 1 ω) := by
    funext ω
    by_cases hω : crossedLadderFuturePath X 1 ω ∈ crossedLadderHitZBeforeAPathEvent <;>
      simp [Set.indicator, hω]
  calc
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex)
        =
          ENNReal.ofReal
            (∫ ω, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
              (crossedLadderFuturePath X 1 ω) ∂μ) := by
                exact
                  crossedLadderEscape_eq_shiftedPathIndicatorIntegral
                    (p := p) (P := P) (X := X)
    _ =
        ENNReal.ofReal
          ((P simpleLadderA : Measure Ω).real
            ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)) := by
          -- Proof comment: convert the shifted-path indicator integral back to the real mass of
          -- the same event.
          congr 1
          symm
          calc
            (P simpleLadderA : Measure Ω).real
                ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
                =
                  ∫ ω,
                    Set.indicator
                      ((crossedLadderFuturePath X 1) ⁻¹' crossedLadderHitZBeforeAPathEvent)
                      (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                        simpa [μ] using
                          (MeasureTheory.integral_indicator_one
                            (μ := μ)
                            (s := (crossedLadderFuturePath X 1) ⁻¹'
                              crossedLadderHitZBeforeAPathEvent)
                            ((crossedLadderHitZBeforeAPathEvent_measurable
                              (p := p)).preimage hfuturePath_meas)).symm
            _ =
                ∫ ω, Set.indicator crossedLadderHitZBeforeAPathEvent (fun _ ↦ (1 : ℝ))
                  (crossedLadderFuturePath X 1 ω) ∂μ := by
                    rw [hIndicatorEq]
    _ = ENNReal.ofReal (∫ y, rowMass y ∂discreteMatrixKernel p simpleLadderA) := by
          rw [crossedLadderFuturePathEvent_real_eq_pathKernelAverageTimeOne (p := p) (P := P)
            (X := X)]
    _ =
        ENNReal.ofReal
          (∫ y, F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y simpleLadderZ
            ∂discreteMatrixKernel p simpleLadderA) := by
              -- Proof comment: identify each path-kernel row mass with the corresponding
              -- continuation value `F_A`.
              congr 1
              refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
              exact crossedLadderHitZBeforeAPathKernelReal_eq_F_A
                (p := p) (P := P) (X := X) y
    _ =
        ENNReal.ofReal
          ((F_A P X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ simpleLadderZ +
              F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                (⟨2, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
              F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                (⟨2, by decide⟩, ⟨1, by decide⟩) simpleLadderZ +
              F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                (⟨4, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
              F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                (⟨4, by decide⟩, ⟨1, by decide⟩) simpleLadderZ) / 5) := by
              -- Proof comment: collapse the one-step kernel integral at `a` to the explicit
              -- average over its five neighbors.
              rw [crossedLadderKernelIntegral_eq_neighborAverage_at_a (p := p)
                (g := fun y ↦ F_A P X ({simpleLadderA} : Set SimpleLadderVertex) y
                  simpleLadderZ)]

/-- Helper for Exercise 19.5.4: once the five continuation values at the neighbors of `a` are
identified with the explicit crossed-ladder voltage values, their average is exactly `3 / 5`. -/
private theorem crossedLadderNeighborAverageFAAtA_eq_threeFifths :
    ENNReal.ofReal
      ((F_A P X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ simpleLadderZ +
          F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
            (⟨2, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
          F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
            (⟨2, by decide⟩, ⟨1, by decide⟩) simpleLadderZ +
          F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
            (⟨4, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
          F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
            (⟨4, by decide⟩, ⟨1, by decide⟩) simpleLadderZ) / 5) =
      (3 / 5 : ℝ≥0∞) := by
  let leftBottom : SimpleLadderVertex := (⟨2, by decide⟩, ⟨0, by decide⟩)
  let leftTop : SimpleLadderVertex := (⟨2, by decide⟩, ⟨1, by decide⟩)
  let rightBottom : SimpleLadderVertex := (⟨4, by decide⟩, ⟨0, by decide⟩)
  let rightTop : SimpleLadderVertex := (⟨4, by decide⟩, ⟨1, by decide⟩)
  have hz :
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ simpleLadderZ = 1 := by
    -- Proof comment: starting from `z`, the first hit of `{a, z}` already occurs at `z`.
    simpa using
      crossedLadderFA_eq_boundaryDatum_on_boundary
        (p := p) (P := P) (X := X) (x := simpleLadderZ)
        (by simp [simpleLadderBoundary])
  have hleftBottom_not_mem : leftBottom ∉ simpleLadderBoundary := by
    simp [leftBottom, simpleLadderBoundary, simpleLadderA, simpleLadderZ]
  have hleftTop_not_mem : leftTop ∉ simpleLadderBoundary := by
    simp [leftTop, simpleLadderBoundary, simpleLadderA, simpleLadderZ]
  have hrightBottom_not_mem : rightBottom ∉ simpleLadderBoundary := by
    simp [rightBottom, simpleLadderBoundary, simpleLadderA, simpleLadderZ]
  have hrightTop_not_mem : rightTop ∉ simpleLadderBoundary := by
    simp [rightTop, simpleLadderBoundary, simpleLadderA, simpleLadderZ]
  have hleftBottom :
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) leftBottom simpleLadderZ = (1 / 2 : ℝ) := by
    -- Proof comment: every interior neighbor of `a` has voltage `1 / 2`, and the voltage owner
    -- already matches the continuation value `F_A`.
    calc
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) leftBottom simpleLadderZ
          = crossedLadderVoltage leftBottom := by
              symm
              exact
                crossedLadderVoltage_eq_F_A_of_not_mem_boundary
                  (p := p) (P := P) (X := X) hleftBottom_not_mem
      _ = (1 / 2 : ℝ) :=
        crossedLadderVoltage_eq_half_of_not_mem_boundary hleftBottom_not_mem
  have hleftTop :
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) leftTop simpleLadderZ = (1 / 2 : ℝ) := by
    -- Proof comment: the same boundary-value computation applies to the upper left interior
    -- neighbor.
    calc
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) leftTop simpleLadderZ
          = crossedLadderVoltage leftTop := by
              symm
              exact
                crossedLadderVoltage_eq_F_A_of_not_mem_boundary
                  (p := p) (P := P) (X := X) hleftTop_not_mem
      _ = (1 / 2 : ℝ) :=
        crossedLadderVoltage_eq_half_of_not_mem_boundary hleftTop_not_mem
  have hrightBottom :
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) rightBottom simpleLadderZ = (1 / 2 : ℝ) := by
    -- Proof comment: the lower right interior neighbor is another non-boundary point, so its
    -- continuation value is again `1 / 2`.
    calc
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) rightBottom simpleLadderZ
          = crossedLadderVoltage rightBottom := by
              symm
              exact
                crossedLadderVoltage_eq_F_A_of_not_mem_boundary
                  (p := p) (P := P) (X := X) hrightBottom_not_mem
      _ = (1 / 2 : ℝ) :=
        crossedLadderVoltage_eq_half_of_not_mem_boundary hrightBottom_not_mem
  have hrightTop :
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) rightTop simpleLadderZ = (1 / 2 : ℝ) := by
    -- Proof comment: likewise for the upper right interior neighbor.
    calc
      F_A P X ({simpleLadderA} : Set SimpleLadderVertex) rightTop simpleLadderZ
          = crossedLadderVoltage rightTop := by
              symm
              exact
                crossedLadderVoltage_eq_F_A_of_not_mem_boundary
                  (p := p) (P := P) (X := X) hrightTop_not_mem
      _ = (1 / 2 : ℝ) :=
        crossedLadderVoltage_eq_half_of_not_mem_boundary hrightTop_not_mem
  -- Proof comment: substituting the five explicit continuation values reduces the average to the
  -- rational number `3 / 5`.
  rw [hz, hleftBottom, hleftTop, hrightBottom, hrightTop]
  have hvalue : ((1 + 1 / 2 + 1 / 2 + 1 / 2 + 1 / 2) / 5 : ℝ) = 3 / 5 := by
    norm_num
  rw [hvalue]
  have hnonneg : (0 : ℝ) ≤ 3 / 5 := by
    norm_num
  rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]
  change ((3 / 5 : NNReal) : ℝ≥0∞) = (3 / 5 : ℝ≥0∞)
  norm_num

-- Proof sketch: the marked vertex `a` has degree `5` in the crossed ladder graph. Combine the
-- conductance value from `crossedLadder_effectiveConductance_between_a_z_eq_three` with the
-- Chapter 19 identity `P_a[τ_z < τ_a] = conductance(a)⁻¹ C_eff(a ↔ z)`.
/-- Exercise 19.5.4 (2): for the simple random walk on the crossed ladder graph of Fig. 19.16,
started at `a`, the probability of hitting `z` before the first strictly positive return to `a`
is `3 / 5`. -/
theorem crossedLadder_hit_z_before_return_to_a_eq_three_fifths :
    escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex) =
      (3 / 5 : ℝ≥0∞) :=
  by
    -- Route correction: the proof now uses a theorem-local deterministic-time-`1` future-path
    -- restart decomposition, followed by the explicit five-neighbor row average at `a`.
    calc
      escapeToSetProbability P X simpleLadderA ({simpleLadderZ} : Set SimpleLadderVertex)
          = ENNReal.ofReal
              ((F_A P X ({simpleLadderA} : Set SimpleLadderVertex) simpleLadderZ simpleLadderZ +
                  F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                    (⟨2, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
                  F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                    (⟨2, by decide⟩, ⟨1, by decide⟩) simpleLadderZ +
                  F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                    (⟨4, by decide⟩, ⟨0, by decide⟩) simpleLadderZ +
                  F_A P X ({simpleLadderA} : Set SimpleLadderVertex)
                    (⟨4, by decide⟩, ⟨1, by decide⟩) simpleLadderZ) / 5) := by
              exact crossedLadderEscape_eq_neighborAverage_ofFAAtA (p := p) (P := P) (X := X)
      _ = (3 / 5 : ℝ≥0∞) := by
            exact crossedLadderNeighborAverageFAAtA_eq_threeFifths (p := p) (P := P) (X := X)

end ProbabilisticBridge

end ProbabilityTheory
