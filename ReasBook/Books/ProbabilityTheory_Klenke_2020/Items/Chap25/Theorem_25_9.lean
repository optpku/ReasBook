/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_54Support
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Remark_25_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 25.2: the textbook vector space `𝓔` of predictable simple integrands is the
canonical submodule `MeasureTheory.predictableSimpleProcesses`, and its canonical image inside
`L²(μ ⊗ dt)` is `MeasureTheory.predictableSimpleProcessL2`. Theorem 25.9 concerns the closure of
that canonical subspace. -/
recall MeasureTheory.predictableSimpleProcesses

open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

namespace predictableSimpleProcessL2

variable {ℱ : ContinuousFiltration} {μ : Measure Ω}

/-- The canonical inclusion of `predictableSimpleProcessL2 ℱ μ` into its realized closure
`PredictableSimpleProcessL2Closure ℱ μ`. -/
noncomputable def toClosure (H : predictableSimpleProcessL2 ℱ μ) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  ⟨(H : Lp ℝ 2 (processMeasure μ)),
    Submodule.le_topologicalClosure (predictableSimpleProcessL2 ℱ μ) H.2⟩

/-- Coercing `H.toClosure` to ambient `L²(μ ⊗ dt)` recovers `H`. -/
@[simp] theorem coe_toClosure (H : predictableSimpleProcessL2 ℱ μ) :
    ((H.toClosure : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      (H : Lp ℝ 2 (processMeasure μ)) :=
  rfl

end predictableSimpleProcessL2

variable {ℱ : ContinuousFiltration} {μ : Measure Ω}

/-- Every globally square-integrable predictable simple process already belongs to the realized
closure `PredictableSimpleProcessL2Closure ℱ μ`. -/
theorem predictableSimpleProcessL2_mem_closure
    (ℱ : ContinuousFiltration) (μ : Measure Ω) (H : predictableSimpleProcessL2 ℱ μ) :
    (H : Lp ℝ 2 (processMeasure μ)) ∈ PredictableSimpleProcessL2Closure ℱ μ :=
  -- The closure contains the defining submodule by construction.
  Submodule.le_topologicalClosure (predictableSimpleProcessL2 ℱ μ) H.2

/-- Any ambient `L²(μ ⊗ dt)` limit of globally square-integrable predictable simple processes
belongs to the realized closure `PredictableSimpleProcessL2Closure ℱ μ`. -/
theorem mem_predictableSimpleProcessL2Closure_of_tendsto
    (ℱ : ContinuousFiltration) (μ : Measure Ω)
    {f : Lp ℝ 2 (processMeasure μ)} {Hs : ℕ → predictableSimpleProcessL2 ℱ μ}
    (hHs : Filter.Tendsto (fun n ↦ (Hs n : Lp ℝ 2 (processMeasure μ))) Filter.atTop (𝓝 f)) :
    f ∈ PredictableSimpleProcessL2Closure ℱ μ := by
  -- The topological closure is closed, so it contains every limit of points that already lie in it.
  exact (Submodule.isClosed_topologicalClosure (predictableSimpleProcessL2 ℱ μ)).mem_of_tendsto hHs
    (Filter.Eventually.of_forall fun n ↦ predictableSimpleProcessL2_mem_closure ℱ μ (Hs n))

/-- A progressively measurable process belongs to the canonical `L²(μ ⊗ dt)` closure of the
predictable simple integrands if its `Lp` class lies in `PredictableSimpleProcessL2Closure ℱ
μ`. -/
def MemPredictableStepProcessClosure (ℱ : ContinuousFiltration) (μ : Measure Ω)
    (H : Process) : Prop :=
  ∃ hH : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ),
    hH.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ

namespace MemPredictableStepProcessClosure

variable {ℱ : ContinuousFiltration} {μ : Measure Ω} {H : Process}

/-- A process in the canonical closure of the predictable simple integrands is globally
square-integrable on `Ω × [0, ∞)`. -/
theorem memLp (hH : MemPredictableStepProcessClosure ℱ μ H) :
    MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ) :=
  Exists.elim hH fun hH_memLp _ ↦ hH_memLp

/-- The `Lp` class of a process in the canonical closure belongs to the realized closure. -/
theorem toLp_mem_closure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hH.memLp.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨_, hhH⟩ => hhH

/-- A process in the canonical `L²(μ ⊗ dt)` closure of the predictable simple integrands defines
the corresponding point of the realized closure. -/
noncomputable def toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => ⟨hH_memLp.toLp (processToTimeSpaceFun H), hhH⟩

/-- Coercing `hH.toClosure` to ambient `L²(μ ⊗ dt)` recovers the `Lp` class represented by
`H`. -/
@[simp] theorem coe_toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    ((hH.toClosure : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      hH.memLp.toLp (processToTimeSpaceFun H) :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => rfl

end MemPredictableStepProcessClosure

/-- Helper for Theorem 25.9: once a process admits an ambient `L²` approximation sequence by
globally square-integrable predictable simple processes, closedness places the limit in the
realized closure `PredictableSimpleProcessL2Closure ℱ μ`. -/
private theorem mem_closure_of_exists_tendsto_predictableSimpleProcessL2
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {f : Lp ℝ 2 (processMeasure μ)}
    (happrox :
      ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
        Filter.Tendsto (fun n ↦ (Hs n : Lp ℝ 2 (processMeasure μ))) Filter.atTop (𝓝 f)) :
    f ∈ PredictableSimpleProcessL2Closure ℱ μ := by
  rcases happrox with ⟨Hs, hHs⟩
  -- The helper isolates the closedness step so the main theorem can focus only on producing the
  -- textbook approximation sequence.
  exact mem_predictableSimpleProcessL2Closure_of_tendsto ℱ μ hHs

/-- Helper for Theorem 25.9: the textbook time-height truncation at level `n` keeps only the part
of `H` with time and absolute value bounded by `n`. -/
private def timeHeightTruncation (H : Process) (n : ℕ) : Process :=
  fun t ω ↦
    if t ≤ (n : NNReal) ∧ |H t ω| ≤ (n : ℝ) then H t ω else 0

/-- Helper for Theorem 25.9: on the admissible time-height region, the truncation agrees with the
original process. -/
private theorem timeHeightTruncation_eq_self
    (H : Process) (n : ℕ) {t : NNReal} {ω : Ω}
    (ht : t ≤ (n : NNReal)) (hH : |H t ω| ≤ (n : ℝ)) :
    timeHeightTruncation H n t ω = H t ω := by
  -- Proof comment: once both cutoff inequalities hold, the defining `if` takes the retained
  -- branch and no further simplification is needed.
  simp [timeHeightTruncation, ht, hH]

/-- Helper for Theorem 25.9: after time `n`, the time-height truncation vanishes. -/
private theorem timeHeightTruncation_eq_zero_of_time_gt
    (H : Process) (n : ℕ) {t : NNReal} {ω : Ω} (ht : (n : NNReal) < t) :
    timeHeightTruncation H n t ω = 0 := by
  -- Proof comment: the time cutoff already fails, so the truncation drops to zero.
  simp [timeHeightTruncation, not_le_of_gt ht]

/-- Helper for Theorem 25.9: the truncation never exceeds the original absolute value. -/
private theorem abs_timeHeightTruncation_le_abs
    (H : Process) (n : ℕ) (t : NNReal) (ω : Ω) :
    |timeHeightTruncation H n t ω| ≤ |H t ω| := by
  -- Proof comment: either the truncation keeps `H t ω` exactly, or it replaces it by `0`.
  by_cases hkeep : t ≤ (n : NNReal) ∧ |H t ω| ≤ (n : ℝ)
  · simp [timeHeightTruncation, hkeep]
  · simp [timeHeightTruncation, hkeep]

/-- Helper for Theorem 25.9: the truncation error is pointwise dominated by the original process. -/
private theorem abs_sub_timeHeightTruncation_le_abs
    (H : Process) (n : ℕ) (t : NNReal) (ω : Ω) :
    |H t ω - timeHeightTruncation H n t ω| ≤ |H t ω| := by
  -- Proof comment: in the retained branch the error is `0`, and outside it the error is exactly
  -- `H t ω`.
  by_cases hkeep : t ≤ (n : NNReal) ∧ |H t ω| ≤ (n : ℝ)
  · simp [timeHeightTruncation, hkeep]
  · simp [timeHeightTruncation, hkeep]

/-- Helper for Theorem 25.9: the level-`n` truncation is uniformly bounded by `n`. -/
private theorem abs_timeHeightTruncation_le_level
    (H : Process) (n : ℕ) (t : NNReal) (ω : Ω) :
    |timeHeightTruncation H n t ω| ≤ (n : ℝ) := by
  -- Proof comment: in the retained branch the defining cutoff already supplies the level bound,
  -- and otherwise the value is `0`.
  by_cases hkeep : t ≤ (n : NNReal) ∧ |H t ω| ≤ (n : ℝ)
  · simp [timeHeightTruncation, hkeep, hkeep.2]
  · simp [timeHeightTruncation, hkeep]

/-- Helper for Theorem 25.9: every time-height truncation has the boundedness package needed for
the bounded-cutoff approximation step. -/
private theorem timeHeightTruncation_hasBound (H : Process) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |timeHeightTruncation H n t ω| ≤ C := by
  -- Proof comment: the explicit textbook bound is the truncation level itself.
  refine ⟨n, by positivity, ?_⟩
  intro t ω
  exact abs_timeHeightTruncation_le_level H n t ω

/-- Helper for Theorem 25.9: every time-height truncation has compact time support `[0, n]`. -/
private theorem timeHeightTruncation_hasCutoff (H : Process) (n : ℕ) :
    ∃ T : NNReal, ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → timeHeightTruncation H n t ω = 0 := by
  -- Proof comment: the truncation is defined to vanish identically after time `n`.
  refine ⟨n, ?_⟩
  intro t ω ht
  exact timeHeightTruncation_eq_zero_of_time_gt H n ht

/-- Helper for Theorem 25.9: under `processMeasure μ`, the time-height truncation is the ambient
indicator cutoff of `processToTimeSpaceFun H` by the joint time and height bound. -/
private theorem processToTimeSpaceFun_timeHeightTruncation
    (μ : Measure Ω) (H : Process) (n : ℕ) :
    processToTimeSpaceFun (timeHeightTruncation H n) =ᵐ[processMeasure μ]
      Set.indicator
        {x : Ω × ℝ | x.2 ≤ (n : ℝ) ∧ |processToTimeSpaceFun H x| ≤ (n : ℝ)}
        (processToTimeSpaceFun H) := by
  -- Route correction: the downstream `MemLp` step only needs an almost-everywhere identity, so
  -- we record the truncation rewrite directly in the `processMeasure μ` spelling world.
  filter_upwards with x
  -- Proof comment: `processToTimeSpaceFun` evaluates the process at `x.2.toNNReal`, so the
  -- truncation condition is exactly the ambient time-height indicator condition.
  rcases x with ⟨ω, t⟩
  by_cases hkeep : t.toNNReal ≤ (n : NNReal) ∧ |H t.toNNReal ω| ≤ (n : ℝ)
  · have hx : t ≤ (n : ℝ) ∧ |processToTimeSpaceFun H (ω, t)| ≤ (n : ℝ) := by
      refine ⟨Real.toNNReal_le_iff_le_coe.1 hkeep.1, ?_⟩
      simpa [processToTimeSpaceFun] using hkeep.2
    simp [processToTimeSpaceFun, timeHeightTruncation, hkeep, hx]
  · have hx : ¬ (t ≤ (n : ℝ) ∧ |processToTimeSpaceFun H (ω, t)| ≤ (n : ℝ)) := by
      intro hx
      apply hkeep
      refine ⟨Real.toNNReal_le_iff_le_coe.2 hx.1, ?_⟩
      simpa [processToTimeSpaceFun] using hx.2
    have hx' : ¬ (t ≤ (n : ℝ) ∧ |H t.toNNReal ω| ≤ (n : ℝ)) := by
      simpa [processToTimeSpaceFun] using hx
    simp [processToTimeSpaceFun, timeHeightTruncation, hx, hx']

/-- Helper for Theorem 25.9: on each finite time strip `Set.Iic i × Ω`, the time-height
truncation is an indicator of the original process by the same strip-local time-height bound. -/
private theorem timeHeightTruncation_strip_eq_indicator
    (H : Process) (i : NNReal) (n : ℕ) :
    (fun p : Set.Iic i × Ω ↦ timeHeightTruncation H n p.1 p.2) =
      Set.indicator
        {p : Set.Iic i × Ω | ((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ)}
        (fun p : Set.Iic i × Ω ↦ H p.1 p.2) := by
  -- Proof comment: on the strip, the truncation keeps `H` exactly on the admissible region and
  -- is zero outside it, which is precisely the indicator definition.
  funext p
  by_cases hkeep : (p.1 : NNReal) ≤ (n : NNReal) ∧ |H p.1 p.2| ≤ (n : ℝ)
  · have hp :
        ((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ) := by
      exact ⟨by exact_mod_cast hkeep.1, hkeep.2⟩
    have hp' : p ∈
        {p : Set.Iic i × Ω | ((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ)} := hp
    simp [timeHeightTruncation, hkeep, hp, hp']
  · have hp :
        ¬ (((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ)) := by
      intro hp
      apply hkeep
      exact ⟨by exact_mod_cast hp.1, hp.2⟩
    have hp' : p ∉
        {p : Set.Iic i × Ω | ((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ)} := hp
    simp [timeHeightTruncation, hkeep, hp, hp']

/-- Helper for Theorem 25.9: time-height truncation preserves progressive measurability. -/
private theorem progMeasurable_timeHeightTruncation
    {ℱ : ContinuousFiltration} {H : Process} (hH : ProgMeasurable ℱ H) (n : ℕ) :
    ProgMeasurable ℱ (timeHeightTruncation H n) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  let s : Set (Set.Iic i × Ω) :=
    {p | ((p.1 : NNReal) : ℝ) ≤ (n : ℝ) ∧ |H p.1 p.2| ≤ (n : ℝ)}
  have htimeMeas : Measurable (fun p : Set.Iic i × Ω ↦ ((p.1 : NNReal) : ℝ)) := by
    exact NNReal.continuous_coe.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  have hslice : StronglyMeasurable (fun p : Set.Iic i × Ω ↦ H p.1 p.2) := hH i
  have hnormMeas : Measurable (fun p : Set.Iic i × Ω ↦ |H p.1 p.2|) := by
    exact hslice.measurable.norm
  have hs : MeasurableSet s := by
    exact (measurableSet_le htimeMeas measurable_const).inter
      (measurableSet_le hnormMeas measurable_const)
  -- Proof comment: after the strip-local normalization, progressive measurability is inherited
  -- from the original process by the indicator constructor on the slab.
  rw [timeHeightTruncation_strip_eq_indicator H i n]
  simpa [s] using (hH i).indicator hs

/-- Helper for Theorem 25.9: on `Ω × [0, ∞)`, the ambient time-space function of a truncation is
pointwise dominated by the ambient time-space function of the original process. -/
private theorem norm_processToTimeSpaceFun_timeHeightTruncation_le
    (H : Process) (n : ℕ) (x : Ω × ℝ) :
    ‖processToTimeSpaceFun (timeHeightTruncation H n) x‖ ≤ ‖processToTimeSpaceFun H x‖ := by
  -- Proof comment: after evaluating `processToTimeSpaceFun`, this is exactly the previously proved
  -- pointwise absolute-value bound for the truncation on the original process.
  simpa [processToTimeSpaceFun, Real.norm_eq_abs] using
    abs_timeHeightTruncation_le_abs H n x.2.toNNReal x.1

/-- Helper for Theorem 25.9: the textbook truncations recover the original time-space function at
each fixed point once the time and height cutoffs exceed that point's coordinates. -/
private theorem tendsto_processToTimeSpaceFun_timeHeightTruncation
    (H : Process) (x : Ω × ℝ) :
    Filter.Tendsto (fun n ↦ processToTimeSpaceFun (timeHeightTruncation H n) x) Filter.atTop
      (𝓝 (processToTimeSpaceFun H x)) := by
  rcases x with ⟨ω, t⟩
  let N : ℕ :=
    max (Nat.ceil ((t.toNNReal : ℝ))) (Nat.ceil |H t.toNNReal ω|)
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
  have ht_real : (t.toNNReal : ℝ) ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil ((t.toNNReal : ℝ))) ?_
    exact_mod_cast le_trans (le_max_left _ _) hn
  have hH_real : |H t.toNNReal ω| ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil |H t.toNNReal ω|) ?_
    exact_mod_cast le_trans (le_max_right _ _) hn
  have ht_nnreal : t.toNNReal ≤ (n : NNReal) := by
    exact_mod_cast ht_real
  -- Proof comment: beyond the combined time-height threshold, the truncation stays on the
  -- retained branch, so the ambient time-space function becomes literally constant.
  simp [processToTimeSpaceFun, timeHeightTruncation_eq_self H n ht_nnreal hH_real]

/-- Helper for Theorem 25.9: once an auxiliary `L²` family `G n` tends to `f`, and each `G n`
admits a predictable-simple `L²` approximation sequence, a diagonal extraction gives one
predictable-simple sequence converging directly to `f`. -/
-- TODO: after the truncation and bounded-cutoff approximation fronts are stabilized, restore the
-- diagonal extraction proof from the current metric-space argument.
private theorem exists_tendsto_predictableSimpleProcessL2_of_tendsto_and_each_exists
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {f : Lp ℝ 2 (processMeasure μ)} {G : ℕ → Process}
    (hG_memLp : ∀ n, MemLp (processToTimeSpaceFun (G n)) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_tendsto :
      Filter.Tendsto
        (fun n ↦ (hG_memLp n).toLp (processToTimeSpaceFun (G n)))
        Filter.atTop (𝓝 f))
    (happrox :
      ∀ n,
        ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
          Filter.Tendsto (fun m ↦ (Hs m : Lp ℝ 2 (processMeasure μ))) Filter.atTop
            (𝓝 ((hG_memLp n).toLp (processToTimeSpaceFun (G n))))) :
    ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
      Filter.Tendsto (fun n ↦ (Hs n : Lp ℝ 2 (processMeasure μ))) Filter.atTop (𝓝 f) := by
  classical
  choose Ks hKs using happrox
  have hKs_close :
      ∀ n, ∃ N : ℕ,
        ∀ m ≥ N,
          dist
              (((Ks n) m : predictableSimpleProcessL2 ℱ μ) :
                Lp ℝ 2 (processMeasure μ))
              ((hG_memLp n).toLp (processToTimeSpaceFun (G n))) <
            (1 : ℝ) / (n + 1) := by
    intro n
    -- Proof comment: for each outer index, choose an inner cutoff where the predictable-simple
    -- approximation is already within `1 / (n + 1)` in the ambient `L²` metric.
    rcases Metric.tendsto_atTop.1 (hKs n) ((1 : ℝ) / (n + 1)) (by positivity) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  choose N hN using hKs_close
  refine ⟨fun n ↦ (Ks n) (max n (N n)), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmall :
      Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- Proof comment: control the outer error by `ε / 2` and the inner diagonal error by the same
  -- margin, then finish by the triangle inequality.
  rcases Metric.tendsto_atTop.1 hG_tendsto (ε / 2) (by positivity) with ⟨N₀, hN₀⟩
  rcases Metric.tendsto_atTop.1 hsmall (ε / 2) (by positivity) with ⟨N₁, hN₁⟩
  refine ⟨max N₀ N₁, ?_⟩
  intro n hn
  have houter :
      dist ((hG_memLp n).toLp (processToTimeSpaceFun (G n))) f < ε / 2 :=
    hN₀ n (le_trans (le_max_left _ _) hn)
  have hdiag :
      dist
          (((Ks n) (max n (N n)) : predictableSimpleProcessL2 ℱ μ) :
            Lp ℝ 2 (processMeasure μ))
          ((hG_memLp n).toLp (processToTimeSpaceFun (G n))) <
        (1 : ℝ) / (n + 1) :=
    hN n (max n (N n)) (le_max_right _ _)
  have hsmall_n : (1 : ℝ) / (n + 1) < ε / 2 :=
    by
      have habs : |(((n : ℝ) + 1)⁻¹)| < ε / 2 := by
        simpa [Real.dist_eq, one_div, Nat.cast_add, Nat.cast_one] using
          hN₁ n (le_trans (le_max_right _ _) hn)
      have hnonneg : 0 ≤ (((n : ℝ) + 1)⁻¹) := by positivity
      simpa [one_div, Nat.cast_add, Nat.cast_one, abs_of_nonneg hnonneg] using habs
  calc
    dist
        ((((Ks n) (max n (N n)) : predictableSimpleProcessL2 ℱ μ) :
          Lp ℝ 2 (processMeasure μ))) f
      ≤ dist
            (((Ks n) (max n (N n)) : predictableSimpleProcessL2 ℱ μ) :
              Lp ℝ 2 (processMeasure μ))
            ((hG_memLp n).toLp (processToTimeSpaceFun (G n))) +
          dist ((hG_memLp n).toLp (processToTimeSpaceFun (G n))) f :=
        dist_triangle _ _ _
    _ < (1 : ℝ) / (n + 1) + ε / 2 := add_lt_add hdiag houter
    _ < ε := by linarith

/-- Helper for Theorem 25.9: clamping a real time by `Real.toNNReal` preserves the interval
indicator of a nonnegative half-open strip. -/
private theorem realIndicator_eq_nnrealIndicator
    (a b : NNReal) (t : ℝ) :
    Set.indicator (Set.Ioc a b) (fun _ : NNReal ↦ (1 : ℝ)) t.toNNReal =
      Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)) t := by
  by_cases ht0 : 0 ≤ t
  · -- Proof comment: on nonnegative times, `Real.toNNReal` is literally the identity.
    have hmem :
        t.toNNReal ∈ Set.Ioc a b ↔ t ∈ Set.Ioc (a : ℝ) b := by
      rw [Set.mem_Ioc, Set.mem_Ioc, Real.toNNReal_of_nonneg ht0]
      constructor
      · intro ht
        exact ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
      · intro ht
        exact ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
    by_cases ht : t ∈ Set.Ioc (a : ℝ) b
    · have hnn : t.toNNReal ∈ Set.Ioc a b := hmem.mpr ht
      simp [ht, hnn]
    · have hnn : t.toNNReal ∉ Set.Ioc a b := by
        exact mt hmem.mp ht
      simp [ht, hnn]
  · have ht_nonpos : t.toNNReal = 0 := Real.toNNReal_of_nonpos (le_of_not_ge ht0)
    have hnot_real : t ∉ Set.Ioc (a : ℝ) b := by
      intro ht
      exact ht0 (le_trans (show (0 : ℝ) ≤ a by exact_mod_cast bot_le) (le_of_lt ht.1))
    -- Proof comment: for negative times, both indicators vanish because the strip lies in
    -- `[0, ∞)`.
    simp [hnot_real, ht_nonpos]

/-- Helper for Theorem 25.9: the indicator of a nonnegative half-open strip is integrable on the
time measure `((volume : Measure ℝ).restrict (Set.Ici 0))`. -/
private theorem integrableIndicatorIocOnIci
    (a b : NNReal) :
    Integrable
      (Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)))
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  have hsubset : Set.Ioc (a : ℝ) b ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact le_of_lt <| lt_of_le_of_lt (show (0 : ℝ) ≤ a by exact_mod_cast bot_le) ht.1
  have hfinite :
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) (Set.Ioc (a : ℝ) b) ≠ ∞ := by
    rw [Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.2 hsubset]
    exact ne_of_lt measure_Ioc_lt_top
  -- Proof comment: on `[0,∞)`, the indicator is just the constant function `1` on a finite strip.
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const hfinite

/-- Helper for Theorem 25.9: integrating a constant multiple of a nonnegative strip indicator over
`[0,∞)` returns the interval length. -/
private theorem integralConstMulIndicatorIocOnIci
    (a b : NNReal) (c : ℝ) (hab : a ≤ b) :
    ∫ t in Set.Ici (0 : ℝ), c * Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)) t =
      c * ((b - a : NNReal) : ℝ) := by
  have hsubset : Set.Ioc (a : ℝ) b ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact le_of_lt <| lt_of_le_of_lt (show (0 : ℝ) ≤ a by exact_mod_cast bot_le) ht.1
  have hlength :
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).real (Set.Ioc (a : ℝ) b) =
        ((b - a : NNReal) : ℝ) := by
    rw [measureReal_def, Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.2 hsubset,
      Real.volume_Ioc]
    simpa [NNReal.coe_sub hab]
  rw [integral_const_mul]
  have hindicator :
      ∫ t in Set.Ici (0 : ℝ),
          Set.indicator (Set.Ioc (a : ℝ) b) (fun _ : ℝ ↦ (1 : ℝ)) t ∂ (volume : Measure ℝ) =
        ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))).real (Set.Ioc (a : ℝ) b) := by
    have hindicator' :=
      integral_indicator_one
        (μ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) (s := Set.Ioc (a : ℝ) b)
        measurableSet_Ioc
    simpa using hindicator'
  -- Proof comment: the indicator integral is exactly the restricted strip length.
  rw [hindicator, hlength]

/-- Helper for Theorem 25.9: package a deterministic partition and bounded left-endpoint
coefficients into a predictable-step representation. -/
private def predictableStepRepresentationOfPartition
    {ℱ : ContinuousFiltration} {n : ℕ}
    (times : Fin (n + 1) → NNReal) (times_zero : times 0 = 0)
    (times_strictMono : StrictMono times) (coeff : Fin n → Ω → ℝ)
    (coeff_bounded : ∀ i, ∃ C : ℝ, ∀ ω, |coeff i ω| ≤ C)
    (coeff_measurable : ∀ i, Measurable[ℱ (times i.castSucc)] (coeff i)) :
    PredictableStepRepresentation ℱ :=
  { n := n
    times := times
    coeff := coeff
    times_zero := times_zero
    times_strictMono := times_strictMono
    coeff_bounded := coeff_bounded
    coeff_measurable := coeff_measurable }

/-- Helper for Theorem 25.9: on a fixed partition strip, squaring the step process isolates the
corresponding squared coefficient times the strip indicator. -/
private theorem predictableStepRepresentation_sq_eq_indicatorSum_of_mem_interval
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω)
    (i : Fin data.n) {t : ℝ} (ht0 : 0 ≤ t)
    (hti : t.toNNReal ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ)) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ j,
        (data.coeff j ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  have hti_real :
      t ∈ Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ) := by
    simpa [Real.toNNReal_of_nonneg ht0] using hti
  have hproc : data.toProcess t.toNNReal ω = data.coeff i ω :=
    data.toProcess_eq_coeff_of_mem_interval i hti ω
  calc
    (data.toProcess t.toNNReal ω) ^ 2 = (data.coeff i ω) ^ 2 := by rw [hproc]
    _ =
        ∑ j,
          (data.coeff j ω) ^ 2 *
            Set.indicator
              (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
              (fun _ : ℝ ↦ (1 : ℝ)) t := by
          symm
          rw [Finset.sum_eq_single i]
          · simp [hti_real]
          · intro j _ hji
            have hj_not :
                t ∉ Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ) := by
              intro htj
              have htj_nn :
                  t.toNNReal ∈ Set.Ioc (data.times j.castSucc) (data.times j.succ) := by
                simpa [Real.toNNReal_of_nonneg ht0] using htj
              exact data.not_mem_interval_of_ne hji hti htj_nn
            simp [hj_not]
          · simp

/-- Helper for Theorem 25.9: once time is past the last partition point, all strip indicators in
the step representation vanish. -/
private theorem predictableStepRepresentation_sq_eq_indicatorSum_of_last_lt
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) {t : ℝ}
    (ht0 : 0 ≤ t) (hAfter : data.times (Fin.last data.n) < t.toNNReal) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ j,
        (data.coeff j ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  have hAfterReal : (data.times (Fin.last data.n) : ℝ) < t := by
    simpa [Real.toNNReal_of_nonneg ht0] using hAfter
  have hproc : data.toProcess t.toNNReal ω = 0 := by
    exact data.toProcess_eq_zero_of_last_lt hAfter ω
  calc
    (data.toProcess t.toNNReal ω) ^ 2 = 0 := by simp [hproc]
    _ =
        ∑ j,
          (data.coeff j ω) ^ 2 *
            Set.indicator
              (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
              (fun _ : ℝ ↦ (1 : ℝ)) t := by
          symm
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hj_upper :
              ((data.times j.succ : NNReal) : ℝ) ≤ data.times (Fin.last data.n) := by
            exact_mod_cast data.times_strictMono.monotone (Fin.le_last j.succ)
          have hj_not :
              t ∉ Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ) := by
            exact fun htj ↦ (not_le_of_gt hAfterReal) (le_trans htj.2 hj_upper)
          simp [hj_not]

/-- Helper for Theorem 25.9: at every nonnegative time, the square of a predictable-step process is
the finite sum of squared coefficients times strip indicators. -/
private theorem predictableStepRepresentation_sq_eq_indicatorSum_of_nonneg
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) {t : ℝ}
    (ht0 : 0 ≤ t) :
    (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ j,
        (data.coeff j ω) ^ 2 *
          Set.indicator
            (Set.Ioc ((data.times j.castSucc : NNReal) : ℝ) (data.times j.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) t := by
  by_cases ht_eq : t = 0
  · subst ht_eq
    -- Proof comment: at time `0`, all half-open strips are empty on the left endpoint.
    simp [PredictableStepRepresentation.toProcess_apply]
  · by_cases ht_le_last : t.toNNReal ≤ data.times (Fin.last data.n)
    · have ht_pos : 0 < t.toNNReal := by
        have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
        simpa [Real.toNNReal_of_nonneg ht0] using this
      obtain ⟨i, hti⟩ := data.exists_mem_interval_of_pos_le_last ht_pos ht_le_last
      exact predictableStepRepresentation_sq_eq_indicatorSum_of_mem_interval data ω i ht0 hti
    · exact predictableStepRepresentation_sq_eq_indicatorSum_of_last_lt data ω ht0
        (lt_of_not_ge ht_le_last)

/-- Helper for Theorem 25.9: integrating the square of a predictable-step process over time yields
the textbook sum of coefficient squares times interval lengths. -/
private theorem predictableStepRepresentation_timeIntegralSq_eq_sum
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) :
    ∫ t in Set.Ici (0 : ℝ), (data.toProcess t.toNNReal ω) ^ 2 =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  have hpoint :
      (fun t : ℝ ↦ (data.toProcess t.toNNReal ω) ^ 2) =ᵐ[
          (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))]
        fun t ↦
          ∑ i,
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
    -- Proof comment: on `[0,∞)`, `t.toNNReal = t`, so the pointwise strip decomposition applies.
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
    exact predictableStepRepresentation_sq_eq_indicatorSum_of_nonneg data ω ht0
  calc
    ∫ t in Set.Ici (0 : ℝ), (data.toProcess t.toNNReal ω) ^ 2 =
        ∫ t in Set.Ici (0 : ℝ),
          ∑ i,
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
      exact integral_congr_ae hpoint
    _ =
        ∑ i,
          ∫ t in Set.Ici (0 : ℝ),
            (data.coeff i ω) ^ 2 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
      rw [integral_finset_sum]
      intro i hi
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (integrableIndicatorIocOnIci (data.times i.castSucc) (data.times i.succ)).const_mul
          ((data.coeff i ω) ^ 2)
    _ =
        ∑ i,
          (data.coeff i ω) ^ 2 *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      -- Proof comment: each strip contributes its coefficient square times the strip length.
      exact integralConstMulIndicatorIocOnIci
        (data.times i.castSucc) (data.times i.succ) ((data.coeff i ω) ^ 2)
        (le_of_lt (data.times_strictMono i.castSucc_lt_succ))

/-- Helper for Theorem 25.9: the ambient time-space function of a predictable-step representation
is strongly measurable on `Ω × ℝ`. -/
private theorem predictableStepRepresentation_stronglyMeasurable_processToTimeSpaceFun
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) :
    StronglyMeasurable (processToTimeSpaceFun data.toProcess) := by
  have hEq :
      processToTimeSpaceFun data.toProcess =
        fun x : Ω × ℝ ↦
          ∑ i,
            data.coeff i x.1 *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) x.2 := by
    funext x
    rcases x with ⟨ω, t⟩
    -- Proof comment: `processToTimeSpaceFun` only changes the time coordinate via `toNNReal`,
    -- and `realIndicator_eq_nnrealIndicator` removes that clamp strip by strip.
    simp [processToTimeSpaceFun, PredictableStepRepresentation.toProcess_apply,
      realIndicator_eq_nnrealIndicator]
  rw [hEq]
  refine (Finset.measurable_fun_sum _ fun i _ ↦ ?_).stronglyMeasurable
  have hcoeff_base : Measurable (data.coeff i) := by
    exact (data.coeff_measurable i).mono (ℱ.le _) le_rfl
  have hcoeff :
      Measurable (fun x : Ω × ℝ ↦ data.coeff i x.1) := by
    exact hcoeff_base.comp measurable_fst
  have hindicator :
      Measurable
        (fun x : Ω × ℝ ↦
          Set.indicator
            (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
            (fun _ : ℝ ↦ (1 : ℝ)) x.2) := by
    exact (Measurable.indicator measurable_const measurableSet_Ioc).comp measurable_snd
  exact hcoeff.mul hindicator

/-- Helper for Theorem 25.9: square-integrable coefficients make the represented step process
square-integrable in the ambient `processMeasure μ` space. -/
private theorem predictableStepRepresentation_integrableSq_of_sqIntegrableCoeff
    {ℱ : ContinuousFiltration} (μ : Measure Ω) (data : PredictableStepRepresentation ℱ)
    (hCoeff : ∀ i : Fin data.n, MemLp (data.coeff i) (2 : ℝ≥0∞) μ) :
    Integrable (fun x : Ω × ℝ ↦ (processToTimeSpaceFun data.toProcess x) ^ 2) (processMeasure μ) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hMeas :
      AEStronglyMeasurable (fun x : Ω × ℝ ↦ (processToTimeSpaceFun data.toProcess x) ^ 2)
        (μ.prod ν) := by
    -- Proof comment: the represented process is predictable, so its squared time-space function is
    -- measurable on the ambient product space.
    let hStrong :
        StronglyMeasurable (processToTimeSpaceFun data.toProcess) :=
      predictableStepRepresentation_stronglyMeasurable_processToTimeSpaceFun data
    exact hStrong.aestronglyMeasurable.pow 2
  refine (integrable_prod_iff hMeas).2 ?_
  refine ⟨Filter.Eventually.of_forall fun ω ↦ ?_, ?_⟩
  · have hpoint :
        (fun t : ℝ ↦ (processToTimeSpaceFun data.toProcess (ω, t)) ^ 2) =ᵐ[ν]
          fun t ↦
            ∑ i,
              (data.coeff i ω) ^ 2 *
                Set.indicator
                  (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                  (fun _ : ℝ ↦ (1 : ℝ)) t := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
      simpa [ν, processToTimeSpaceFun] using
        predictableStepRepresentation_sq_eq_indicatorSum_of_nonneg data ω ht0
    have hsum :
        Integrable
          (fun t : ℝ ↦
            ∑ i,
              (data.coeff i ω) ^ 2 *
                Set.indicator
                  (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                  (fun _ : ℝ ↦ (1 : ℝ)) t)
          ν := by
      refine integrable_finset_sum _ ?_
      intro i hi
      simpa [ν, mul_comm, mul_left_comm, mul_assoc] using
        (integrableIndicatorIocOnIci (data.times i.castSucc) (data.times i.succ)).const_mul
          ((data.coeff i ω) ^ 2)
    -- Proof comment: each time section is a finite sum of integrable strip indicators.
    exact hsum.congr hpoint.symm
  · have hOuterEq :
        (fun ω ↦
          ∫ t, ‖(processToTimeSpaceFun data.toProcess (ω, t)) ^ 2‖ ∂ν) =
          fun ω ↦
            ∑ i,
              (data.coeff i ω) ^ 2 *
                ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
      funext ω
      calc
        ∫ t, ‖(processToTimeSpaceFun data.toProcess (ω, t)) ^ 2‖ ∂ν =
            ∫ t, (processToTimeSpaceFun data.toProcess (ω, t)) ^ 2 ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
          have hsq_nonneg : 0 ≤ (processToTimeSpaceFun data.toProcess (ω, t)) ^ 2 := sq_nonneg _
          simp [ν, hsq_nonneg]
        _ = ∫ t in Set.Ici (0 : ℝ), (data.toProcess t.toNNReal ω) ^ 2 := by
          rfl
        _ =
            ∑ i,
              (data.coeff i ω) ^ 2 *
                ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) :=
          predictableStepRepresentation_timeIntegralSq_eq_sum data ω
    rw [hOuterEq]
    -- Proof comment: the outer integrand is a finite linear combination of the coefficient-square
    -- sections, which are integrable by the `MemLp` hypotheses.
    refine integrable_finset_sum _ ?_
    intro i hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hCoeff i).integrable_sq.mul_const
        (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ))

/-- Helper for Theorem 25.9: if the coefficients of a predictable-step representation are
square-integrable under `μ`, then the represented process belongs to ambient
`L²(processMeasure μ)`. -/
private theorem predictableStepRepresentation_memLp_of_sqIntegrableCoeff
    {ℱ : ContinuousFiltration} (μ : Measure Ω) (data : PredictableStepRepresentation ℱ)
    (hCoeff : ∀ i : Fin data.n, MemLp (data.coeff i) (2 : ℝ≥0∞) μ) :
    MemLp (processToTimeSpaceFun data.toProcess) (2 : ℝ≥0∞) (processMeasure μ) := by
  -- Route correction: prove square-integrability directly in the ambient product-measure spelling
  -- and only then repackage it as a `MemLp` statement.
  let hStrong :
      StronglyMeasurable (processToTimeSpaceFun data.toProcess) :=
    predictableStepRepresentation_stronglyMeasurable_processToTimeSpaceFun data
  refine
    (memLp_two_iff_integrable_sq hStrong.aestronglyMeasurable).2 ?_
  simpa using predictableStepRepresentation_integrableSq_of_sqIntegrableCoeff μ data hCoeff

/-- Helper for Theorem 25.9: a predictable-step representation with square-integrable
coefficients determines a point of `predictableSimpleProcessL2 ℱ μ`. -/
private theorem predictableStepRepresentation_toLp_mem_predictableSimpleProcessL2_of_sqIntegrableCoeff
    {ℱ : ContinuousFiltration} (μ : Measure Ω) (data : PredictableStepRepresentation ℱ)
    (hCoeff : ∀ i : Fin data.n, MemLp (data.coeff i) (2 : ℝ≥0∞) μ) :
    (predictableStepRepresentation_memLp_of_sqIntegrableCoeff μ data hCoeff).toLp
        (processToTimeSpaceFun data.toProcess) ∈
      predictableSimpleProcessL2 ℱ μ := by
  -- Proof comment: once the represented process is in ambient `L²`, the canonical predictable
  -- simple process attached to the representation lies in the defining submodule by construction.
  simpa [PredictableStepRepresentation.toPredictableSimpleProcess_coe] using
    toLp_mem_predictableSimpleProcessL2 data.toPredictableSimpleProcess
      (predictableStepRepresentation_memLp_of_sqIntegrableCoeff μ data hCoeff)

/-- Helper for Theorem 25.9: the source Step 2 moving-average regularization with deterministic
cutoff horizon `T`. -/
private def movingAverageCutoff (G : Process) (T : NNReal) (n : ℕ) : Process :=
  fun t ω ↦
    ((n + 1 : ℝ)) *
      ∫ s in max ((t : ℝ) - (1 / (n + 1 : ℝ))) 0..min (t : ℝ) T, G s.toNNReal ω

/-- Helper for Theorem 25.9: once time is at least one averaging window past `T`, the moving
average cutoff row vanishes because the whole backward window lies in the zero region of `G`. -/
private theorem movingAverageCutoff_eq_zero_of_window_past_cutoff
    {G : Process} (T : NNReal) (n : ℕ)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    {t : NNReal} (ht : T + (1 / (n + 1 : NNReal)) ≤ t) (ω : Ω) :
    movingAverageCutoff G T n t ω = 0 := by
  have hstep_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
  have ht' : (T : ℝ) + 1 / (n + 1 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast ht
  have hT_le_t : (T : ℝ) ≤ (t : ℝ) := by
    calc
      (T : ℝ) ≤ (T : ℝ) + 1 / (n + 1 : ℝ) := by linarith
      _ ≤ (t : ℝ) := ht'
  have hT_le_windowLeft : (T : ℝ) ≤ (t : ℝ) - 1 / (n + 1 : ℝ) := by
    linarith
  have hwindowLeft_nonneg : 0 ≤ (t : ℝ) - 1 / (n + 1 : ℝ) := by
    linarith [show (0 : ℝ) ≤ (T : ℝ) by exact_mod_cast bot_le, hT_le_windowLeft]
  have hmax :
      max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0 = (t : ℝ) - 1 / (n + 1 : ℝ) :=
    max_eq_left hwindowLeft_nonneg
  have hmin : min (t : ℝ) T = T := min_eq_right hT_le_t
  have hzero_ae :
      ∀ᵐ s ∂volume,
        s ∈ Set.uIoc ((t : ℝ) - 1 / (n + 1 : ℝ)) (T : ℝ) → G (Real.toNNReal s) ω = 0 :=
    Filter.Eventually.of_forall fun s hs ↦ by
      rw [Set.uIoc_of_ge hT_le_windowLeft] at hs
      have hs_nonneg : 0 ≤ s := by
        exact le_trans (show (0 : ℝ) ≤ (T : ℝ) by exact_mod_cast bot_le) hs.1.le
      have hs_gt : T < s.toNNReal := by
        rw [Real.toNNReal_of_nonneg hs_nonneg]
        exact hs.1
      exact hG_cutoff hs_gt
  have hintegral :
      ∫ s in ((t : ℝ) - 1 / (n + 1 : ℝ))..(T : ℝ), G s.toNNReal ω = 0 :=
    intervalIntegral.integral_zero_ae hzero_ae
  -- Proof comment: after rewriting the window endpoints, the interval lies entirely to the right
  -- of `T`, so the integrand is identically zero on the whole `uIoc` support.
  rw [movingAverageCutoff, hmax, hmin, hintegral, mul_zero]

/-- Helper for Theorem 25.9: on the active time strip `t ≤ T + 1/(n+1)`, the moving-average row
inherits the same uniform bound as `G`. -/
private theorem abs_movingAverageCutoff_le_of_le_cutoffWindow
    {G : Process} (T : NNReal) (n : ℕ)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hG_bdd : ∀ t ω, |G t ω| ≤ C)
    {t : NNReal} (ht : t ≤ T + (1 / (n + 1 : NNReal))) (ω : Ω) :
    |movingAverageCutoff G T n t ω| ≤ C := by
  let a : ℝ := max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0
  let b : ℝ := min (t : ℝ) T
  have hstep_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
  have ht' : (t : ℝ) ≤ (T : ℝ) + 1 / (n + 1 : ℝ) := by
    exact_mod_cast ht
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast bot_le
  have ha_le_t : a ≤ (t : ℝ) := by
    refine max_le_iff.mpr ?_
    constructor
    · linarith
    · simpa using ht_nonneg
  have ha_le_T : a ≤ (T : ℝ) := by
    refine max_le_iff.mpr ?_
    constructor
    · linarith
    · exact show (0 : ℝ) ≤ (T : ℝ) by exact_mod_cast bot_le
  have ha_le_b : a ≤ b := le_min ha_le_t ha_le_T
  have hwindowLeft_le_a : (t : ℝ) - 1 / (n + 1 : ℝ) ≤ a := le_max_left _ _
  have hb_le_t : b ≤ (t : ℝ) := min_le_left _ _
  have habs :
      |∫ s in a..b, G s.toNNReal ω| ≤ C * |b - a| := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := b) (f := fun s : ℝ ↦ G s.toNNReal ω) fun s _hs ↦ hG_bdd s.toNNReal ω)
  have hlength : |b - a| ≤ 1 / (n + 1 : ℝ) := by
    have hsub : b - a ≤ 1 / (n + 1 : ℝ) := by
      have h₁ : b - a ≤ (t : ℝ) - a := sub_le_sub_right hb_le_t a
      have h₂ : (t : ℝ) - a ≤ (t : ℝ) - ((t : ℝ) - 1 / (n + 1 : ℝ)) := by
        exact sub_le_sub_left hwindowLeft_le_a (t : ℝ)
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr ha_le_b)]
    exact hsub
  have hfactor_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
  have hlength_nonneg : 0 ≤ |b - a| := abs_nonneg _
  calc
    |movingAverageCutoff G T n t ω|
      = ((n + 1 : ℝ)) * |∫ s in a..b, G s.toNNReal ω| := by
          simp [movingAverageCutoff, a, b, abs_mul, abs_of_nonneg hfactor_nonneg]
    _ ≤ ((n + 1 : ℝ)) * (C * |b - a|) :=
      mul_le_mul_of_nonneg_left habs hfactor_nonneg
    _ ≤ ((n + 1 : ℝ)) * (C * (1 / (n + 1 : ℝ))) := by
      gcongr
    _ = C := by
      have hfactor_ne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hfactor_ne]

/-- Helper for Theorem 25.9: every moving-average cutoff row stays uniformly bounded by the same
bound `C` as the original bounded cutoff process. -/
private theorem abs_movingAverageCutoff_le
    {G : Process} (T : NNReal) (n : ℕ)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hG_bdd : ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (t : NNReal) (ω : Ω) :
    |movingAverageCutoff G T n t ω| ≤ C := by
  by_cases ht : t ≤ T + (1 / (n + 1 : NNReal))
  · -- Proof comment: before the deterministic cutoff window expires, the averaging interval has
    -- length at most `1 / (n + 1)`, so the normalized average stays within the original bound.
    exact abs_movingAverageCutoff_le_of_le_cutoffWindow T n hC_nonneg hG_bdd ht ω
  · have hzero :
        movingAverageCutoff G T n t ω = 0 :=
      movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff
        (le_of_lt (lt_of_not_ge ht)) ω
    -- Proof comment: once the whole backward window is beyond `T`, the process is identically
    -- zero, so the global bound is immediate.
    simp [hzero, hC_nonneg]

/-- Helper for Theorem 25.9: each moving-average cutoff row inherits the same global bound
package as the original bounded cutoff process. -/
private theorem movingAverageCutoff_hasBound
    {G : Process} (T : NNReal) (n : ℕ)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |movingAverageCutoff G T n t ω| ≤ C := by
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ω
  -- Proof comment: the row-wise moving average never exceeds the original uniform bound.
  exact abs_movingAverageCutoff_le T n hC_nonneg hC hG_cutoff t ω

/-- Helper for Theorem 25.9: each moving-average cutoff row vanishes after the deterministic
horizon `T + 1 / (n + 1)`. -/
private theorem movingAverageCutoff_hasCutoff
    {G : Process} (T : NNReal) (n : ℕ)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∃ S : NNReal,
      ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, S < t → movingAverageCutoff G T n t ω = 0 := by
  refine ⟨T + 1 / (n + 1 : NNReal), ?_⟩
  intro t ω ht
  -- Proof comment: once time passes one full averaging window beyond `T`, the backward window is
  -- entirely inside the zero region of `G`.
  exact movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff (le_of_lt ht) ω

/-- Helper for Theorem 25.9: each fixed-time slice of a moving-average cutoff row is measurable
with respect to the corresponding filtration time. -/
private theorem movingAverageCutoff_measurable_fixedTime
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (t : NNReal) :
    Measurable[ℱ t] (fun ω ↦ movingAverageCutoff G T n t ω) := by
  by_cases ht : t ≤ T + (1 / (n + 1 : NNReal))
  · let a : ℝ := max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0
    let b : ℝ := min (t : ℝ) T
    let J : Set ℝ := Set.Ioc a b
    let νJ : Measure J := Measure.comap Subtype.val volume
    let g : Ω → J → ℝ := fun ω s ↦ G s.1.toNNReal ω
    letI : MeasurableSpace Ω := ℱ t
    have hstep_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by
      positivity
    have ht' : (t : ℝ) ≤ (T : ℝ) + 1 / (n + 1 : ℝ) := by
      exact_mod_cast ht
    have ha_nonneg : 0 ≤ a := by
      exact le_max_right _ _
    have hb_le_t : b ≤ (t : ℝ) := min_le_left _ _
    have ha_le_t : a ≤ (t : ℝ) := by
      refine max_le_iff.mpr ?_
      constructor
      · exact sub_le_self _ hstep_nonneg
      · exact_mod_cast bot_le
    have ha_le_T : a ≤ (T : ℝ) := by
      refine max_le_iff.mpr ?_
      constructor
      · linarith
      · exact_mod_cast bot_le
    have ha_le_b : a ≤ b := le_min ha_le_t ha_le_T
    let hJ : MeasurableEmbedding (Subtype.val : J → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ioc
    letI : IsFiniteMeasure νJ := by
      refine ⟨?_⟩
      calc
        νJ Set.univ = volume ((Subtype.val : J → ℝ) '' Set.univ) := by
          simpa [νJ] using hJ.comap_apply volume (Set.univ : Set J)
        _ = volume J := by simp
        _ < ∞ := by
          simpa [J] using (measure_Ioc_lt_top (μ := volume) (a := a) (b := b))
    have hstrip :
        StronglyMeasurable (fun p : Set.Iic t × Ω ↦ G p.1 p.2) :=
      hG_prog t
    have htime : Measurable (fun p : Ω × J ↦ (p.2.1 : ℝ)) :=
      measurable_snd.subtype_val
    have htimeNN : Measurable (fun p : Ω × J ↦ p.2.1.toNNReal) :=
      htime.real_toNNReal
    have htimeSub :
        Measurable
          (fun p : Ω × J ↦
            (⟨p.2.1.toNNReal, by
                refine Real.toNNReal_le_iff_le_coe.2 ?_
                exact le_trans p.2.2.2 hb_le_t⟩ : Set.Iic t)) :=
      htimeNN.subtype_mk
    have hmap :
        Measurable
          (fun p : Ω × J ↦
            ((⟨p.2.1.toNNReal, by
                refine Real.toNNReal_le_iff_le_coe.2 ?_
                exact le_trans p.2.2.2 hb_le_t⟩ : Set.Iic t), p.1)) :=
      htimeSub.prodMk measurable_fst
    have hg :
        Measurable (Function.uncurry g) := by
      -- Proof comment: on the active averaging window, the integrand is exactly the strip
      -- restriction of the progressively measurable process `G`.
      simpa [Function.uncurry, g] using hstrip.measurable.comp hmap
    have hgIntegral :
        StronglyMeasurable (fun ω : Ω ↦ ∫ s, g ω s ∂νJ) := by
      -- Proof comment: integration over the finite deterministic window preserves measurability
      -- of the sample-point parameter.
      simpa [Function.uncurry, g, νJ] using
        (MeasureTheory.StronglyMeasurable.integral_prod_right (ν := νJ) (f := g)
          hg.stronglyMeasurable)
    have hEq :
        (fun ω ↦ movingAverageCutoff G T n t ω) =
          fun ω ↦ ((n + 1 : ℝ)) * ∫ s, g ω s ∂νJ := by
      funext ω
      calc
        movingAverageCutoff G T n t ω
          = ((n + 1 : ℝ)) * ∫ s in a..b, G s.toNNReal ω := by
              simp [movingAverageCutoff, a, b]
        _ = ((n + 1 : ℝ)) * ∫ s in J, G s.toNNReal ω ∂volume := by
              congr 1
              simpa [J] using
                (intervalIntegral.integral_of_le ha_le_b :
                  ∫ s in a..b, G s.toNNReal ω = ∫ s in Set.Ioc a b, G s.toNNReal ω ∂volume)
        _ = ((n + 1 : ℝ)) * ∫ s, g ω s ∂νJ := by
              congr 1
              symm
              simpa [g, νJ, J] using
                (integral_subtype_comap (μ := volume) (s := J) measurableSet_Ioc
                  (fun s : ℝ ↦ G s.toNNReal ω))
    -- Proof comment: the explicit strip-integral representation turns the slice into a scalar
    -- multiple of a measurable Bochner integral.
    rw [hEq]
    exact measurable_const.mul hgIntegral.measurable
  · have hzero :
        ∀ ω : Ω, movingAverageCutoff G T n t ω = 0 := by
      intro ω
      exact movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff
        (le_of_lt (lt_of_not_ge ht)) ω
    -- Proof comment: outside the active averaging horizon, the fixed-time slice is identically
    -- zero and hence automatically measurable.
    simpa [hzero] using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))

 /-- Helper for Theorem 25.9: fixing the sample point of a progressively measurable process
 yields a measurable real-time path after composing time with `Real.toNNReal`. -/
private theorem measurable_realPath_of_progMeasurable
    {ℱ : ContinuousFiltration} {G : Process}
    (hG_prog : ProgMeasurable ℱ G) (ω : Ω) :
    Measurable (fun s : ℝ ↦ G s.toNNReal ω) := by
  have huncurry : Measurable (Function.uncurry G) :=
    MeasureTheory.ProgMeasurable.measurable_uncurry hG_prog
  have hpair : Measurable fun s : ℝ ↦ (s.toNNReal, ω) := by
    fun_prop
  -- Proof comment: fixing the sample coordinate turns the progressive joint measurability of `G`
  -- into measurability of the one-parameter path.
  simpa [Function.uncurry] using huncurry.comp hpair

/-- Helper for Theorem 25.9: every sample path of a moving-average cutoff row is continuous in
time. -/
private theorem movingAverageCutoff_continuousPath
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (ω : Ω) :
    Continuous fun t : NNReal ↦ movingAverageCutoff G T n t ω := by
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  let f : ℝ → ℝ := fun s ↦ G s.toNNReal ω
  have hf_meas : Measurable f := by
    -- Proof comment: reuse the fixed-sample measurability bridge for progressively measurable
    -- processes.
    simpa [f] using measurable_realPath_of_progMeasurable hG_prog ω
  have hf_loc : LocallyIntegrable f (volume : Measure ℝ) := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have hf_aestrong : AEStronglyMeasurable f volume := hf_meas.aestronglyMeasurable
    -- Proof comment: on each compact interval, the path is measurable and uniformly bounded by
    -- the global cutoff bound `C`, so it is Lebesgue integrable.
    refine
      Measure.integrableOn_of_bounded (μ := volume) (s := K) (M := C) hK.measure_lt_top.ne
        hf_aestrong ?_
    filter_upwards with s
    simpa [f, Real.norm_eq_abs] using hC s.toNNReal ω
  have hf_interval : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    exact (hf_loc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  let F : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, f s
  have hF_cont : Continuous F :=
    intervalIntegral.continuous_primitive hf_interval 0
  have hrepr :
      (fun t : NNReal ↦ movingAverageCutoff G T n t ω) =
        fun t : NNReal ↦
          (n + 1 : ℝ) *
            (F (min (t : ℝ) T) -
              F (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0)) := by
    funext t
    have hinterval :
        F (min (t : ℝ) T) - F (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) =
          ∫ s in max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0..min (t : ℝ) T, f s := by
      simpa [F] using
        intervalIntegral.integral_interval_sub_left
          (hf_interval (0 : ℝ) (min (t : ℝ) T))
          (hf_interval (0 : ℝ) (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0))
    -- Proof comment: the moving average is a fixed scalar multiple of the difference between two
    -- continuous primitive evaluations at the moving interval endpoints.
    calc
      movingAverageCutoff G T n t ω
        = (n + 1 : ℝ) *
            ∫ s in max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0..min (t : ℝ) T, f s := by
              simp [movingAverageCutoff, f]
      _ =
          (n + 1 : ℝ) *
            (F (min (t : ℝ) T) -
              F (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0)) := by
            rw [hinterval]
  rw [hrepr]
  -- Proof comment: continuity follows from the continuity of the primitive and the continuity of
  -- the endpoint maps `t ↦ min t T` and `t ↦ max (t - h) 0`.
  exact continuous_const.mul <|
    (hF_cont.comp (continuous_subtype_val.min continuous_const)).sub
      (hF_cont.comp ((continuous_subtype_val.sub continuous_const).max continuous_const))

/-- Helper for Theorem 25.9: every moving-average cutoff row is progressively measurable. -/
private theorem progMeasurable_movingAverageCutoff
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ProgMeasurable ℱ (movingAverageCutoff G T n) := by
  let hK_adapted : Adapted ℱ (movingAverageCutoff G T n) := by
    intro t
    exact movingAverageCutoff_measurable_fixedTime T n hG_prog hG_cutoff t
  -- Proof comment: fixed-time slice measurability gives adaptedness, and the already proved
  -- pathwise continuity upgrades that adaptedness to progressive measurability.
  exact hK_adapted.stronglyAdapted.progMeasurable_of_continuous
    (fun ω ↦ movingAverageCutoff_continuousPath T n hG_prog hG_bdd ω)

/-- Helper for Theorem 25.9: the ambient time-space realization of each moving-average cutoff row
is a.e.-strongly measurable under `processMeasure μ`. -/
private theorem aestronglyMeasurable_processToTimeSpaceFun_movingAverageCutoff
    {ℱ : ContinuousFiltration} (μ : Measure Ω) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    AEStronglyMeasurable (processToTimeSpaceFun (movingAverageCutoff G T n))
      (processMeasure μ) := by
  have huncurry : Measurable (Function.uncurry (movingAverageCutoff G T n)) :=
    (progMeasurable_movingAverageCutoff T n hG_prog hG_bdd hG_cutoff).measurable_uncurry
  have hswap : Measurable fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1) := by
    fun_prop
  -- Proof comment: `processToTimeSpaceFun` is exactly the measurable uncurry of the process after
  -- composing the time coordinate with `Real.toNNReal`.
  simpa [Function.uncurry, processToTimeSpaceFun] using
    (huncurry.comp hswap).aestronglyMeasurable

/-- Helper for Theorem 25.9: the backward mesh `x - 1 / (n + 1)` approaches `x` through the left
neighborhood filter `𝓝[<] x`. -/
private theorem tendsto_sub_inv_nat_nhdsWithin_left (x : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ x - 1 / (n + 1 : ℝ)) Filter.atTop (𝓝[<] x) := by
  have hto :
      Filter.Tendsto (fun n : ℕ ↦ x - 1 / (n + 1 : ℝ)) Filter.atTop (𝓝 x) := by
    -- Proof comment: the explicit mesh size `1 / (n + 1)` tends to `0`, so the shifted points
    -- converge to `x` in the ordinary neighborhood filter.
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 0)))
  refine Filter.tendsto_inf.2 ⟨hto, Filter.tendsto_principal.2 ?_⟩
  -- Proof comment: every mesh point stays strictly to the left of `x`, so the convergence lives in
  -- the left-sided neighborhood filter.
  exact Filter.Eventually.of_forall fun n ↦ by
    have hstep : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    exact sub_lt_self _ hstep

/-- Helper for Theorem 25.9: the left difference quotients of a differentiable primitive converge
to the derivative. -/
private theorem tendsto_backwardDifferenceQuotient_of_hasDerivAt
    {f F : ℝ → ℝ} {x : ℝ} (hF : HasDerivAt F (f x) x) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (F x - F (x - 1 / (n + 1 : ℝ))) / (1 / (n + 1 : ℝ)))
      Filter.atTop (𝓝 (f x)) := by
  rw [hasDerivAt_iff_tendsto_slope_left_right] at hF
  have hslope :
      Filter.Tendsto
        (fun n : ℕ ↦ slope F (x - 1 / (n + 1 : ℝ)) x)
        Filter.atTop (𝓝 (f x)) :=
    (hF.1.comp (tendsto_sub_inv_nat_nhdsWithin_left x)).congr'
      (Filter.Eventually.of_forall fun n ↦ by simp [slope_comm])
  refine hslope.congr' ?_
  -- Proof comment: along the explicit backward mesh, the slope formula is exactly the usual
  -- difference quotient.
  exact Filter.Eventually.of_forall fun n ↦ by
    have hden :
        x - (x - 1 / (n + 1 : ℝ)) = 1 / (n + 1 : ℝ) := by ring
    simp [slope_def_field, hden]

/-- Helper for Theorem 25.9: for a locally integrable real function on `ℝ`, the backward interval
averages over windows of size `1 / (n + 1)` converge almost everywhere to the function value. -/
private theorem ae_tendsto_backwardIntervalAverage_of_locallyIntegrable
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume,
      Filter.Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℝ)) * ∫ s in x - 1 / (n + 1 : ℝ)..x, f s)
        Filter.atTop (𝓝 (f x)) := by
  have hg : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    exact intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
  have hquot :
      Filter.Tendsto
        (fun n : ℕ ↦
          ((fun y : ℝ ↦ ∫ s in (0 : ℝ)..y, f s) x -
              (fun y : ℝ ↦ ∫ s in (0 : ℝ)..y, f s) (x - 1 / (n + 1 : ℝ))) /
            (1 / (n + 1 : ℝ)))
        Filter.atTop (𝓝 (f x)) :=
    tendsto_backwardDifferenceQuotient_of_hasDerivAt
      (f := f) (F := fun y : ℝ ↦ ∫ s in (0 : ℝ)..y, f s) (x := x) (hx 0)
  refine hquot.congr' ?_
  -- Proof comment: the primitive difference quotient is exactly the normalized backward interval
  -- average once the fundamental theorem spelling is expanded.
  exact Filter.Eventually.of_forall fun n ↦ by
    have hne : ((n + 1 : ℝ)) ≠ 0 := by positivity
    have hinterval :
        (∫ s in (0 : ℝ)..x, f s) - ∫ s in (0 : ℝ)..(x - 1 / (n + 1 : ℝ)), f s =
          ∫ s in x - 1 / (n + 1 : ℝ)..x, f s := by
      simpa using
        intervalIntegral.integral_interval_sub_left
          (hg (0 : ℝ) x) (hg (0 : ℝ) (x - 1 / (n + 1 : ℝ)))
    have hinterval' :
        (∫ s in (0 : ℝ)..x, f s) - ∫ s in (0 : ℝ)..(x - ((n + 1 : ℝ))⁻¹), f s =
          ∫ s in x - ((n + 1 : ℝ))⁻¹..x, f s := by
      simpa [one_div] using hinterval
    simpa [div_eq_mul_inv, one_div, inv_inv, hne, mul_comm] using hinterval'

/-- Helper for Theorem 25.9: a bounded progressively measurable real path is locally integrable on
`ℝ` after clamping time by `Real.toNNReal`. -/
private theorem locallyIntegrable_realPath_of_progMeasurable_bounded
    {ℱ : ContinuousFiltration} {G : Process}
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (ω : Ω) :
    LocallyIntegrable (fun s : ℝ ↦ G s.toNNReal ω) volume := by
  rcases hG_bdd with ⟨C, _, hC⟩
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  have hmeas : Measurable (fun s : ℝ ↦ G s.toNNReal ω) := by
    simpa [processToTimeSpaceFun] using measurable_realPath_of_progMeasurable hG_prog ω
  have hkfinite : volume k ≠ ∞ := hk.measure_lt_top.ne
  refine Measure.integrableOn_of_bounded (μ := volume) (s := k) (M := C) hkfinite
    hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hk.measurableSet]
  filter_upwards with s hs
  have hs_bound : |G s.toNNReal ω| ≤ C := hC s.toNNReal ω
  -- Proof comment: the global deterministic bound on `G` controls every real-time section after
  -- the `Real.toNNReal` clamp.
  simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hs_bound

/-- Helper for Theorem 25.9: for each sample point `ω`, the moving-average cutoff rows converge
for `dt`-almost every nonnegative time back to the bounded cutoff process. -/
private theorem ae_tendsto_processToTimeSpaceFun_movingAverageCutoff
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∀ ω : Ω,
      ∀ᵐ t ∂ ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))),
        Filter.Tendsto
          (fun n ↦ processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))
          Filter.atTop
          (𝓝 (processToTimeSpaceFun G (ω, t))) := by
  intro ω
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let avg : ℕ → ℝ → ℝ := fun n t ↦
    ((n + 1 : ℝ)) * ∫ s in t - 1 / (n + 1 : ℝ)..t, G s.toNNReal ω
  have havg_ae :
      ∀ᵐ t ∂ν, Filter.Tendsto (fun n ↦ avg n t) Filter.atTop (𝓝 (G t.toNNReal ω)) := by
    change
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))),
        Filter.Tendsto (fun n ↦ avg n t) Filter.atTop (𝓝 (G t.toNNReal ω))
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards
      [ae_tendsto_backwardIntervalAverage_of_locallyIntegrable
        (f := fun s : ℝ ↦ G s.toNNReal ω)
        (locallyIntegrable_realPath_of_progMeasurable_bounded hG_prog hG_bdd ω)] with t ht ht0
    -- Proof comment: on the nonnegative half-line, the one-dimensional differentiation theorem
    -- gives the backward-average limit for the real-time path `s ↦ G s.toNNReal ω`.
    simpa [avg] using ht
  have hzero_ae : ∀ᵐ t ∂ν, t ≠ 0 := by
    change ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))), t ≠ 0
    rw [ae_iff]
    simp [measurableSet_singleton]
  filter_upwards [havg_ae, ae_restrict_mem measurableSet_Ici, hzero_ae] with t htavg ht0 hzero
  by_cases ht : t ≤ T
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hzero)
    have hmesh :
        ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (n + 1) < t := by
      exact
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 (0 : ℝ))).eventually
          (Iio_mem_nhds ht_pos)
    -- Proof comment: for `t > 0` and `t ≤ T`, the moving-average window eventually becomes the
    -- ordinary backward interval `[t - 1 / (n + 1), t]`, so the section follows the real-path
    -- differentiation theorem.
    refine htavg.congr' ?_
    filter_upwards [hmesh] with n hn
    have hwindow_nonneg : 0 ≤ t - 1 / (n + 1 : ℝ) := by
      linarith
    have hmax0 : max t 0 = t := max_eq_left ht0
    have hmax : max (t - 1 / (n + 1 : ℝ)) 0 = t - 1 / (n + 1 : ℝ) :=
      max_eq_left hwindow_nonneg
    have hmin : min t T = t := min_eq_left ht
    -- Proof comment: on this branch the clipped averaging window is exactly the backward interval
    -- used in `avg`, so the two realizations agree pointwise for every sufficiently large mesh.
    dsimp [avg, processToTimeSpaceFun, movingAverageCutoff]
    rw [hmax0, hmax, hmin]
  · have hTt : (T : ℝ) < t := lt_of_not_ge ht
    have hδ : 0 < t - T := sub_pos.mpr hTt
    have hmesh :
        ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (n + 1) < t - T := by
      exact
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 (0 : ℝ))).eventually
          (Iio_mem_nhds hδ)
    have hGt_zero : processToTimeSpaceFun G (ω, t) = 0 := by
      have hTtNN : T < t.toNNReal := by
        rw [Real.toNNReal_of_nonneg ht0]
        exact hTt
      -- Proof comment: once the observation time lies strictly beyond `T`, the deterministic
      -- cutoff of `G` forces the target value itself to be zero.
      simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hG_cutoff hTtNN
    -- Proof comment: for `t > T`, the backward window eventually lies completely to the right of
    -- `T`, so every moving-average row is eventually identically zero.
    have hconst :
        Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop
          (𝓝 (processToTimeSpaceFun G (ω, t))) := by
      simpa [hGt_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0))
    refine hconst.congr' ?_
    filter_upwards [hmesh] with n hn
    have hineq : (T : ℝ) + 1 / (n + 1 : ℝ) ≤ t := by
      linarith
    have hineqNN : T + (1 / (n + 1 : NNReal)) ≤ t.toNNReal := by
      rw [Real.toNNReal_of_nonneg ht0]
      exact_mod_cast hineq
    have hz :
        movingAverageCutoff G T n t.toNNReal ω = 0 :=
      movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff hineqNN ω
    simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hz.symm

/-- Helper for Theorem 25.9: under an `SFinite` base measure, restricting `processMeasure μ` to a
deterministic time interval is exactly the corresponding product measure with restricted Lebesgue
time factor. -/
private theorem ae_tendsto_processToTimeSpaceFun_movingAverageCutoff_prod
    (μ : Measure Ω) {ℱ : ContinuousFiltration} {G : Process} (T : NNReal)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∀ᵐ x ∂ processMeasure μ,
      Filter.Tendsto
        (fun n ↦ processToTimeSpaceFun (movingAverageCutoff G T n) x)
        Filter.atTop
        (𝓝 (processToTimeSpaceFun G x)) := by
  let s : Set (Ω × ℝ) :=
    {x |
      Filter.Tendsto
        (fun n ↦ processToTimeSpaceFun (movingAverageCutoff G T n) x)
        Filter.atTop
        (𝓝 (processToTimeSpaceFun G x))}
  have hG_meas : Measurable (processToTimeSpaceFun G) := by
    have huncurry : Measurable (Function.uncurry G) :=
      MeasureTheory.ProgMeasurable.measurable_uncurry hG_prog
    have hswap : Measurable fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1) := by
      fun_prop
    -- Proof comment: the ambient realization is the progressively measurable uncurry composed with
    -- the nonnegative-time clamp on the second coordinate.
    simpa [Function.uncurry, processToTimeSpaceFun] using huncurry.comp hswap
  have hK_meas :
      ∀ n, Measurable (processToTimeSpaceFun (movingAverageCutoff G T n)) := by
    intro n
    have huncurry : Measurable (Function.uncurry (movingAverageCutoff G T n)) :=
      (progMeasurable_movingAverageCutoff T n hG_prog hG_bdd hG_cutoff).measurable_uncurry
    have hswap : Measurable fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1) := by
      fun_prop
    -- Proof comment: every moving-average row inherits the same measurable ambient realization.
    simpa [Function.uncurry, processToTimeSpaceFun] using huncurry.comp hswap
  have hs_meas : MeasurableSet s := by
    -- Proof comment: `measurableSet_tendsto_fun` upgrades pointwise convergence of measurable rows
    -- to a measurable convergence set on `Ω × ℝ`.
    simpa [s] using MeasureTheory.measurableSet_tendsto_fun hK_meas hG_meas
  rw [processMeasure, Measure.ae_prod_iff_ae_ae hs_meas]
  -- Proof comment: after rewriting `processMeasure μ` as the product measure on `Ω × [0,∞)`, the
  -- previously proved sectionwise a.e. convergence applies on each sample-time slice.
  exact Filter.Eventually.of_forall
    (ae_tendsto_processToTimeSpaceFun_movingAverageCutoff T hG_prog hG_bdd hG_cutoff)

/-- Helper for Theorem 25.9: under an `SFinite` base measure, restricting `processMeasure μ` to a
deterministic time interval is exactly the corresponding product measure with restricted Lebesgue
time factor. -/
private theorem processMeasure_restrict_eq_prod_Icc
    (μ : Measure Ω) [SFinite μ] (T : NNReal) :
    (processMeasure μ).restrict ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) (T : ℝ)) =
      μ.prod (volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))) := by
  have hsubset : Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    -- Proof comment: the deterministic time strip already lies inside the nonnegative-time half
    -- line used in the definition of `processMeasure`.
    intro t ht
    exact ht.1
  -- Proof comment: `processMeasure μ` is already a product measure, so restricting to
  -- `Ω × [0,T]` only restricts the time factor.
  rw [processMeasure, ← Measure.prod_restrict]
  simp [Measure.restrict_restrict, measurableSet_Icc, Set.inter_eq_left.mpr hsubset]

/-- Helper for Theorem 25.9: with an `SFinite` base measure, ambient `L²(processMeasure μ)`
control yields square-integrable time sections for `μ`-almost every sample point. -/
private theorem integrable_sq_timeSection_ae_of_memLp
    (μ : Measure Ω) [SFinite μ] {H : Process}
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    ∀ᵐ ω ∂μ,
      Integrable (fun t : ℝ ↦ (processToTimeSpaceFun H (ω, t)) ^ 2)
        ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  have hsq :
      Integrable (fun x : Ω × ℝ ↦ (processToTimeSpaceFun H x) ^ 2) (processMeasure μ) := by
    simpa using hH_memLp.integrable_sq
  -- Proof comment: after expanding `processMeasure`, Fubini gives the square-integrable time
  -- sections needed by the one-dimensional averaging theorem.
  simpa [processMeasure] using hsq.prod_right_ae

/-- Helper for Theorem 25.9: the ambient `L²(processMeasure μ)` norm of a process controls the
integrable row-energy function `ω ↦ ∫_0^∞ H_t(ω)^2 dt`. -/
private def sqRowEnergy (H : Process) : Ω → ℝ :=
  fun ω ↦ ∫ t in Set.Ici (0 : ℝ), (processToTimeSpaceFun H (ω, t)) ^ 2

/-- Helper for Theorem 25.9: the row energy of a predictable-step representation is the finite
weighted sum of its coefficient squares. -/
private theorem predictableStepRepresentation_sqRowEnergy_eq_sum
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ) (ω : Ω) :
    sqRowEnergy data.toProcess ω =
      ∑ i,
        (data.coeff i ω) ^ 2 *
          ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
  -- Proof comment: `sqRowEnergy` is exactly the time integral of the squared step process on
  -- `Set.Ici 0`, so the previously established interval-by-interval formula applies verbatim.
  simpa [sqRowEnergy] using predictableStepRepresentation_timeIntegralSq_eq_sum data ω

/-- Helper for Theorem 25.9: localizing a process by a sample-space indicator becomes an ambient
indicator on `Ω × ℝ` after passing to `processToTimeSpaceFun`. -/
private theorem processToTimeSpaceFun_sampleIndicator
    (A : Set Ω) (K : Process) :
    processToTimeSpaceFun (fun t ω ↦ Set.indicator A (fun ω ↦ K t ω) ω) =
      Set.indicator (A ×ˢ (Set.univ : Set ℝ)) (processToTimeSpaceFun K) := by
  funext x
  rcases x with ⟨ω, t⟩
  -- Proof comment: `processToTimeSpaceFun` only changes the time coordinate via `Real.toNNReal`,
  -- so sample-space localization is exactly the product-set indicator on the first coordinate.
  by_cases hω : ω ∈ A
  · simp [processToTimeSpaceFun, hω]
  · simp [processToTimeSpaceFun, hω]

/-- Helper for Theorem 25.9: sample-space localization commutes with the row-energy integral. -/
private theorem sqRowEnergy_sampleIndicator_eq
    (A : Set Ω) (K : Process) :
    sqRowEnergy (fun t ω ↦ Set.indicator A (fun ω ↦ K t ω) ω) =
      A.indicator (sqRowEnergy K) := by
  funext ω
  -- Proof comment: at a fixed sample point, the indicator is either the identity on the whole
  -- time row or the zero process on that row.
  by_cases hω : ω ∈ A
  · simp [sqRowEnergy, processToTimeSpaceFun, hω]
  · simp [sqRowEnergy, processToTimeSpaceFun, hω]

/-- Helper for Theorem 25.9: ambient square-integrability yields an integrable row-energy function
on `Ω`. -/
private theorem sqRowEnergy_integrable_of_memLp
    (μ : Measure Ω) {H : Process}
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    Integrable (sqRowEnergy H) μ := by
  let f : Ω × ℝ → ℝ := fun x ↦ (processToTimeSpaceFun H x) ^ 2
  have hf : Integrable f (processMeasure μ) := by
    simpa [f] using hH_memLp.integrable_sq
  -- Proof comment: `processMeasure μ` is the product measure `μ ⊗ dt` on `Ω × [0,∞)`, so
  -- `Integrable.integral_prod_left` turns the ambient square integral into an integrable
  -- row-energy function on `Ω`.
  simpa [sqRowEnergy, f, processMeasure] using hf.integral_prod_left

/-- Helper for Theorem 25.9: the ambient square integral of a sample-localized process is exactly
the `μ`-integral of the localized row energy. -/
private theorem sqIntegral_sampleIndicator_eq_rowEnergyIntegral
    (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) {K : Process}
    (hK_memLp : MemLp (processToTimeSpaceFun K) (2 : ℝ≥0∞) (processMeasure μ)) :
    ∫ x, (processToTimeSpaceFun (fun t ω ↦ Set.indicator A (fun ω ↦ K t ω) ω) x) ^ 2
        ∂ processMeasure μ =
      ∫ ω, A.indicator (sqRowEnergy K) ω ∂μ := by
  let Kloc : Process := fun t ω ↦ Set.indicator A (fun ω ↦ K t ω) ω
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let f : Ω × ℝ → ℝ := fun x ↦ (processToTimeSpaceFun Kloc x) ^ 2
  have hKloc_memLp :
      MemLp (processToTimeSpaceFun Kloc) (2 : ℝ≥0∞) (processMeasure μ) := by
    -- Proof comment: after rewriting the localized process in ambient coordinates, this is just
    -- the standard `MemLp.indicator` constructor on the measurable set `A × ℝ`.
    rw [processToTimeSpaceFun_sampleIndicator A K]
    exact MemLp.indicator (hA.prod MeasurableSet.univ) hK_memLp
  have hsq_int : Integrable f (μ.prod ν) := by
    simpa using hKloc_memLp.integrable_sq
  have hrow_int :
      ∀ᵐ ω ∂μ, Integrable (fun t : ℝ ↦ f (ω, t)) ν := by
    -- Proof comment: the ambient square-integrable function has integrable time rows for `μ`-a.e.
    -- sample point by the product-space characterization of integrability.
    exact ((integrable_prod_iff hsq_int.aestronglyMeasurable).mp hsq_int).1
  have hsqRow_nonneg : 0 ≤ᵐ[μ] sqRowEnergy Kloc := by
    -- Proof comment: each row energy is an integral of a pointwise nonnegative square.
    filter_upwards [hrow_int] with ω hω
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg (processToTimeSpaceFun Kloc (ω, t)))
  have hrow_lintegral :
      (fun ω ↦ ENNReal.ofReal (sqRowEnergy Kloc ω)) =ᵐ[μ]
        fun ω ↦ ∫⁻ t, ENNReal.ofReal (f (ω, t)) ∂ν := by
    -- Proof comment: on the a.e. integrable rows furnished above, the row energy is exactly the
    -- ordinary integral corresponding to the nonnegative `ENNReal` row integral.
    filter_upwards [hrow_int] with ω hω
    simpa [sqRowEnergy, f, ν] using
      (ofReal_integral_eq_lintegral_ofReal
        (μ := ν) hω
        (Filter.Eventually.of_forall fun t ↦ sq_nonneg (processToTimeSpaceFun Kloc (ω, t))))
  have hleft_nonneg :
      0 ≤ ∫ x, (processToTimeSpaceFun Kloc x) ^ 2 ∂ processMeasure μ := by
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (processToTimeSpaceFun Kloc x))
  have hright_nonneg :
      0 ≤ ∫ ω, A.indicator (sqRowEnergy K) ω ∂μ := by
    rw [← sqRowEnergy_sampleIndicator_eq A K]
    exact integral_nonneg_of_ae hsqRow_nonneg
  rw [← ENNReal.ofReal_eq_ofReal_iff hleft_nonneg hright_nonneg]
  calc
    ENNReal.ofReal
        (∫ x, (processToTimeSpaceFun Kloc x) ^ 2 ∂ processMeasure μ) =
        ∫⁻ x, ENNReal.ofReal (f x) ∂μ.prod ν := by
          -- Proof comment: convert the ambient square integral to the corresponding nonnegative
          -- `ENNReal` integral before applying Tonelli.
          simpa [f, processMeasure, ν] using
            (ofReal_integral_eq_lintegral_ofReal
              (μ := processMeasure μ) hKloc_memLp.integrable_sq
              (Filter.Eventually.of_forall fun x ↦ sq_nonneg (processToTimeSpaceFun Kloc x)))
    _ = ∫⁻ ω, ∫⁻ t, ENNReal.ofReal (f (ω, t)) ∂ν ∂μ := by
          -- Proof comment: Tonelli now moves the nonnegative square from the ambient product
          -- measure to iterated row integrals without any `[SFinite μ]` assumption.
          exact lintegral_prod _ hsq_int.aemeasurable.ennreal_ofReal
    _ = ∫⁻ ω, ENNReal.ofReal (sqRowEnergy Kloc ω) ∂μ := by
          exact lintegral_congr_ae hrow_lintegral.symm
    _ = ENNReal.ofReal (∫ ω, A.indicator (sqRowEnergy K) ω ∂μ) := by
          -- Proof comment: rewrite the row energy of the localized process back to the sample-space
          -- indicator form and convert the outer integral to its `ENNReal` counterpart.
          have hrowIntA : Integrable (A.indicator (sqRowEnergy K)) μ := by
            have htmp : Integrable (sqRowEnergy Kloc) μ :=
              sqRowEnergy_integrable_of_memLp μ hKloc_memLp
            rwa [sqRowEnergy_sampleIndicator_eq A K] at htmp
          have hrowNonnegA : 0 ≤ᵐ[μ] A.indicator (sqRowEnergy K) := by
            have htmp : 0 ≤ᵐ[μ] sqRowEnergy Kloc := hsqRow_nonneg
            rwa [sqRowEnergy_sampleIndicator_eq A K] at htmp
          rw [sqRowEnergy_sampleIndicator_eq A K]
          symm
          exact ofReal_integral_eq_lintegral_ofReal
            (μ := μ)
            hrowIntA hrowNonnegA

/-- Helper for Theorem 25.9: the ambient square integral of a process is exactly the outer
integral of its row-energy function. -/
private theorem integral_sq_process_eq_integral_sqRowEnergy
    (μ : Measure Ω) {K : Process}
    (hK_memLp : MemLp (processToTimeSpaceFun K) (2 : ℝ≥0∞) (processMeasure μ)) :
    ∫ x, (processToTimeSpaceFun K x) ^ 2 ∂ processMeasure μ =
      ∫ ω, sqRowEnergy K ω ∂μ := by
  -- Proof comment: `sqIntegral_sampleIndicator_eq_rowEnergyIntegral` already identifies the
  -- ambient square integral with the localized row-energy integral, and taking the localization
  -- set to be `univ` removes the indicator on both sides.
  simpa using
    (sqIntegral_sampleIndicator_eq_rowEnergyIntegral
      (μ := μ) (A := Set.univ) MeasurableSet.univ (K := K) hK_memLp)

/-- Helper for Theorem 25.9: ambient square-integrability lets us localize the row energy of a
process to a finite-measure subset of `Ω`. -/
private theorem sqRowEnergy_exists_finiteLocalization_of_memLp
    (μ : Measure Ω) {H : Process}
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ∞ ∧ eLpNorm (Aᶜ.indicator (sqRowEnergy H)) 1 μ < ε := by
  have hRowEnergy_memLp : MemLp (sqRowEnergy H) 1 μ := by
    rw [memLp_one_iff_integrable]
    exact sqRowEnergy_integrable_of_memLp μ hH_memLp
  -- Proof comment: the scalar row-energy function is an `L¹(μ)` object, so the standard finite
  -- localization lemma produces a finite-measure subset of `Ω` with arbitrarily small tail.
  exact hRowEnergy_memLp.exists_eLpNorm_indicator_compl_lt (by simp) hε

/-- Helper for Theorem 25.9: one finite-measure sample localization can control the `L²(μ)` tails
of a finite family of functions simultaneously. -/
private theorem exists_finiteLocalization_of_finset_memLp
    (μ : Measure Ω) {ι : Type*} (s : Finset ι) {F : ι → Ω → ℝ}
    (hF : ∀ i ∈ s, MemLp (F i) (2 : ℝ≥0∞) μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ∞ ∧
      ∀ i ∈ s, eLpNorm (Aᶜ.indicator (F i)) (2 : ℝ≥0∞) μ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
      intro i hi
      simp at hi
  | @insert i s hi ih =>
      rcases ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)) with
        ⟨A, hA_meas, hA_fin, hA_tail⟩
      rcases
          (hF i (Finset.mem_insert_self i s)).exists_eLpNorm_indicator_compl_lt
            (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε with
        ⟨B, hB_meas, hB_fin, hB_tail⟩
      refine ⟨A ∪ B, hA_meas.union hB_meas, ?_, ?_⟩
      · -- Proof comment: a finite union of finite-measure localizations still has finite measure.
        calc
          μ (A ∪ B) ≤ μ A + μ B := measure_union_le A B
          _ < ∞ := ENNReal.add_lt_top.2 ⟨hA_fin, hB_fin⟩
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · -- Proof comment: enlarging the localization can only shrink the complement tail for the
          -- distinguished coefficient indexed by the newly inserted element.
          refine lt_of_le_of_lt (eLpNorm_mono fun ω ↦ ?_) hB_tail
          by_cases hω : ω ∈ (A ∪ B)ᶜ
          · have hωB : ω ∈ Bᶜ := by
              exact by
                have hωAB : ω ∉ A ∧ ω ∉ B := by
                  simpa [Set.mem_compl, not_or] using hω
                simpa [Set.mem_compl] using hωAB.2
            have hωA : ω ∈ Aᶜ := by
              exact by
                have hωAB : ω ∉ A ∧ ω ∉ B := by
                  simpa [Set.mem_compl, not_or] using hω
                simpa [Set.mem_compl] using hωAB.1
            simp [Set.indicator_apply, hω, hωA, hωB]
          · by_cases hωB : ω ∈ B
            · simp [Set.indicator_apply, hω, hωB]
            · by_cases hωA : ω ∈ A
              · simp [Set.indicator_apply, hω, hωA, hωB]
              · exfalso
                apply hω
                simpa [Set.mem_compl, hωA, hωB]
        · -- Proof comment: the same monotonicity argument preserves the previously established
          -- tail bound for every older coefficient in the finite family.
          refine lt_of_le_of_lt (eLpNorm_mono fun ω ↦ ?_) (hA_tail j hj)
          by_cases hω : ω ∈ (A ∪ B)ᶜ
          · have hωA : ω ∈ Aᶜ := by
              exact by
                have hωAB : ω ∉ A ∧ ω ∉ B := by
                  simpa [Set.mem_compl, not_or] using hω
                simpa [Set.mem_compl] using hωAB.1
            have hωB : ω ∈ Bᶜ := by
              exact by
                have hωAB : ω ∉ A ∧ ω ∉ B := by
                  simpa [Set.mem_compl, not_or] using hω
                simpa [Set.mem_compl] using hωAB.2
            simp [Set.indicator_apply, hω, hωA, hωB]
          · by_cases hωA : ω ∈ A
            · simp [Set.indicator_apply, hω, hωA]
            · by_cases hωB : ω ∈ B
              · simp [Set.indicator_apply, hω, hωA, hωB]
              · exfalso
                apply hω
                simpa [Set.mem_compl, hωA, hωB]

/-- Helper for Theorem 25.9: on a finite-measure sample-space localization, a bounded measurable
slice automatically belongs to `L²(μ)`, and the ambient version is the corresponding indicator. -/
private theorem memLp_indicator_of_bound_of_finiteMeasure
    (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) (hA_fin : μ A < ∞)
    {f : Ω → ℝ} (hf_aesm : AEStronglyMeasurable f (μ.restrict A))
    {C : ℝ} (hbound : ∀ ⦃ω : Ω⦄, ω ∈ A → |f ω| ≤ C) :
    MemLp (A.indicator f) (2 : ℝ≥0∞) μ := by
  letI : Fact (μ A < ∞) := ⟨hA_fin⟩
  rw [memLp_indicator_iff_restrict hA]
  have hbound_restrict : ∀ᵐ ω ∂μ.restrict A, ‖f ω‖ ≤ C := by
    rw [ae_restrict_iff' hA]
    exact Filter.Eventually.of_forall fun ω hω ↦ by
      simpa [Real.norm_eq_abs] using hbound hω
  -- Proof comment: after passing to the finite restricted measure, the uniform bound puts the
  -- slice directly in `L²`; `memLp_indicator_iff_restrict` then transports it back to `μ`.
  exact MemLp.of_bound hf_aesm C hbound_restrict

/-- Helper for Theorem 25.9: if the squared time rows are integrable for `μ`-almost every sample
point and the resulting row-energy function is integrable on `Ω`, then the process lies in ambient
`L²(processMeasure μ)`. -/
private theorem memLp_of_sqRowEnergy_integrable
    (μ : Measure Ω) {K : Process}
    (hK_aesm : AEStronglyMeasurable (processToTimeSpaceFun K) (processMeasure μ))
    (hrow_int :
      ∀ᵐ ω ∂μ,
        Integrable (fun t : ℝ ↦ (processToTimeSpaceFun K (ω, t)) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))))
    (hRowEnergy_int : Integrable (sqRowEnergy K) μ) :
    MemLp (processToTimeSpaceFun K) (2 : ℝ≥0∞) (processMeasure μ) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let f : Ω × ℝ → ℝ := fun x ↦ (processToTimeSpaceFun K x) ^ 2
  have hf_aesm : AEStronglyMeasurable f (μ.prod ν) := by
    -- Proof comment: squaring preserves ambient a.e.-strong measurability of the time-space
    -- realization.
    simpa [f, processMeasure, ν] using hK_aesm.pow 2
  have houter_eq :
      (fun ω ↦ ∫ t, ‖f (ω, t)‖ ∂ν) =ᵐ[μ] sqRowEnergy K := by
    -- Proof comment: on each integrable row, the outer norm integral is exactly the row-energy
    -- integral because the squared integrand is pointwise nonnegative.
    filter_upwards [hrow_int] with ω hω
    calc
      ∫ t, ‖f (ω, t)‖ ∂ν = ∫ t, f (ω, t) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards with t
        simp [f, sq_nonneg (processToTimeSpaceFun K (ω, t))]
      _ = sqRowEnergy K ω := by
        simp [sqRowEnergy, f, ν]
  have houter_int : Integrable (fun ω ↦ ∫ t, ‖f (ω, t)‖ ∂ν) μ := by
    exact hRowEnergy_int.congr houter_eq.symm
  have hf_int : Integrable f (μ.prod ν) := by
    -- Proof comment: the product-space integrability criterion packages the rowwise integrability
    -- and the scalar row-energy control into ambient integrability of the square.
    exact (integrable_prod_iff hf_aesm).2 ⟨by simpa [f, ν] using hrow_int, houter_int⟩
  -- Proof comment: once the square is integrable in the ambient product measure, the standard
  -- `MemLp` characterization at exponent `2` finishes the transport back to `L²`.
  refine (memLp_two_iff_integrable_sq hK_aesm).2 ?_
  simpa [f, processMeasure, ν] using hf_int

/-- Helper for Theorem 25.9: a bounded process with deterministic cutoff has square-integrable
sample paths on `Set.Ici 0`. -/
private theorem integrable_sq_realPath_on_Ici_of_bound_cutoff
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    Integrable
      (fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2)
      ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let f : ℝ → ℝ := fun s ↦ (processToTimeSpaceFun G (ω, s)) ^ 2
  have hf_meas : Measurable f := by
    -- Proof comment: fixing the sample point turns progressive measurability into measurability
    -- of the squared real-time path.
    simpa [f, processToTimeSpaceFun, sq] using
      (measurable_realPath_of_progMeasurable hG_prog ω).mul
        (measurable_realPath_of_progMeasurable hG_prog ω)
  have hf_aesm : AEStronglyMeasurable f ν := hf_meas.aestronglyMeasurable
  have hIcc_int : IntegrableOn f (Set.Icc (0 : ℝ) T) ν := by
    have hsubset : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := by
      intro s hs
      exact hs.1
    have hfinite : ν (Set.Icc (0 : ℝ) T) ≠ ∞ := by
      simpa [ν, Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.2 hsubset] using
        (ne_of_lt (measure_Icc_lt_top (a := (0 : ℝ)) (b := (T : ℝ))))
    refine
      Measure.integrableOn_of_bounded
        (μ := ν) (s := Set.Icc (0 : ℝ) T) (M := C ^ 2) hfinite hf_aesm ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun s hs ↦ by
      have hs_nonneg : 0 ≤ s := hs.1
      have hsq :
          (processToTimeSpaceFun G (ω, s)) ^ 2 ≤ C ^ 2 := by
        have habs : |processToTimeSpaceFun G (ω, s)| ≤ C := by
          simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg hs_nonneg] using hC s.toNNReal ω
        have hx := abs_le.mp habs
        nlinarith [hx.1, hx.2]
      have hnonneg : 0 ≤ f s := sq_nonneg _
      simpa [f, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hsq
  have hEq :
      Set.indicator (Set.Icc (0 : ℝ) T) f =ᵐ[ν] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs_nonneg
    have hs_nonneg' : 0 ≤ s := hs_nonneg
    by_cases hsT : s ≤ T
    · have hs_mem : s ∈ Set.Icc (0 : ℝ) T := ⟨hs_nonneg', hsT⟩
      simp [f, hs_mem]
    · have hs_gt : T < s := lt_of_not_ge hsT
      have hzero : processToTimeSpaceFun G (ω, s) = 0 := by
        have hs_gt_nn : T < s.toNNReal := (Real.lt_toNNReal_iff_coe_lt).2 hs_gt
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg hs_nonneg'] using
          hG_cutoff (ω := ω) hs_gt_nn
      have hzero' : G s.toNNReal ω = 0 := by
        simpa [processToTimeSpaceFun] using hzero
      have hs_not_mem : s ∉ Set.Icc (0 : ℝ) T := by simp [hsT]
      simp [f, hs_not_mem, hzero']
  -- Proof comment: on `Set.Ici 0`, the cutoff makes the path vanish after time `T`, so the whole
  -- row is the indicator of its bounded part on `Set.Icc 0 T`.
  exact (hIcc_int.integrable_indicator measurableSet_Icc).congr hEq

/-- Helper for Theorem 25.9: each moving-average value is controlled by the square integral on its
backward window. -/
private theorem movingAverageCutoff_sq_le_windowSqIntegral_of_le_cutoffWindow
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    {t : NNReal} (ht : t ≤ T + (1 / (n + 1 : NNReal))) (ω : Ω) :
    (movingAverageCutoff G T n t ω) ^ 2 ≤
      (n + 1 : ℝ) *
        ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
          (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  let a : ℝ := max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0
  let b : ℝ := min (t : ℝ) T
  let J : Set ℝ := Set.uIoc a b
  let f : ℝ → ℝ := fun s ↦ |G s.toNNReal ω|
  let B : ℝ := ∫ s in J, (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume
  have hstep_nonneg : 0 ≤ (1 / (n + 1 : ℝ)) := by
    positivity
  have ht' : (t : ℝ) ≤ (T : ℝ) + 1 / (n + 1 : ℝ) := by
    exact_mod_cast ht
  have ht_nonneg : 0 ≤ (t : ℝ) := by
    exact_mod_cast bot_le
  have ha_le_t : a ≤ (t : ℝ) := by
    refine max_le_iff.mpr ?_
    constructor
    · linarith
    · simpa using ht_nonneg
  have ha_le_T : a ≤ (T : ℝ) := by
    refine max_le_iff.mpr ?_
    constructor
    · linarith
    · exact show (0 : ℝ) ≤ (T : ℝ) by exact_mod_cast bot_le
  have ha_le_b : a ≤ b := le_min ha_le_t ha_le_T
  have hwindowLeft_le_a : (t : ℝ) - 1 / (n + 1 : ℝ) ≤ a := le_max_left _ _
  have hb_le_t : b ≤ (t : ℝ) := min_le_left _ _
  have hlength : b - a ≤ 1 / (n + 1 : ℝ) := by
    have h₁ : b - a ≤ (t : ℝ) - a := sub_le_sub_right hb_le_t a
    have h₂ : (t : ℝ) - a ≤ (t : ℝ) - ((t : ℝ) - 1 / (n + 1 : ℝ)) := by
      exact sub_le_sub_left hwindowLeft_le_a (t : ℝ)
    linarith
  by_cases hab : a = b
  · have hintegral : ∫ s in a..b, G s.toNNReal ω = 0 := by
      simp [hab]
    have havg_zero : movingAverageCutoff G T n t ω = 0 := by
      have hdef :
          movingAverageCutoff G T n t ω = ((n + 1 : ℝ)) * ∫ s in a..b, G s.toNNReal ω := by
        simp [movingAverageCutoff, a, b]
      rw [hdef, hintegral, mul_zero]
    have hwindow : B = 0 := by
      simp [B, J, hab]
    have hwindow_nonneg :
        0 ≤
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
      have hfactor_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
      have hwindow_int :
          ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume = 0 := by
        simpa [B, J, a, b] using hwindow
      rw [hwindow_int]
      positivity
    -- Proof comment: on the degenerate active window both the moving average and the square
    -- integral vanish identically.
    simpa [havg_zero] using hwindow_nonneg
  · have hab_lt : a < b := lt_of_le_of_ne ha_le_b hab
    have hba : b ≠ a := by
      intro h
      exact hab h.symm
    have hm_ne : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr hba
    have hf_meas : Measurable f := by
      -- Proof comment: fixing the sample point turns the progressively measurable process into a
      -- measurable real-time path; taking the absolute value preserves measurability.
      simpa [f, Real.norm_eq_abs] using (measurable_realPath_of_progMeasurable hG_prog ω).norm
    have hf_sq_meas : Measurable (fun s : ℝ ↦ f s ^ 2) := hf_meas.pow_const 2
    have hJ_nonzero : volume J ≠ 0 := by
      simpa [J, Set.uIoc_of_le ha_le_b, Real.volume_Ioc, ENNReal.ofReal_eq_zero] using
        (sub_pos.mpr hab_lt)
    have hJ_finite : volume J ≠ ∞ := by
      simp [J, Set.uIoc_of_le ha_le_b, Real.volume_Ioc]
    have hf_int : IntegrableOn f J volume := by
      refine
        Measure.integrableOn_of_bounded (μ := volume) (s := J) (M := C) hJ_finite
          hf_meas.aestronglyMeasurable ?_
      filter_upwards with s
      -- Proof comment: the original cutoff bound controls the absolute-value path on every point
      -- of the deterministic window.
      simpa [f, Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hC s.toNNReal ω
    have hf_sq_int : IntegrableOn (fun s : ℝ ↦ f s ^ 2) J volume := by
      refine
        Measure.integrableOn_of_bounded (μ := volume) (s := J) (M := C ^ 2) hJ_finite
          hf_sq_meas.aestronglyMeasurable ?_
      filter_upwards with s
      have hs : f s ≤ C := by
        simpa [f] using hC s.toNNReal ω
      have hs_nonneg : 0 ≤ f s := abs_nonneg _
      have hsq : f s ^ 2 ≤ C ^ 2 := by
        nlinarith [hC_nonneg, hs, hs_nonneg]
      have hsq_nonneg : 0 ≤ f s ^ 2 := sq_nonneg _
      -- Proof comment: squaring preserves the deterministic bound on the active window.
      simpa [Real.norm_eq_abs, abs_of_nonneg hsq_nonneg] using hsq
    have hf_nonneg :
        ∀ᵐ s ∂volume.restrict J, f s ∈ Set.Ici (0 : ℝ) := by
      exact Filter.Eventually.of_forall fun s ↦ by
        show 0 ≤ f s
        exact abs_nonneg _
    have havg_sq :
        (⨍ s in J, f s ∂volume) ^ 2 ≤ ⨍ s in J, f s ^ 2 ∂volume := by
      -- Proof comment: Jensen on the convex function `x ↦ x²` upgrades the average of `|G|` on the
      -- finite window to the average of the square.
      simpa using
        (convexOn_pow (𝕜 := ℝ) (n := 2) :
          ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ 2)).map_set_average_le
          ((continuous_id'.pow 2).continuousOn) isClosed_Ici hJ_nonzero hJ_finite
          hf_nonneg hf_int hf_sq_int
    have hmeasure_real : volume.real J = b - a := by
      simp [measureReal_def, J, Set.uIoc_of_le ha_le_b, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr ha_le_b)]
    let A : ℝ := ∫ s in J, f s ∂volume
    let Q : ℝ := ∫ s in J, f s ^ 2 ∂volume
    have htmp :
        (A / (b - a)) ^ 2 ≤ Q / (b - a) := by
      simpa [A, Q, setAverage_eq, hmeasure_real, smul_eq_mul, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using havg_sq
    have hwindow_sq :
        A ^ 2 ≤ (b - a) * Q := by
      have hm_pos : 0 < b - a := sub_pos.mpr hab_lt
      have htmp' := mul_le_mul_of_nonneg_right htmp hm_pos.le
      field_simp [hm_ne] at htmp'
      simpa [A, Q, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp'
    have hnorm :
        |∫ s in a..b, G s.toNNReal ω| ≤ ∫ s in J, f s ∂volume := by
      -- Proof comment: the absolute interval integral is bounded by the integral of the absolute
      -- value over the same `uIoc` window.
      simpa [J, f, Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc
          (μ := volume) (f := fun s : ℝ ↦ G s.toNNReal ω) (a := a) (b := b))
    have hbounds :
        -(∫ s in J, f s ∂volume) ≤ ∫ s in a..b, G s.toNNReal ω ∧
          ∫ s in a..b, G s.toNNReal ω ≤ ∫ s in J, f s ∂volume := by
      exact abs_le.mp hnorm
    have hB_eq :
        ∫ s in J, f s ^ 2 ∂volume = B := by
      simp [B, J, f, sq_abs]
    have hint_sq :
        (∫ s in a..b, G s.toNNReal ω) ^ 2 ≤ (b - a) * B := by
      have hnorm_sq :
          (∫ s in a..b, G s.toNNReal ω) ^ 2 ≤ (∫ s in J, f s ∂volume) ^ 2 := by
        nlinarith [hbounds.1, hbounds.2]
      exact hnorm_sq.trans <| by simpa [A, Q, hB_eq] using hwindow_sq
    have hB_nonneg : 0 ≤ B := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s ↦ sq_nonneg _)
    have hfactor_nonneg : 0 ≤ (n + 1 : ℝ) := by
      positivity
    -- Proof comment: the window has length at most `1 / (n + 1)`, so scaling by the averaging
    -- factor converts the Jensen bound into the claimed square estimate.
    calc
      (movingAverageCutoff G T n t ω) ^ 2
          = ((n + 1 : ℝ) * ∫ s in a..b, G s.toNNReal ω) ^ 2 := by
              simp [movingAverageCutoff, a, b]
      _ = (n + 1 : ℝ) ^ 2 * (∫ s in a..b, G s.toNNReal ω) ^ 2 := by
            ring
      _ ≤ (n + 1 : ℝ) ^ 2 * ((b - a) * B) := by
            gcongr
      _ ≤ (n + 1 : ℝ) ^ 2 * ((1 / (n + 1 : ℝ)) * B) := by
            gcongr
      _ = (n + 1 : ℝ) * B := by
            have hfactor_ne : (n + 1 : ℝ) ≠ 0 := by positivity
            field_simp [hfactor_ne]
      _ =
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
            simp [B, J, a, b]

/-- Helper for Theorem 25.9: each moving-average value is controlled by the square integral on its
backward window. -/
private theorem movingAverageCutoff_sq_le_windowSqIntegral
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (t : NNReal) (ω : Ω) :
    (movingAverageCutoff G T n t ω) ^ 2 ≤
      (n + 1 : ℝ) *
        ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
          (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
  by_cases ht : t ≤ T + (1 / (n + 1 : NNReal))
  · -- Proof comment: before the deterministic cutoff window expires, the active-window Jensen
    -- estimate gives the required square bound directly.
    exact movingAverageCutoff_sq_le_windowSqIntegral_of_le_cutoffWindow
      T n hG_prog hG_bdd ht ω
  · have hzero :
        movingAverageCutoff G T n t ω = 0 :=
      movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff
        (le_of_lt (lt_of_not_ge ht)) ω
    have hfactor_nonneg : 0 ≤ (n + 1 : ℝ) := by
      positivity
    have hnonneg :
        0 ≤
          ∫ s in Set.uIoc (max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0) (min (t : ℝ) T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s ↦ sq_nonneg _)
    -- Proof comment: once the whole backward window lies past the cutoff horizon, the moving
    -- average vanishes and only the nonnegativity of the square integral remains.
    simpa [hzero] using mul_nonneg hfactor_nonneg hnonneg

/-- Helper for Theorem 25.9: every deterministic moving-average slice is pointwise dominated by
the row energy of `G`. -/
private theorem movingAverageCutoff_fixedTime_sq_le_rowEnergy
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (t : NNReal) (ω : Ω) :
    (movingAverageCutoff G T n t ω) ^ 2 ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
  let a : ℝ := max ((t : ℝ) - 1 / (n + 1 : ℝ)) 0
  let b : ℝ := min (t : ℝ) T
  have hwindow_le :
      ∫ s in Set.uIoc a b, (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ≤
        sqRowEnergy G ω := by
    have ha_nonneg : 0 ≤ a := by
      exact le_max_right _ _
    have hb_nonneg : 0 ≤ b := by
      refine le_min ?_ ?_
      · exact_mod_cast bot_le
      · exact_mod_cast bot_le
    have hsubset : Set.uIoc a b ⊆ Set.Ici (0 : ℝ) := by
      intro s hs
      have hs' : s ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hs
      rw [Set.mem_uIcc] at hs'
      rcases hs' with hs' | hs'
      · exact le_trans ha_nonneg hs'.1
      · exact le_trans hb_nonneg hs'.1
    have hrow_int :
        Integrable (fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
      simpa using integrable_sq_realPath_on_Ici_of_bound_cutoff T hG_prog hG_bdd hG_cutoff ω
    have hsq_nonneg :
        0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))]
          fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2 := by
      exact Filter.Eventually.of_forall fun s ↦ sq_nonneg _
    -- Proof comment: the fixed backward window sits inside `Set.Ici 0`, so its square integral
    -- is bounded by the full row energy of `G`.
    simpa [sqRowEnergy, a, b] using
      (integral_mono_measure
        (Measure.restrict_mono hsubset le_rfl) hsq_nonneg hrow_int :
          ∫ s, (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume.restrict (Set.uIoc a b) ≤
            ∫ s, (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume.restrict (Set.Ici (0 : ℝ)))
  have hsq :=
    movingAverageCutoff_sq_le_windowSqIntegral T n hG_prog hG_bdd hG_cutoff t ω
  -- Proof comment: first control the slice by the square integral on its own averaging window,
  -- then enlarge that window to the whole row energy on `[0, ∞)`.
  calc
    (movingAverageCutoff G T n t ω) ^ 2
        ≤
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc a b, (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
              simpa [a, b] using hsq
    _ ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
          gcongr

/-- Helper for Theorem 25.9: localizing a deterministic moving-average slice to a measurable
sample-space set is controlled by the same localization of the row energy of `G`. -/
private theorem movingAverageCutoff_fixedTime_sqIntegral_on_set_le
    {ℱ : ContinuousFiltration} (μ : Measure Ω) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    {A : Set Ω} (hA : MeasurableSet A) (t : NNReal) :
    ∫ ω, A.indicator (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2) ω ∂μ ≤
      (n + 1 : ℝ) * ∫ ω, A.indicator (sqRowEnergy G) ω ∂μ := by
  have hRowEnergy_int : Integrable (sqRowEnergy G) μ :=
    sqRowEnergy_integrable_of_memLp μ hG_memLp
  have hright_int :
      Integrable (A.indicator (fun ω ↦ (n + 1 : ℝ) * sqRowEnergy G ω)) μ := by
    exact (hRowEnergy_int.const_mul (n + 1 : ℝ)).indicator hA
  have hslice_meas :
      Measurable (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2) :=
    (movingAverageCutoff_measurable_fixedTime T n hG_prog hG_cutoff t).mono (ℱ.le _) le_rfl |>.pow_const 2
  have hleft_int :
      Integrable (A.indicator (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2)) μ := by
    refine hright_int.mono' ((hslice_meas.indicator hA).aestronglyMeasurable) ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · have hpoint :=
        movingAverageCutoff_fixedTime_sq_le_rowEnergy T n hG_prog hG_bdd hG_cutoff t ω
      have hleft_nonneg : 0 ≤ (movingAverageCutoff G T n t ω) ^ 2 := sq_nonneg _
      have hright_nonneg : 0 ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
        refine mul_nonneg (by positivity) ?_
        exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s ↦ sq_nonneg _)
      simpa [Set.indicator_of_mem, hω, Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
        abs_of_nonneg hright_nonneg] using hpoint
    · simp [Set.indicator_of_notMem, hω]
  have hpointwise :
      ∀ᵐ ω ∂μ,
        A.indicator (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2) ω ≤
          A.indicator (fun ω ↦ (n + 1 : ℝ) * sqRowEnergy G ω) ω := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · simpa [Set.indicator_of_mem, hω] using
        movingAverageCutoff_fixedTime_sq_le_rowEnergy T n hG_prog hG_bdd hG_cutoff t ω
    · simp [Set.indicator_of_notMem, hω]
  calc
    ∫ ω, A.indicator (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2) ω ∂μ
        ≤ ∫ ω, A.indicator (fun ω ↦ (n + 1 : ℝ) * sqRowEnergy G ω) ω ∂μ := by
            exact integral_mono_ae hleft_int hright_int hpointwise
    _ = (n + 1 : ℝ) * ∫ ω, A.indicator (sqRowEnergy G) ω ∂μ := by
          have hmul :
              A.indicator (fun ω ↦ (n + 1 : ℝ) * sqRowEnergy G ω) =
                fun ω ↦ (n + 1 : ℝ) * A.indicator (sqRowEnergy G) ω := by
            funext ω
            by_cases hω : ω ∈ A <;> simp [Set.indicator_apply, hω]
          rw [hmul, integral_const_mul]

/-- Helper for Theorem 25.9: every deterministic slice of a moving-average cutoff row belongs to
`L²(μ)`. -/
private theorem memLp_fixedTime_movingAverageCutoff
    {ℱ : ContinuousFiltration} (μ : Measure Ω) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (t : NNReal) :
    MemLp (fun ω ↦ movingAverageCutoff G T n t ω) (2 : ℝ≥0∞) μ := by
  have hslice_meas :
      Measurable (fun ω ↦ movingAverageCutoff G T n t ω) :=
    (movingAverageCutoff_measurable_fixedTime T n hG_prog hG_cutoff t).mono (ℱ.le _) le_rfl
  have hslice_aesm :
      AEStronglyMeasurable (fun ω ↦ movingAverageCutoff G T n t ω) μ :=
    hslice_meas.aestronglyMeasurable
  have hRowEnergy_int : Integrable (sqRowEnergy G) μ :=
    sqRowEnergy_integrable_of_memLp μ hG_memLp
  have hdom_int : Integrable (fun ω ↦ (n + 1 : ℝ) * sqRowEnergy G ω) μ :=
    hRowEnergy_int.const_mul (n + 1 : ℝ)
  have hsq_int :
      Integrable (fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2) μ := by
    let f : Ω → ℝ := fun ω ↦ (movingAverageCutoff G T n t ω) ^ 2
    -- Proof comment: the fixed-time square is measurable and pointwise dominated by the
    -- integrable scalar majorant `(n + 1) * sqRowEnergy G`.
    refine hdom_int.mono' ((hslice_meas.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with ω
    have hf_nonneg : 0 ≤ f ω := sq_nonneg _
    have hdom_nonneg : 0 ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
      refine mul_nonneg (by positivity) ?_
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun s ↦ sq_nonneg _)
    calc
      ‖f ω‖ = f ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
      _ ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
            simpa [f] using
              movingAverageCutoff_fixedTime_sq_le_rowEnergy T n hG_prog hG_bdd hG_cutoff t ω
  -- Proof comment: the fixed-time square is dominated by the integrable row energy of `G`, so the
  -- `MemLp` criterion at exponent `2` applies directly.
  exact (memLp_two_iff_integrable_sq hslice_aesm).2 hsq_int

/-- Helper for Theorem 25.9: if a nonnegative backward averaging window contains `s ∈ [0, T]`,
then the averaging time lies within one mesh step to the right of `s`. -/
private theorem mem_Icc_of_mem_movingAverageWindow
    {T : NNReal} {n : ℕ} {s t : ℝ}
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (hsT : s ≤ T)
    (hs :
      s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)) :
    t ∈ Set.Icc s (s + 1 / (n + 1 : ℝ)) := by
  have hs' :
      min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) < s ∧
        s ≤ max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) := by
    simpa [Set.uIoc, Set.mem_Ioc] using hs
  have hmax_le_t : max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) ≤ t := by
    refine max_le_iff.mpr ?_
    constructor
    · refine max_le_iff.mpr ?_
      constructor
      · exact sub_le_self _ (by positivity)
      · exact ht0
    · exact min_le_left _ _
  have hs_le_t : s ≤ t := le_trans hs'.2 hmax_le_t
  have hs_le_min : s ≤ min t T := le_min hs_le_t hsT
  have hleft_lt : max (t - 1 / (n + 1 : ℝ)) 0 < s := by
    by_contra hnot
    have hmin_ge :
        s ≤ min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) := by
      refine le_min ?_ hs_le_min
      exact le_of_not_gt hnot
    exact not_lt_of_ge hmin_ge hs'.1
  have hwindow_left_lt : t - 1 / (n + 1 : ℝ) < s := by
    exact lt_of_le_of_lt (le_max_left _ _) hleft_lt
  have ht_le : t ≤ s + 1 / (n + 1 : ℝ) := by
    linarith
  -- Proof comment: the window inclusion gives the lower bound `s ≤ t`, while the open left edge
  -- forces the left endpoint `t - 1 / (n + 1)` to stay strictly below `s`.
  exact ⟨hs_le_t, ht_le⟩

/-- Helper for Theorem 25.9: for `s ∈ [0, T]`, the set of nonnegative averaging times whose
backward window contains `s` has Lebesgue measure at most one mesh step. -/
private theorem windowOverlapIntegral_le_mesh
    (T : NNReal) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    ∫ t in Set.Ici (0 : ℝ),
        Set.indicator
          {t : ℝ |
            s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
          (fun _ ↦ (1 : ℝ)) t ∂volume ≤
      1 / (n + 1 : ℝ) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let W : Set ℝ :=
    {t : ℝ | s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
  let E : Set ℝ := Set.Icc s (s + 1 / (n + 1 : ℝ))
  have hW_meas : MeasurableSet W := by
    have hleft :
        Measurable fun t : ℝ ↦
          min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) :=
      ((measurable_id.sub measurable_const).max measurable_const).min
        (measurable_id.min measurable_const)
    have hright :
        Measurable fun t : ℝ ↦
          max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) :=
      ((measurable_id.sub measurable_const).max measurable_const).max
        (measurable_id.min measurable_const)
    -- Proof comment: the overlap set is cut out by measurable endpoint inequalities in the time
    -- variable.
    change MeasurableSet
      {t : ℝ |
        min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) < s ∧
          s ≤ max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
    exact
      (measurableSet_lt hleft measurable_const).inter
        (measurableSet_le measurable_const hright)
  have hE_subset : E ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact le_trans hs0 ht.1
  have hE_int :
      Integrable (Set.indicator E (fun _ : ℝ ↦ (1 : ℝ))) ν := by
    have hE_finite : ν E ≠ ∞ := by
      simp [ν, Measure.restrict_apply', measurableSet_Icc, Set.inter_eq_left.mpr hE_subset]
      exact (measure_Icc_lt_top (a := s) (b := s + 1 / (n + 1 : ℝ))).ne
    -- Proof comment: on the finite interval `E`, the constant function `1` is integrable, so its
    -- indicator on the ambient restricted measure is integrable as well.
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (μ := ν) (s := E) (C := (1 : ℝ)) hE_finite
  have hW_aesm :
      AEStronglyMeasurable (Set.indicator W (fun _ : ℝ ↦ (1 : ℝ))) ν := by
    exact (measurable_const.indicator hW_meas).aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂ν,
        Set.indicator W (fun _ : ℝ ↦ (1 : ℝ)) t ≤
          Set.indicator E (fun _ : ℝ ↦ (1 : ℝ)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
    by_cases htW : t ∈ W
    · have htE : t ∈ E := mem_Icc_of_mem_movingAverageWindow ht0 hs0 hsT htW
      simp [Set.indicator_of_mem, htW, htE]
    · have hE_nonneg : 0 ≤ Set.indicator E (fun _ : ℝ ↦ (1 : ℝ)) t := by
        by_cases htE : t ∈ E <;> simp [Set.indicator_apply, htE]
      simpa [Set.indicator_of_notMem, htW] using hE_nonneg
  have hW_int :
      Integrable (Set.indicator W (fun _ : ℝ ↦ (1 : ℝ))) ν :=
    hE_int.mono' hW_aesm <| by
      filter_upwards [hpointwise] with t ht
      have hnonneg : 0 ≤ Set.indicator W (fun _ : ℝ ↦ (1 : ℝ)) t := by
        by_cases htW : t ∈ W <;> simp [Set.indicator_apply, htW]
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht
  have hmeasureE :
      ν.real E = 1 / (n + 1 : ℝ) := by
    have hE_apply : ν E = volume E := by
      simp [ν, Measure.restrict_apply', measurableSet_Icc, Set.inter_eq_left.mpr hE_subset]
    have hdiff : s + 1 / (n + 1 : ℝ) - s = 1 / (n + 1 : ℝ) := by ring
    -- Proof comment: after restricting to `Set.Ici 0`, the interval measure is just the ordinary
    -- Lebesgue length of `E = [s, s + 1 / (n + 1)]`.
    rw [measureReal_def, hE_apply]
    change (volume (Set.Icc s (s + 1 / (n + 1 : ℝ)))).toReal = 1 / (n + 1 : ℝ)
    have hstep_nonneg : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
    have hden_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [Real.volume_Icc]
    simpa [hdiff, hstep_nonneg, hden_nonneg]
  -- Proof comment: the overlap set inside `Set.Ici 0` sits in the deterministic interval
  -- `[s, s + 1 / (n + 1)]`, whose Lebesgue measure is exactly one mesh step.
  calc
    ∫ t in Set.Ici (0 : ℝ), Set.indicator W (fun _ ↦ (1 : ℝ)) t ∂volume
        = ∫ t, Set.indicator W (fun _ ↦ (1 : ℝ)) t ∂ν := by
            rfl
    _ ≤ ∫ t, Set.indicator E (fun _ ↦ (1 : ℝ)) t ∂ν := by
          exact integral_mono_ae hW_int hE_int hpointwise
    _ = 1 / (n + 1 : ℝ) := by
          rw [integral_indicator_const (μ := ν) (e := (1 : ℝ)) measurableSet_Icc]
          simpa [E] using hmeasureE

/-- Helper for Theorem 25.9: clipping the overlap-count integral to the active strip
`[0, T + 1]` keeps the same mesh bound. -/
private theorem windowOverlapIntegral_le_mesh_clipped
    (T : NNReal) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        Set.indicator
          {t : ℝ |
            s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
          (fun _ ↦ (1 : ℝ)) t ∂volume ≤
      1 / (n + 1 : ℝ) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
  let W : Set ℝ :=
    {t : ℝ | s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
  let E : Set ℝ := Set.Icc s (s + 1 / (n + 1 : ℝ))
  have hW_meas : MeasurableSet W := by
    have hleft :
        Measurable fun t : ℝ ↦
          min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) :=
      ((measurable_id.sub measurable_const).max measurable_const).min
        (measurable_id.min measurable_const)
    have hright :
        Measurable fun t : ℝ ↦
          max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) :=
      ((measurable_id.sub measurable_const).max measurable_const).max
        (measurable_id.min measurable_const)
    -- Proof comment: the clipped overlap set is still described by measurable endpoint
    -- inequalities in the time variable.
    change MeasurableSet
      {t : ℝ |
        min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) < s ∧
          s ≤ max (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
    exact
      (measurableSet_lt hleft measurable_const).inter
        (measurableSet_le measurable_const hright)
  have hstep_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hone_pos : (0 : ℝ) < 1 := by positivity
    calc
      1 / (n + 1 : ℝ) ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le hone_pos hden
      _ = 1 := by norm_num
  have hE_subset_strip : E ⊆ Set.Icc (0 : ℝ) ((T : ℝ) + 1) := by
    intro t ht
    constructor
    · exact le_trans hs0 ht.1
    · linarith [ht.2, hsT, hstep_le_one]
  have hν_lt : ν Set.univ < ∞ := by
    simpa [ν, Measure.restrict_apply', measurableSet_Icc] using
      (measure_Icc_lt_top (a := (0 : ℝ)) (b := (T : ℝ) + 1))
  have hν_finite : ν Set.univ ≠ ∞ := hν_lt.ne
  have hE_finite : ν E ≠ ∞ := by
    have hE_lt : ν E < ∞ := by
      calc
        ν E ≤ ν Set.univ := by
          exact measure_mono (show E ⊆ Set.univ by intro x hx; simp)
        _ < ∞ := hν_lt
    exact hE_lt.ne
  have hE_int :
      Integrable (Set.indicator E (fun _ : ℝ ↦ (1 : ℝ))) ν := by
    rw [integrable_indicator_iff]
    · exact integrableOn_const (μ := ν) (s := E) (C := (1 : ℝ)) hE_finite
    · simpa [E] using (measurableSet_Icc : MeasurableSet E)
  have hW_aesm :
      AEStronglyMeasurable (Set.indicator W (fun _ : ℝ ↦ (1 : ℝ))) ν := by
    exact (measurable_const.indicator hW_meas).aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂ν,
        Set.indicator W (fun _ : ℝ ↦ (1 : ℝ)) t ≤
          Set.indicator E (fun _ : ℝ ↦ (1 : ℝ)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t htStrip
    by_cases htW : t ∈ W
    · have htE : t ∈ E := mem_Icc_of_mem_movingAverageWindow htStrip.1 hs0 hsT htW
      simp [Set.indicator_of_mem, htW, htE]
    · have hE_nonneg : 0 ≤ Set.indicator E (fun _ : ℝ ↦ (1 : ℝ)) t := by
        by_cases htE : t ∈ E <;> simp [Set.indicator_apply, htE]
      simpa [Set.indicator_of_notMem, htW] using hE_nonneg
  have hW_int :
      Integrable (Set.indicator W (fun _ : ℝ ↦ (1 : ℝ))) ν :=
    hE_int.mono' hW_aesm <| by
      filter_upwards [hpointwise] with t ht
      have hnonneg : 0 ≤ Set.indicator W (fun _ : ℝ ↦ (1 : ℝ)) t := by
        by_cases htW : t ∈ W <;> simp [Set.indicator_apply, htW]
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht
  have hE_apply : ν E = volume E := by
    dsimp [ν]
    rw [Measure.restrict_apply]
    · congr 1
      ext t
      constructor
      · intro ht
        exact ht.1
      · intro ht
        exact ⟨ht, hE_subset_strip ht⟩
    · simpa [E] using (measurableSet_Icc : MeasurableSet E)
  have hmeasureE :
      ν.real E = 1 / (n + 1 : ℝ) := by
    rw [measureReal_def, hE_apply]
    change (volume (Set.Icc s (s + 1 / (n + 1 : ℝ)))).toReal = 1 / (n + 1 : ℝ)
    have hstep_nonneg : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
    have hden_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    have hdiff : s + 1 / (n + 1 : ℝ) - s = 1 / (n + 1 : ℝ) := by ring
    rw [Real.volume_Icc]
    simpa [hdiff, hstep_nonneg, hden_nonneg]
  -- Proof comment: on the active strip, the overlap set is still contained in the deterministic
  -- interval `[s, s + 1 / (n + 1)]`, so its clipped measure is bounded by the same mesh size.
  calc
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1), Set.indicator W (fun _ ↦ (1 : ℝ)) t ∂volume
        = ∫ t, Set.indicator W (fun _ ↦ (1 : ℝ)) t ∂ν := by
            rfl
    _ ≤ ∫ t, Set.indicator E (fun _ ↦ (1 : ℝ)) t ∂ν := by
          exact integral_mono_ae hW_int hE_int hpointwise
    _ = 1 / (n + 1 : ℝ) := by
          rw [integral_indicator_const (μ := ν) (e := (1 : ℝ))]
          · simpa [E] using hmeasureE
          · simpa [E] using (measurableSet_Icc : MeasurableSet E)

/-- Helper for Theorem 25.9: every moving-average row is pointwise dominated by the original
row-energy function. -/
private theorem movingAverageWindowIntegral_eq_stripIndicatorIntegral
    {G : Process} (T : NNReal) (n : ℕ)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) {t : ℝ} (ht0 : 0 ≤ t) :
    ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
        (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume =
      ∫ s in Set.Icc (0 : ℝ) T,
        (processToTimeSpaceFun G (ω, s)) ^ 2 *
          Set.indicator
            {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
            (fun _ ↦ (1 : ℝ)) s ∂volume := by
  let W : Set ℝ := Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)
  let f : ℝ → ℝ := fun s ↦ (processToTimeSpaceFun G (ω, s)) ^ 2
  have hrestrict :
      Set.indicator (Set.Icc (0 : ℝ) T) f =ᵐ[volume.restrict W] f := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hs_uIcc :
        s ∈ Set.uIcc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) :=
      Set.uIoc_subset_uIcc hs
    have hleft_nonneg : 0 ≤ max (t - 1 / (n + 1 : ℝ)) 0 := le_max_right _ _
    have hright_nonneg : 0 ≤ min t T := by
      refine le_min ht0 ?_
      exact_mod_cast bot_le
    have hs_lower :
        min (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) ≤ s := by
      rw [Set.mem_uIcc] at hs_uIcc
      rcases hs_uIcc with hs_uIcc | hs_uIcc
      · exact min_le_iff.mpr (Or.inl hs_uIcc.1)
      · exact min_le_iff.mpr (Or.inr hs_uIcc.1)
    have hs0 : 0 ≤ s := by
      exact le_trans (le_min hleft_nonneg hright_nonneg) hs_lower
    by_cases hsT : s ≤ T
    · have hs_mem : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0, hsT⟩
      simp [W, f, hs_mem]
    · have hs_gt : T < s := lt_of_not_ge hsT
      have hzero : processToTimeSpaceFun G (ω, s) = 0 := by
        have hs_gt_nn : T < s.toNNReal := by
          rw [Real.toNNReal_of_nonneg hs0]
          exact hs_gt
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg hs0] using
          hG_cutoff (ω := ω) hs_gt_nn
      have hzero' : G s.toNNReal ω = 0 := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg hs0] using hzero
      have hs_not_mem : s ∉ Set.Icc (0 : ℝ) T := by
        simp [hsT]
      simp [W, f, hs_not_mem, hzero']
  have hindicator_mul :
      (fun s ↦ Set.indicator W f s) =
        fun s ↦
          f s *
            Set.indicator
              {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
              (fun _ ↦ (1 : ℝ)) s := by
    funext s
    by_cases hs : s ∈ W
    · have hs' :
          s ∈ {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)} := by
        simpa [W] using hs
      rw [Set.indicator_of_mem hs']
      simpa [W] using Set.indicator_of_mem (f := f) hs
    · have hs' :
          s ∉ {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)} := by
        simpa [W] using hs
      rw [Set.indicator_of_notMem hs']
      simpa [W] using Set.indicator_of_notMem (f := f) hs
  -- Proof comment: outside the deterministic strip `[0,T]`, the square path vanishes on the
  -- moving window because `G` is already zero there, so the window integral can be rewritten as a
  -- fixed-strip indicator integral.
  calc
    ∫ s in W, f s ∂volume = ∫ s in W, Set.indicator (Set.Icc (0 : ℝ) T) f s ∂volume := by
      exact integral_congr_ae hrestrict.symm
    _ = ∫ s in W ∩ Set.Icc (0 : ℝ) T, f s ∂volume := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Icc]
    _ = ∫ s in Set.Icc (0 : ℝ) T ∩ W, f s ∂volume := by
      rw [Set.inter_comm]
    _ = ∫ s in Set.Icc (0 : ℝ) T, Set.indicator W f s ∂volume := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_uIoc]
    _ =
        ∫ s in Set.Icc (0 : ℝ) T,
          f s *
            Set.indicator
              {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
              (fun _ ↦ (1 : ℝ)) s ∂volume := by
        simp [hindicator_mul]

-- Route correction: use one shared strip kernel and one named overlap weight so the Fubini
-- bridge and the later row-energy domination consume the same analytic bookkeeping.

/-- Helper for Theorem 25.9: the clipped strip support for the shared moving-average kernel. -/
private def movingAverageStripSupport (T : NNReal) (n : ℕ) : Set (ℝ × ℝ) :=
  {p |
    p.2 ∈
      Set.uIoc (max (p.1 - 1 / (n + 1 : ℝ)) 0) (min p.1 T)}

/-- Helper for Theorem 25.9: the shared rectangle kernel for the clipped moving-average window. -/
private def movingAverageStripKernel {G : Process} (T : NNReal) (n : ℕ) (ω : Ω) :
    ℝ → ℝ → ℝ :=
  fun t s ↦
    (n + 1 : ℝ) *
      ((processToTimeSpaceFun G (ω, s)) ^ 2 *
        Set.indicator (movingAverageStripSupport T n) (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (t, s))

/-- Helper for Theorem 25.9: the deterministic overlap weight of the clipped moving-average
windows. -/
private def movingAverageStripOverlap (T : NNReal) (n : ℕ) : ℝ → ℝ :=
  fun s ↦
    (n + 1 : ℝ) *
      ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        Set.indicator
          {t : ℝ |
            s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
          (fun _ ↦ (1 : ℝ)) t ∂volume

/-- Helper for Theorem 25.9: the clipped strip support is measurable in the `(t,s)` variables. -/
private theorem measurableSet_movingAverageStripSupport (T : NNReal) (n : ℕ) :
    MeasurableSet (movingAverageStripSupport T n) := by
  have hleft :
      Measurable fun p : ℝ × ℝ ↦
        min (max (p.1 - 1 / (n + 1 : ℝ)) 0) (min p.1 T) :=
    ((measurable_fst.sub measurable_const).max measurable_const).min
      (measurable_fst.min measurable_const)
  have hright :
      Measurable fun p : ℝ × ℝ ↦
        max (max (p.1 - 1 / (n + 1 : ℝ)) 0) (min p.1 T) :=
    ((measurable_fst.sub measurable_const).max measurable_const).max
      (measurable_fst.min measurable_const)
  -- Proof comment: the strip is cut out by measurable inequalities in the pair `(t,s)`.
  change MeasurableSet
    {p : ℝ × ℝ |
      min (max (p.1 - 1 / (n + 1 : ℝ)) 0) (min p.1 T) < p.2 ∧
        p.2 ≤ max (max (p.1 - 1 / (n + 1 : ℝ)) 0) (min p.1 T)}
  exact
    (measurableSet_lt hleft measurable_snd).inter
      (measurableSet_le measurable_snd hright)

/-- Helper for Theorem 25.9: the shared strip kernel is integrable on the clipped rectangle with
one uniform square bound. -/
private theorem movingAverageStripKernel_integrable
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (ω : Ω) :
    let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
    let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    Integrable (Function.uncurry (movingAverageStripKernel (G := G) T n ω)) (νt.prod νs) := by
  rcases hG_bdd with ⟨C, _, hC⟩
  let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
  let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
  letI : IsFiniteMeasure νt := by
    dsimp [νt]
    infer_instance
  letI : IsFiniteMeasure νs := by
    dsimp [νs]
    infer_instance
  letI : IsFiniteMeasure (νt.prod νs) := by
    infer_instance
  have hg_meas :
      Measurable fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2 := by
    -- Proof comment: fixing the sample point keeps the progressively measurable path measurable in
    -- real time, and squaring preserves measurability.
    have hpath_meas := measurable_realPath_of_progMeasurable hG_prog ω
    simpa [pow_two] using hpath_meas.mul hpath_meas
  have hkernel_meas :
      Measurable (Function.uncurry (movingAverageStripKernel (G := G) T n ω)) := by
    have hsq :
        Measurable fun p : ℝ × ℝ ↦
          (processToTimeSpaceFun G (ω, p.2)) ^ 2 := by
      exact hg_meas.comp measurable_snd
    have hindicator :
        Measurable
          (Set.indicator (movingAverageStripSupport T n) (fun _ : ℝ × ℝ ↦ (1 : ℝ))) :=
      measurable_const.indicator (measurableSet_movingAverageStripSupport T n)
    -- Proof comment: the kernel is the product of the square coefficient with the measurable strip
    -- indicator on the clipped rectangle.
    change Measurable fun p : ℝ × ℝ ↦
      (n + 1 : ℝ) *
        ((processToTimeSpaceFun G (ω, p.2)) ^ 2 *
          Set.indicator (movingAverageStripSupport T n) (fun _ : ℝ × ℝ ↦ (1 : ℝ)) p)
    exact measurable_const.mul (hsq.mul hindicator)
  have hkernel_bound :
      ∀ᵐ p ∂(νt.prod νs),
        ‖Function.uncurry (movingAverageStripKernel (G := G) T n ω) p‖ ≤
          (n + 1 : ℝ) * C ^ 2 := by
    filter_upwards with p
    have hg_bound : |processToTimeSpaceFun G (ω, p.2)| ≤ C := by
      simpa [processToTimeSpaceFun] using hC p.2.toNNReal ω
    by_cases hp : p ∈ movingAverageStripSupport T n
    · have hg_sq : (processToTimeSpaceFun G (ω, p.2)) ^ 2 ≤ C ^ 2 := by
        have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg _) hg_bound
        have hlow := (abs_le.mp hg_bound).1
        have hhigh := (abs_le.mp hg_bound).2
        nlinarith
      have hnonneg :
          0 ≤ ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, p.2)) ^ 2) := by
        positivity
      have hvalue :
          Function.uncurry (movingAverageStripKernel (G := G) T n ω) p =
            ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, p.2)) ^ 2) := by
        simp [movingAverageStripKernel, Function.uncurry, hp, mul_assoc]
      -- Proof comment: on the strip support, the kernel is bounded by the global square bound
      -- `C²` times the mesh factor `(n + 1)`.
      calc
        ‖Function.uncurry (movingAverageStripKernel (G := G) T n ω) p‖
            = ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, p.2)) ^ 2) := by
                rw [hvalue, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ ≤ (n + 1 : ℝ) * C ^ 2 := by
              exact mul_le_mul_of_nonneg_left hg_sq (by positivity : 0 ≤ (n + 1 : ℝ))
    · have hbound_nonneg : 0 ≤ (n + 1 : ℝ) * C ^ 2 := by positivity
      have hvalue :
          Function.uncurry (movingAverageStripKernel (G := G) T n ω) p = 0 := by
        simp [movingAverageStripKernel, Function.uncurry, hp]
      calc
        ‖Function.uncurry (movingAverageStripKernel (G := G) T n ω) p‖ = 0 := by
            rw [hvalue]
            simp
        _ ≤ (n + 1 : ℝ) * C ^ 2 := hbound_nonneg
  exact
    Integrable.of_bound
      hkernel_meas.aestronglyMeasurable ((n + 1 : ℝ) * C ^ 2) hkernel_bound

/-- Helper for Theorem 25.9: the `s`-sections of the shared strip kernel recover the clipped
moving-window square integral. -/
private theorem movingAverageStripKernel_timeSection_eq
    {G : Process} (T : NNReal) (n : ℕ)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    (fun t ↦ ∫ s, movingAverageStripKernel (G := G) T n ω t s ∂νs) =ᵐ[
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))]
      fun t ↦
        (n + 1 : ℝ) *
          ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
  let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have ht0 : 0 ≤ t := ht.1
  rw [movingAverageWindowIntegral_eq_stripIndicatorIntegral T n hG_cutoff ω ht0]
  -- Proof comment: once the window integral is normalized to the fixed strip `[0,T]`, the left
  -- section is just a constant multiple of the shared kernel.
  simpa [νs, movingAverageStripKernel, movingAverageStripSupport, mul_assoc] using
    (integral_const_mul
      (μ := νs)
      (r := (n + 1 : ℝ))
      (f := fun s : ℝ ↦
        (processToTimeSpaceFun G (ω, s)) ^ 2 *
          Set.indicator
            {u : ℝ | u ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
            (fun _ ↦ (1 : ℝ)) s))

/-- Helper for Theorem 25.9: the `t`-sections of the shared strip kernel recover the overlap
weight on the fixed strip. -/
private theorem movingAverageStripKernel_spaceSection_eq
    {G : Process} (T : NNReal) (n : ℕ) (ω : Ω) :
    let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
    (fun s ↦ ∫ t, movingAverageStripKernel (G := G) T n ω t s ∂νt) =ᵐ[
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))]
      fun s ↦
        (processToTimeSpaceFun G (ω, s)) ^ 2 * movingAverageStripOverlap T n s := by
  let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
  refine Filter.Eventually.of_forall fun s ↦ ?_
  -- Proof comment: for fixed `s`, the right section is the constant square factor times the
  -- deterministic overlap count of clipped windows containing `s`.
  calc
    ∫ t, movingAverageStripKernel (G := G) T n ω t s ∂νt
        =
          ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
            ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, s)) ^ 2) *
              Set.indicator
                {t : ℝ |
                  s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
                (fun _ ↦ (1 : ℝ)) t ∂volume := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun t ↦ by
              have hmem_iff :
                  (t, s) ∈ movingAverageStripSupport T n ↔
                    s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) := by
                simp [movingAverageStripSupport]
              have hindicator :
                  Set.indicator (movingAverageStripSupport T n) (fun _ : ℝ × ℝ ↦ (1 : ℝ)) (t, s) =
                    Set.indicator
                      {t : ℝ |
                        s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
                      (fun _ ↦ (1 : ℝ)) t := by
                classical
                change (if (t, s) ∈ movingAverageStripSupport T n then 1 else 0) =
                  if s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T) then 1 else 0
                by_cases ht :
                    s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)
                · rw [if_pos (hmem_iff.mpr ht), if_pos ht]
                · rw [if_neg (by simpa [hmem_iff] using ht), if_neg ht]
              simp [movingAverageStripKernel, hindicator, mul_assoc]
    _ =
        ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, s)) ^ 2) *
          ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
            Set.indicator
              {t : ℝ |
                s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
              (fun _ ↦ (1 : ℝ)) t ∂volume := by
          exact integral_const_mul
            (μ := νt)
            (r := ((n + 1 : ℝ) * (processToTimeSpaceFun G (ω, s)) ^ 2))
            (f := fun t : ℝ ↦
              Set.indicator
                {t : ℝ |
                  s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
                (fun _ ↦ (1 : ℝ)) t)
    _ = (processToTimeSpaceFun G (ω, s)) ^ 2 * movingAverageStripOverlap T n s := by
          simp [movingAverageStripOverlap, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 25.9: every moving-average row is pointwise dominated by the original
row-energy function. -/
private theorem movingAverageStripKernel_productBridge
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        (n + 1 : ℝ) *
          ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ∂volume =
    ∫ s in Set.Icc (0 : ℝ) T,
        (processToTimeSpaceFun G (ω, s)) ^ 2 *
          ((n + 1 : ℝ) *
            ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
              Set.indicator
                {t : ℝ |
                  s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
                (fun _ ↦ (1 : ℝ)) t ∂volume) ∂volume := by
  let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
  let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
  letI : IsFiniteMeasure νt := by
    dsimp [νt]
    infer_instance
  letI : IsFiniteMeasure νs := by
    dsimp [νs]
    infer_instance
  letI : IsFiniteMeasure (νt.prod νs) := by
    infer_instance
  have hkernel_int :
      Integrable (Function.uncurry (movingAverageStripKernel (G := G) T n ω)) (νt.prod νs) := by
    simpa [νt, νs] using movingAverageStripKernel_integrable
      (G := G) (T := T) (n := n) hG_prog hG_bdd ω
  have hleft_ae :
      (fun t ↦ ∫ s, movingAverageStripKernel (G := G) T n ω t s ∂νs) =ᵐ[νt]
        fun t ↦
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
    simpa [νt, νs] using movingAverageStripKernel_timeSection_eq
      (G := G) (T := T) (n := n) hG_cutoff ω
  have hright_ae :
      (fun s ↦ ∫ t, movingAverageStripKernel (G := G) T n ω t s ∂νt) =ᵐ[νs]
        fun s ↦
          (processToTimeSpaceFun G (ω, s)) ^ 2 * movingAverageStripOverlap T n s := by
    simpa [νt, νs] using movingAverageStripKernel_spaceSection_eq
      (G := G) (T := T) (n := n) ω
  -- Proof comment: one bounded rectangle kernel packages the strip normalization and supports a
  -- single Fubini swap on the finite rectangle.
  calc
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        (n + 1 : ℝ) *
          ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ∂volume
        = ∫ t, ∫ s, movingAverageStripKernel (G := G) T n ω t s ∂νs ∂νt := by
            exact integral_congr_ae hleft_ae.symm
    _ = ∫ s, ∫ t, movingAverageStripKernel (G := G) T n ω t s ∂νt ∂νs := by
          exact integral_integral_swap hkernel_int
    _ =
        ∫ s in Set.Icc (0 : ℝ) T,
          (processToTimeSpaceFun G (ω, s)) ^ 2 *
            ((n + 1 : ℝ) *
              ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
                Set.indicator
                  {t : ℝ |
                    s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
                  (fun _ ↦ (1 : ℝ)) t ∂volume) ∂volume := by
          exact integral_congr_ae hright_ae

/-- Helper for Theorem 25.9: every moving-average row is pointwise dominated by the original
row-energy function. -/
private theorem movingAverageCutoff_windowIntegralOnStrip_le_sqRowEnergy
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        (n + 1 : ℝ) *
          ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ∂volume ≤
      sqRowEnergy G ω := by
  have hG_bdd' := hG_bdd
  rcases hG_bdd with ⟨C, _, hC⟩
  let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
  let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
  letI : IsFiniteMeasure νt := by
    dsimp [νt]
    infer_instance
  letI : IsFiniteMeasure νs := by
    dsimp [νs]
    infer_instance
  let g : ℝ → ℝ := fun s ↦ (processToTimeSpaceFun G (ω, s)) ^ 2
  have hg_meas : Measurable g := by
    -- Proof comment: the fixed sample path of `G` is measurable in real time, and squaring keeps
    -- that measurability on the clipped strip.
    have hpath_meas := measurable_realPath_of_progMeasurable hG_prog ω
    simpa [g, pow_two] using hpath_meas.mul hpath_meas
  have hg_int :
      Integrable g νs := by
    have hsq_int :
        Integrable
          (fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
      simpa using
        integrable_sq_realPath_on_Ici_of_bound_cutoff T hG_prog hG_bdd' hG_cutoff ω
    have hbound_on_strip :
        ∀ᵐ s ∂νs, ‖g s‖ ≤ C ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hg_bound : |processToTimeSpaceFun G (ω, s)| ≤ C := by
        have hs_nonneg : 0 ≤ s := hs.1
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg hs_nonneg] using hC s.toNNReal ω
      have hg_sq : g s ≤ C ^ 2 := by
        have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg _) hg_bound
        have hsq_le : |processToTimeSpaceFun G (ω, s)| ^ 2 ≤ |C| ^ 2 := by
          refine sq_le_sq.mpr ?_
          simpa [abs_of_nonneg hC_nonneg] using hg_bound
        simpa [g, sq_abs, abs_of_nonneg hC_nonneg] using hsq_le
      have hnonneg : 0 ≤ g s := by
        dsimp [g]
        exact sq_nonneg _
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hg_sq
    -- Proof comment: on the finite strip `[0,T]`, the squared path is uniformly bounded by `C²`.
    exact Integrable.of_bound (μ := νs) hg_meas.aestronglyMeasurable (C ^ 2) hbound_on_strip
  have hkernel_int :
      Integrable (Function.uncurry (movingAverageStripKernel (G := G) T n ω)) (νt.prod νs) := by
    simpa [νt, νs] using movingAverageStripKernel_integrable
      (G := G) (T := T) (n := n) hG_prog hG_bdd' ω
  have hoverlap_nonneg :
      ∀ᵐ s ∂νs, 0 ≤ movingAverageStripOverlap T n s := by
    filter_upwards with s
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun t ↦ by
      by_cases ht :
          t ∈
            {t : ℝ |
              s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
      · rw [Set.indicator_of_mem ht]
        positivity
      · rw [Set.indicator_of_notMem ht]
        positivity
  have hoverlap_le_one :
      ∀ᵐ s ∂νs, movingAverageStripOverlap T n s ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs0 : 0 ≤ s := hs.1
    have hsT : s ≤ T := hs.2
    have hoverlap_le :
        ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
            Set.indicator
              {t : ℝ |
                s ∈ Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T)}
              (fun _ ↦ (1 : ℝ)) t ∂volume ≤
          1 / (n + 1 : ℝ) :=
      windowOverlapIntegral_le_mesh_clipped T n hs0 hsT
    -- Proof comment: the overlap count of the clipped windows is at most one mesh interval, so
    -- after multiplying by `(n + 1)` the weight is bounded by `1`.
    have hfactor_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
    calc
      movingAverageStripOverlap T n s
          ≤ (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) := by
            simpa [movingAverageStripOverlap] using
              mul_le_mul_of_nonneg_left hoverlap_le hfactor_nonneg
      _ = 1 := by
            field_simp
  have hspace_int :
      Integrable
        (fun s : ℝ ↦ ∫ t, movingAverageStripKernel (G := G) T n ω t s ∂νt) νs := by
    simpa [νt, νs, movingAverageStripKernel, Function.uncurry] using
      hkernel_int.integral_prod_right
  have hweighted_int :
      Integrable (fun s ↦ g s * movingAverageStripOverlap T n s) νs := by
    refine hspace_int.congr ?_
    simpa [g, νt, νs] using movingAverageStripKernel_spaceSection_eq
      (G := G) (T := T) (n := n) ω
  -- Proof comment: after the single Fubini swap above, the clipped overlap weight is at most `1`
  -- on `[0,T]`, so the strip integral is dominated by the row energy of `G`.
  calc
    ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
        (n + 1 : ℝ) *
          ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
            (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ∂volume
        =
        ∫ s in Set.Icc (0 : ℝ) T, g s * movingAverageStripOverlap T n s ∂volume := by
          simpa [g, movingAverageStripOverlap] using movingAverageStripKernel_productBridge
            (G := G) (T := T) (n := n) hG_prog hG_bdd' hG_cutoff ω
    _ ≤ ∫ s in Set.Icc (0 : ℝ) T, g s ∂volume := by
          exact integral_mono_ae hweighted_int hg_int <| by
            filter_upwards [hoverlap_nonneg, hoverlap_le_one] with s hs_nonneg hs_le
            have hg_nonneg : 0 ≤ g s := by
              dsimp [g]
              exact sq_nonneg _
            nlinarith
    _ ≤ sqRowEnergy G ω := by
          have hsq_nonneg :
              0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))]
                fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2 := by
            exact Filter.Eventually.of_forall fun s ↦ sq_nonneg _
          have hsubset : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) := by
            intro s hs
            exact hs.1
          have hrow_int :
              Integrable (fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2)
                ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
            simpa using
              integrable_sq_realPath_on_Ici_of_bound_cutoff T hG_prog hG_bdd' hG_cutoff ω
          simpa [g, sqRowEnergy] using
            (integral_mono_measure
              (Measure.restrict_mono hsubset le_rfl) hsq_nonneg hrow_int :
                ∫ s, g s ∂volume.restrict (Set.Icc (0 : ℝ) T) ≤
                  ∫ s, g s ∂volume.restrict (Set.Ici (0 : ℝ)))

/-- Helper for Theorem 25.9: every moving-average row is pointwise dominated by the original
row-energy function. -/
private theorem sqRowEnergy_movingAverageCutoff_le
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    sqRowEnergy (movingAverageCutoff G T n) ω ≤ sqRowEnergy G ω := by
  let K : Process := movingAverageCutoff G T n
  let f : ℝ → ℝ := fun t ↦ (processToTimeSpaceFun K (ω, t)) ^ 2
  have hK_prog : ProgMeasurable ℱ K := by
    simpa [K] using progMeasurable_movingAverageCutoff T n hG_prog hG_bdd hG_cutoff
  have hK_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |K t ω| ≤ C := by
    simpa [K] using movingAverageCutoff_hasBound T n hG_bdd hG_cutoff
  have hK_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, (T + 1 / (n + 1 : NNReal)) < t → K t ω = 0 := by
    intro t ω ht
    exact movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff (le_of_lt ht) ω
  have hstep_le_one : 1 / (n + 1 : ℝ) ≤ 1 := by
    have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hone_pos : (0 : ℝ) < 1 := by positivity
    calc
      1 / (n + 1 : ℝ) ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le hone_pos hden
      _ = 1 := by norm_num
  have hrestrict :
      Set.indicator (Set.Icc (0 : ℝ) ((T : ℝ) + 1)) f =ᵐ[
          (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht0
    by_cases htT : t ≤ (T : ℝ) + 1
    · have ht_mem : t ∈ Set.Icc (0 : ℝ) ((T : ℝ) + 1) := ⟨ht0, htT⟩
      simp [f, ht_mem]
    · have ht_gt : (T : ℝ) + 1 < t := lt_of_not_ge htT
      have ht_mesh : (T : ℝ) + 1 / (n + 1 : ℝ) < t := lt_of_le_of_lt (by nlinarith) ht_gt
      have ht_mesh_nn :
          T + (1 / (n + 1 : NNReal)) < t.toNNReal := by
        rw [Real.toNNReal_of_nonneg ht0]
        exact_mod_cast ht_mesh
      have hzero : K t.toNNReal ω = 0 := hK_cutoff ht_mesh_nn
      have hzero_subtype : K ⟨t, ht0⟩ ω = 0 := by
        simpa [Real.toNNReal_of_nonneg ht0] using hzero
      have hsq_zero : f t = 0 := by
        simp [f, processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0, hzero_subtype]
      have ht_not_mem : t ∉ Set.Icc (0 : ℝ) ((T : ℝ) + 1) := by
        simp [htT]
      -- Proof comment: beyond `T + 1`, the moving-average window is already wholly past the
      -- original cutoff, so the row contributes nothing to the energy.
      simpa [ht_not_mem] using hsq_zero.symm
  have hf_int :
      Integrable f ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
    simpa [K, f] using
      integrable_sq_realPath_on_Ici_of_bound_cutoff
        (T + 1 / (n + 1 : NNReal)) hK_prog hK_bdd hK_cutoff ω
  have hwindow_int :
      Integrable
        (fun t : ℝ ↦
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume)
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))) := by
    let νt : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))
    let νs : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (T : ℝ))
    letI : IsFiniteMeasure νt := by
      dsimp [νt]
      infer_instance
    letI : IsFiniteMeasure νs := by
      dsimp [νs]
      infer_instance
    letI : IsFiniteMeasure (νt.prod νs) := by
      infer_instance
    have hkernel_int :
        Integrable (Function.uncurry (movingAverageStripKernel (G := G) T n ω)) (νt.prod νs) := by
      simpa [νt, νs] using movingAverageStripKernel_integrable
        (G := G) (T := T) (n := n) hG_prog hG_bdd ω
    have hsection_int :
        Integrable
          (fun t : ℝ ↦ ∫ s, movingAverageStripKernel (G := G) T n ω t s ∂νs) νt := by
      simpa [νt, νs, movingAverageStripKernel, Function.uncurry] using
        hkernel_int.integral_prod_left
    -- Proof comment: the strip-window majorant is exactly the left section integral of the shared
    -- bounded rectangle kernel.
    refine hsection_int.congr ?_
    simpa [νt, νs] using movingAverageStripKernel_timeSection_eq
      (G := G) (T := T) (n := n) hG_cutoff ω
  have hf_strip_int :
      Integrable f ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))) := by
    have hf_on :
        IntegrableOn f (Set.Ici (0 : ℝ)) volume := by
      simpa [IntegrableOn] using hf_int
    have hf_on_strip :
        IntegrableOn f (Set.Icc (0 : ℝ) ((T : ℝ) + 1)) volume :=
      hf_on.mono_set (by intro t ht; exact ht.1)
    simpa [IntegrableOn] using hf_on_strip
  have hpointwise :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) ((T : ℝ) + 1))),
        f t ≤
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa [f, K, processToTimeSpaceFun, Real.toNNReal_of_nonneg ht.1] using
      movingAverageCutoff_sq_le_windowSqIntegral T n hG_prog hG_bdd hG_cutoff t.toNNReal ω
  -- Proof comment: the moving-average row energy lives on `[0,T+1]`; there the pointwise Jensen
  -- bound reduces the full row energy to the already proved strip integral estimate.
  calc
    sqRowEnergy K ω = ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1), f t ∂volume := by
      calc
        sqRowEnergy K ω = ∫ t in Set.Ici (0 : ℝ), f t ∂volume := by
          rfl
        _ = ∫ t in Set.Ici (0 : ℝ), Set.indicator (Set.Icc (0 : ℝ) ((T : ℝ) + 1)) f t ∂volume := by
          exact integral_congr_ae hrestrict.symm
        _ = ∫ t in Set.Ici (0 : ℝ) ∩ Set.Icc (0 : ℝ) ((T : ℝ) + 1), f t ∂volume := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Icc]
        _ = ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1), f t ∂volume := by
          have hinter :
              Set.Ici (0 : ℝ) ∩ Set.Icc (0 : ℝ) ((T : ℝ) + 1) =
                Set.Icc (0 : ℝ) ((T : ℝ) + 1) := by
            ext t
            constructor
            · intro ht
              exact ht.2
            · intro ht
              exact ⟨ht.1, ht⟩
          rw [hinter]
    _ ≤
        ∫ t in Set.Icc (0 : ℝ) ((T : ℝ) + 1),
          (n + 1 : ℝ) *
            ∫ s in Set.uIoc (max (t - 1 / (n + 1 : ℝ)) 0) (min t T),
              (processToTimeSpaceFun G (ω, s)) ^ 2 ∂volume ∂volume := by
          exact integral_mono_ae hf_strip_int hwindow_int hpointwise
    _ ≤ sqRowEnergy G ω := by
          exact movingAverageCutoff_windowIntegralOnStrip_le_sqRowEnergy
            T n hG_prog hG_bdd hG_cutoff ω

/-- Helper for Theorem 25.9: stable wrapper around the row-energy domination for moving-average
rows. -/
theorem movingAverageCutoff_sqRowEnergy_le
    {ℱ : ContinuousFiltration} {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    sqRowEnergy (movingAverageCutoff G T n) ω ≤ sqRowEnergy G ω := by
  -- Proof comment: expose the already proved overlap-count estimate through a stable non-private
  -- wrapper so later row-energy arguments do not depend on a private declaration name.
  exact sqRowEnergy_movingAverageCutoff_le T n hG_prog hG_bdd hG_cutoff ω

/-- Helper for Theorem 25.9: row-energy domination upgrades every moving-average row to ambient
`L²(processMeasure μ)`. -/
private theorem movingAverageCutoff_memLp_of_rowEnergy_domination
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    MemLp (processToTimeSpaceFun (movingAverageCutoff G T n))
      (2 : ℝ≥0∞) (processMeasure μ) := by
  let K : Process := movingAverageCutoff G T n
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hK_aesm :
      AEStronglyMeasurable (processToTimeSpaceFun K) (processMeasure μ) := by
    -- Proof comment: the moving-average row is progressively measurable, so its ambient
    -- realization is a.e.-strongly measurable on `Ω × [0,∞)`.
    simpa [K] using
      aestronglyMeasurable_processToTimeSpaceFun_movingAverageCutoff
        (μ := μ) (T := T) (n := n) hG_prog hG_bdd hG_cutoff
  have hK_prog : ProgMeasurable ℱ K := by
    -- Proof comment: the rowwise averaging construction preserves progressive measurability.
    simpa [K] using progMeasurable_movingAverageCutoff T n hG_prog hG_bdd hG_cutoff
  have hK_bdd :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |K t ω| ≤ C := by
    -- Proof comment: every moving-average row inherits the same deterministic bound as `G`.
    simpa [K] using movingAverageCutoff_hasBound T n hG_bdd hG_cutoff
  have hK_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, (T + 1 / (n + 1 : NNReal)) < t → K t ω = 0 := by
    -- Proof comment: once the averaging window lies wholly past `T`, the row vanishes.
    intro t ω ht
    exact movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff (le_of_lt ht) ω
  have hrow_int :
      ∀ᵐ ω ∂μ,
        Integrable (fun t : ℝ ↦ (processToTimeSpaceFun K (ω, t)) ^ 2) ν := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    -- Proof comment: each sample path is bounded and supported in a deterministic compact time
    -- strip, so its square is integrable on `[0,∞)`.
    simpa [K, ν] using
      integrable_sq_realPath_on_Ici_of_bound_cutoff
        (T + 1 / (n + 1 : NNReal)) hK_prog hK_bdd hK_cutoff ω
  have hRowEnergy_aesm : AEStronglyMeasurable (sqRowEnergy K) μ := by
    have hsq_aesm :
        AEStronglyMeasurable
          (fun x : Ω × ℝ ↦ (processToTimeSpaceFun K x) ^ 2)
          (μ.prod ν) := by
      simpa [processMeasure, ν] using hK_aesm.pow 2
    -- Proof comment: `sqRowEnergy K` is the outer integral of the ambient square function.
    simpa [sqRowEnergy, processMeasure, ν] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := μ) (ν := ν) hsq_aesm)
  have hRowEnergy_int_G : Integrable (sqRowEnergy G) μ :=
    sqRowEnergy_integrable_of_memLp μ hG_memLp
  have hRowEnergy_int_K : Integrable (sqRowEnergy K) μ := by
    refine hRowEnergy_int_G.mono' hRowEnergy_aesm ?_
    filter_upwards with ω
    have hK_nonneg : 0 ≤ sqRowEnergy K ω := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    have hG_nonneg : 0 ≤ sqRowEnergy G ω := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    -- Proof comment: the previously proved overlap-count estimate controls the full row energy of
    -- `K` by the integrable row energy of `G`.
    calc
      ‖sqRowEnergy K ω‖ = sqRowEnergy K ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hK_nonneg]
      _ ≤ sqRowEnergy G ω := by
        simpa [K] using sqRowEnergy_movingAverageCutoff_le T n hG_prog hG_bdd hG_cutoff ω
  -- Proof comment: the general row-energy-to-ambient bridge now turns the deterministic rowwise
  -- square integrability and the integrable row-energy majorant into ambient `L²`.
  exact memLp_of_sqRowEnergy_integrable μ hK_aesm hrow_int hRowEnergy_int_K

/-- Helper for Theorem 25.9: the active dyadic cutoff horizon is the deterministic terminal time
`T + 1 / (n + 1)`. -/
private def dyadicMovingAverageCutoffHorizon (T : NNReal) (n : ℕ) : NNReal :=
  T + 1 / (n + 1 : NNReal)

/-- Helper for Theorem 25.9: the dyadic partition points are the uniform mesh points on the active
cutoff horizon. -/
private def dyadicMovingAverageCutoffTimes (T : NNReal) (n m : ℕ) :
    Fin (2 ^ m + 1) → NNReal :=
  fun j ↦ (j : NNReal) * (dyadicMovingAverageCutoffHorizon T n / (2 ^ m : NNReal))

/-- Helper for Theorem 25.9: each dyadic coefficient is the moving-average cutoff sampled at the
left endpoint of the corresponding dyadic strip. -/
private def dyadicMovingAverageCutoffCoeff (G : Process) (T : NNReal) (n m : ℕ) :
    Fin (2 ^ m) → Ω → ℝ :=
  fun i ω ↦ movingAverageCutoff G T n (dyadicMovingAverageCutoffTimes T n m i.castSucc) ω

/-- Helper for Theorem 25.9: the dyadic partition begins at time `0`. -/
private theorem dyadicMovingAverageCutoffTimes_zero (T : NNReal) (n m : ℕ) :
    dyadicMovingAverageCutoffTimes T n m 0 = 0 := by
  -- Proof comment: the zeroth mesh point is the origin by direct evaluation.
  simp [dyadicMovingAverageCutoffTimes]

/-- Helper for Theorem 25.9: the dyadic partition points increase strictly along the positive
common mesh of the active cutoff horizon. -/
private theorem dyadicMovingAverageCutoffTimes_strictMono (T : NNReal) (n m : ℕ) :
    StrictMono (dyadicMovingAverageCutoffTimes T n m) := by
  intro i j hij
  have hstep_pos :
      0 < dyadicMovingAverageCutoffHorizon T n / (2 ^ m : NNReal) := by
    -- Proof comment: both the cutoff horizon and the dyadic denominator are strictly positive.
    dsimp [dyadicMovingAverageCutoffHorizon]
    positivity
  -- Proof comment: multiplying the strictly increasing index map by a positive mesh preserves the
  -- strict order of partition points.
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hstep_pos

/-- Helper for Theorem 25.9: the dyadic coefficient family inherits the deterministic uniform
bound of the moving-average cutoff row. -/
private theorem dyadicMovingAverageCutoffCoeff_bounded
    {G : Process} (T : NNReal) (n m : ℕ)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∀ i, ∃ C : ℝ, ∀ ω, |dyadicMovingAverageCutoffCoeff G T n m i ω| ≤ C := by
  rcases movingAverageCutoff_hasBound T n hG_bdd hG_cutoff with ⟨C, _, hC⟩
  intro i
  refine ⟨C, ?_⟩
  intro ω
  -- Proof comment: each coefficient is exactly one fixed-time sample of the already bounded
  -- moving-average cutoff row.
  simpa [dyadicMovingAverageCutoffCoeff] using
    hC (dyadicMovingAverageCutoffTimes T n m i.castSucc) ω

/-- Helper for Theorem 25.9: each dyadic left-endpoint coefficient is measurable at the left
filtration time of its strip. -/
private theorem dyadicMovingAverageCutoffCoeff_measurable
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∀ i, Measurable[ℱ (dyadicMovingAverageCutoffTimes T n m i.castSucc)]
      (dyadicMovingAverageCutoffCoeff G T n m i) := by
  intro i
  -- Proof comment: the coefficients are sampled exactly at the left endpoints, so the existing
  -- fixed-time measurability lemma applies without any additional transport.
  simpa [dyadicMovingAverageCutoffCoeff] using
    movingAverageCutoff_measurable_fixedTime T n hG_prog hG_cutoff
      (dyadicMovingAverageCutoffTimes T n m i.castSucc)

/-- Helper for Theorem 25.9: the deterministic dyadic partition of the active cutoff horizon
`[0, T + 1 / (n + 1)]` packages the left-endpoint samples of `movingAverageCutoff G T n` into a
canonical predictable-step representation. -/
private def dyadicRepresentationOfMovingAverageCutoff
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    PredictableStepRepresentation ℱ :=
  -- Proof comment: the dyadic representation is a proof-free package assembled from the mesh,
  -- the left-endpoint samples, and the previously isolated monotonicity/boundedness/measurability
  -- interface lemmas.
  predictableStepRepresentationOfPartition
    (dyadicMovingAverageCutoffTimes T n m)
    (dyadicMovingAverageCutoffTimes_zero T n m)
    (dyadicMovingAverageCutoffTimes_strictMono T n m)
    (dyadicMovingAverageCutoffCoeff G T n m)
    (dyadicMovingAverageCutoffCoeff_bounded T n m hG_bdd hG_cutoff)
    (dyadicMovingAverageCutoffCoeff_measurable ℱ T n m hG_prog hG_cutoff)

/-- Helper for Theorem 25.9: the left endpoint of the `i`-th dyadic strip is the `i`-th mesh
point of the active cutoff horizon. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_times_castSucc_eq
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (i :
      Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n) :
    (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
      i.castSucc : NNReal) : ℝ) =
      (i : ℝ) * (((T + 1 / (n + 1 : NNReal)) : ℝ) / (2 ^ m : ℝ)) := by
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  -- Proof comment: unfolding the packaged dyadic representation once exposes the deterministic
  -- partition formula for the left endpoint.
  simpa [data, dyadicRepresentationOfMovingAverageCutoff,
    predictableStepRepresentationOfPartition, dyadicMovingAverageCutoffTimes,
    dyadicMovingAverageCutoffHorizon]

/-- Helper for Theorem 25.9: the right endpoint of the `i`-th dyadic strip is the next mesh point
of the active cutoff horizon. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_times_succ_eq
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (i :
      Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n) :
    (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
      i.succ : NNReal) : ℝ) =
      ((i : ℕ) + 1 : ℝ) * (((T + 1 / (n + 1 : NNReal)) : ℝ) / (2 ^ m : ℝ)) := by
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  -- Proof comment: the successor partition point is one mesh step to the right of the left
  -- endpoint, so the same single unfold gives the explicit formula.
  simpa [data, dyadicRepresentationOfMovingAverageCutoff,
    predictableStepRepresentationOfPartition, dyadicMovingAverageCutoffTimes,
    dyadicMovingAverageCutoffHorizon, Nat.cast_add, Nat.cast_one]

/-- Helper for Theorem 25.9: each dyadic coefficient is the moving-average cutoff sampled at the
left endpoint of its strip. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_coeff_eq
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (i :
      Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n)
    (ω : Ω) :
    ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).coeff i) ω =
      movingAverageCutoff G T n
        ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
          i.castSucc) ω := by
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  -- Proof comment: the packaged coefficient field was defined exactly as the left-endpoint sample
  -- of the moving-average cutoff.
  simpa [data, dyadicRepresentationOfMovingAverageCutoff,
    predictableStepRepresentationOfPartition, dyadicMovingAverageCutoffCoeff]

/-- Helper for Theorem 25.9: the terminal dyadic partition point is the active cutoff horizon
`T + 1 / (n + 1)`. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_times_last_eq
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
        (Fin.last
          (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n) =
      T + 1 / (n + 1 : NNReal) := by
  apply NNReal.coe_injective
  simp [dyadicRepresentationOfMovingAverageCutoff, predictableStepRepresentationOfPartition,
    dyadicMovingAverageCutoffTimes, dyadicMovingAverageCutoffHorizon]
  field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]

/-- Helper for Theorem 25.9: every dyadic left-endpoint coefficient of the moving-average cutoff
representation is square-integrable under `μ`. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_coeff_memLp
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (i :
      Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n) :
    MemLp
      ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).coeff i)
      (2 : ℝ≥0∞) μ := by
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  -- Proof comment: each coefficient is a deterministic fixed-time sample of the moving-average
  -- cutoff row, so the already established fixed-time `L²(μ)` bridge applies directly.
  simpa [data, dyadicRepresentationOfMovingAverageCutoff] using
    memLp_fixedTime_movingAverageCutoff μ T n hG_prog hG_memLp hG_bdd hG_cutoff
      (data.times i.castSucc)

/-- Helper for Theorem 25.9: the row energy of each dyadic left-endpoint approximation to
`movingAverageCutoff G T n` is uniformly controlled by `sqRowEnergy G`. -/
private theorem sqRowEnergy_dyadicRepresentationOfMovingAverageCutoff_le
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    sqRowEnergy
        (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess ω ≤
      (((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) * sqRowEnergy G ω := by
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  have hlength :
      ∀ i : Fin data.n,
        (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)) =
          (S : ℝ) / (2 ^ m : ℝ) := by
    intro i
    have hstep :
        data.times i.castSucc ≤ data.times i.succ := by
      exact le_of_lt (data.times_strictMono i.castSucc_lt_succ)
    let mesh : ℝ := (S : ℝ) / (2 ^ m : ℝ)
    have hsucc :
        (data.times i.succ : ℝ) = ((i : ℕ) + 1 : ℝ) * mesh := by
      -- Proof comment: the dyadic partition times are the integer multiples of the common mesh.
      simpa [mesh, S] using
        dyadicRepresentationOfMovingAverageCutoff_times_succ_eq
          ℱ T n m hG_prog hG_bdd hG_cutoff i
    have hcastSucc :
        (data.times i.castSucc : ℝ) = (i : ℝ) * mesh := by
      -- Proof comment: the left endpoint of the `i`-th strip is the `i`-th dyadic mesh point.
      simpa [mesh, S] using
        dyadicRepresentationOfMovingAverageCutoff_times_castSucc_eq
          ℱ T n m hG_prog hG_bdd hG_cutoff i
    rw [NNReal.coe_sub hstep, hsucc, hcastSucc]
    ring
  have hsum_lengths :
      ∑ i : Fin data.n, (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)) = (S : ℝ) := by
    calc
      ∑ i : Fin data.n, (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ))
          = ∑ i : Fin data.n, (S : ℝ) / (2 ^ m : ℝ) := by
              -- Proof comment: every strip of the dyadic partition has the same deterministic
              -- mesh size.
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hlength i
      _ = (data.n : ℝ) * ((S : ℝ) / (2 ^ m : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (2 ^ m : ℝ) * ((S : ℝ) / (2 ^ m : ℝ)) := by
            simp [data, dyadicRepresentationOfMovingAverageCutoff,
              predictableStepRepresentationOfPartition]
      _ = (S : ℝ) := by
            field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
  calc
    sqRowEnergy data.toProcess ω =
        ∑ i : Fin data.n,
          (data.coeff i ω) ^ 2 *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
      -- Proof comment: the row energy of a predictable-step process is the sum of the coefficient
      -- squares weighted by the strip lengths.
      exact predictableStepRepresentation_sqRowEnergy_eq_sum data ω
    _ ≤
        ∑ i : Fin data.n,
          ((n + 1 : ℝ) * sqRowEnergy G ω) *
            ((data.times i.succ - data.times i.castSucc : NNReal) : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcoeff :
              (data.coeff i ω) ^ 2 ≤ (n + 1 : ℝ) * sqRowEnergy G ω := by
            -- Proof comment: each dyadic coefficient is one fixed-time sample of the moving
            -- average, so the fixed-time row-energy estimate applies directly.
            simpa [data, dyadicRepresentationOfMovingAverageCutoff] using
              movingAverageCutoff_fixedTime_sq_le_rowEnergy
                T n hG_prog hG_bdd hG_cutoff (data.times i.castSucc) ω
          have hlen_nonneg :
              0 ≤ (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)) := by
            positivity
          exact mul_le_mul_of_nonneg_right hcoeff hlen_nonneg
    _ = ((n + 1 : ℝ) * sqRowEnergy G ω) *
          ∑ i : Fin data.n, (((data.times i.succ - data.times i.castSucc : NNReal) : ℝ)) := by
          rw [Finset.mul_sum]
    _ = ((n + 1 : ℝ) * sqRowEnergy G ω) * (S : ℝ) := by rw [hsum_lengths]
    _ = (((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) * sqRowEnergy G ω := by
          simp [S]
          ring

/-- Helper for Theorem 25.9: the dyadic mesh on a fixed deterministic horizon tends to `0`. -/
private theorem tendsto_dyadicMesh_zero (S : NNReal) :
    Filter.Tendsto (fun m : ℕ ↦ (S : ℝ) / (2 ^ m : ℝ)) Filter.atTop (𝓝 0) := by
  have hpow :
      Filter.Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) Filter.atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul :
      Filter.Tendsto (fun m : ℕ ↦ (S : ℝ) * (1 / 2 : ℝ) ^ m) Filter.atTop (𝓝 ((S : ℝ) * 0)) :=
    tendsto_const_nhds.mul hpow
  have hEq :
      (fun m : ℕ ↦ (S : ℝ) / (2 ^ m : ℝ)) = fun m ↦ (S : ℝ) * (1 / 2 : ℝ) ^ m := by
    funext m
    simp [div_eq_mul_inv, one_div, inv_pow]
  rw [hEq]
  simpa using hmul

/-- Helper for Theorem 25.9: every dyadic left-endpoint step row stays under the same deterministic
bound as the moving-average cutoff it samples. -/
private theorem abs_toProcess_dyadicRepresentationOfMovingAverageCutoff_le
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    {C : ℝ}
    (hC :
      ∀ t ω, |movingAverageCutoff G T n t ω| ≤ C) :
    ∀ t ω,
      |(dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess t ω| ≤
        C := by
  intro t ω
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  by_cases hAfter : S < t
  · have hlast_eq : data.times (Fin.last data.n) = S := by
      simpa [data, S] using
        dyadicRepresentationOfMovingAverageCutoff_times_last_eq
          ℱ T n m hG_prog hG_bdd hG_cutoff
    have hlast : data.times (Fin.last data.n) < t := by
      simpa [hlast_eq] using hAfter
    have hzero : data.toProcess t ω = 0 := data.toProcess_eq_zero_of_last_lt hlast ω
    have hC_nonneg : 0 ≤ C := by
      exact le_trans (abs_nonneg (movingAverageCutoff G T n 0 ω)) (hC 0 ω)
    -- Proof comment: once time is past the last dyadic partition point, the step process is
    -- identically zero.
    rw [hzero]
    simpa using hC_nonneg
  · have ht_le : t ≤ S := le_of_not_gt hAfter
    by_cases ht0 : t = 0
    · subst ht0
      have hC_nonneg : 0 ≤ C := by
        exact le_trans (abs_nonneg (movingAverageCutoff G T n 0 ω)) (hC 0 ω)
      -- Proof comment: every half-open strip starts strictly after `0`, so the dyadic process
      -- vanishes at the initial time.
      simpa [PredictableStepRepresentation.toProcess_apply] using hC_nonneg
    · have ht_pos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht0)
      have hlast_eq : data.times (Fin.last data.n) = S := by
        simpa [data, S] using
          dyadicRepresentationOfMovingAverageCutoff_times_last_eq
            ℱ T n m hG_prog hG_bdd hG_cutoff
      have ht_last : t ≤ data.times (Fin.last data.n) := by
        simpa [hlast_eq] using ht_le
      obtain ⟨i, hti⟩ := data.exists_mem_interval_of_pos_le_last ht_pos ht_last
      have hproc : data.toProcess t ω = data.coeff i ω :=
        data.toProcess_eq_coeff_of_mem_interval i hti ω
      -- Proof comment: on the active dyadic strip, the step value is exactly the sampled
      -- left-endpoint moving-average value, which inherits the same deterministic bound.
      calc
        |data.toProcess t ω| = |data.coeff i ω| := by rw [hproc]
        _ ≤ C := by
          simpa [data, dyadicRepresentationOfMovingAverageCutoff] using hC (data.times i.castSucc) ω

/-- Helper for Theorem 25.9: fixing the sample point turns the dyadic predictable-step
approximation into a measurable real-time path. -/
private theorem measurable_realPath_dyadicRepresentationOfMovingAverageCutoff
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    Measurable
      (fun t : ℝ ↦
        processToTimeSpaceFun
          (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess
          (ω, t)) := by
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  have hEq :
      (fun t : ℝ ↦ processToTimeSpaceFun data.toProcess (ω, t)) =
        fun t : ℝ ↦
          ∑ i,
            data.coeff i ω *
              Set.indicator
                (Set.Ioc ((data.times i.castSucc : NNReal) : ℝ) (data.times i.succ))
                (fun _ : ℝ ↦ (1 : ℝ)) t := by
    funext t
    -- Proof comment: after moving to `Ω × ℝ`, `processToTimeSpaceFun` only inserts the `toNNReal`
    -- clamp, and the dyadic step process is still the same finite indicator sum strip by strip.
    simp [processToTimeSpaceFun, PredictableStepRepresentation.toProcess_apply,
      realIndicator_eq_nnrealIndicator]
  rw [hEq]
  refine Finset.measurable_fun_sum _ fun i _ ↦ ?_
  exact measurable_const.mul (Measurable.indicator measurable_const measurableSet_Ioc)

/-- Helper for Theorem 25.9: for each sample point `ω`, the dyadic left-endpoint step rows should
converge for `dt`-almost every nonnegative time to the bounded moving-average cutoff path. -/
private theorem dyadicLeftEndpointSub_le_mesh_of_mem_interval
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    {t : ℝ} (ht0 : 0 ≤ t)
    (i : Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n)
    (hti : t.toNNReal ∈ Set.Ioc
      ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
        i.castSucc)
      ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
        i.succ)) :
    0 ≤
        t -
          (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
            i.castSucc : NNReal) : ℝ) ∧
      t -
          (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
            i.castSucc : NNReal) : ℝ) ≤
        ((T + 1 / (n + 1 : NNReal)) : ℝ) / (2 ^ m : ℝ) := by
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  let mesh : ℝ := (S : ℝ) / (2 ^ m : ℝ)
  have hti_real :
      t ∈ Set.Ioc (((data.times i.castSucc : NNReal) : ℝ)) (data.times i.succ) := by
    simpa [data, Real.toNNReal_of_nonneg ht0] using hti
  have hsucc :
      (data.times i.succ : ℝ) = ((i : ℕ) + 1 : ℝ) * mesh := by
    -- Proof comment: the upper endpoint of the `i`-th strip is the next dyadic mesh point.
    simpa [data, mesh, S] using
      dyadicRepresentationOfMovingAverageCutoff_times_succ_eq
        ℱ T n m hG_prog hG_bdd hG_cutoff i
  have hcastSucc :
      (((data.times i.castSucc : NNReal) : ℝ)) = (i : ℝ) * mesh := by
    -- Proof comment: the chosen left endpoint is the current dyadic mesh point.
    simpa [data, mesh, S] using
      dyadicRepresentationOfMovingAverageCutoff_times_castSucc_eq
        ℱ T n m hG_prog hG_bdd hG_cutoff i
  constructor
  · -- Proof comment: strip membership forces the left endpoint to lie no later than `t`.
    linarith [hti_real.1]
  · have hsub :
        t - (((data.times i.castSucc : NNReal) : ℝ)) ≤
          (data.times i.succ : ℝ) - (((data.times i.castSucc : NNReal) : ℝ)) := by
      linarith [hti_real.2]
    have hmesh :
        (data.times i.succ : ℝ) - (((data.times i.castSucc : NNReal) : ℝ)) = mesh := by
      rw [hsucc, hcastSucc]
      ring
    -- Proof comment: the whole strip has length exactly one mesh, so the predecessor-point error
    -- is bounded by that mesh.
    rw [hmesh] at hsub
    simpa [mesh, S] using hsub

/-- Helper for Theorem 25.9: for a fixed positive time in the active cutoff strip, any sequence of
dyadic predecessor points converges to that time. -/
private theorem tendsto_dyadicChosenLeftEndpoint_of_pos_le_cutoff
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    {t : ℝ} (ht_pos : 0 < t)
    (ht_le : t ≤ ((T + 1 / (n + 1 : NNReal)) : ℝ))
    (i :
      ∀ m,
        Fin (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).n)
    (hi :
      ∀ m,
        t.toNNReal ∈ Set.Ioc
          ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
            (i m).castSucc)
          ((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
            (i m).succ)) :
    Filter.Tendsto
      (fun m ↦
        (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
          (i m).castSucc : NNReal) : ℝ))
      Filter.atTop (𝓝 t) := by
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let left : ℕ → ℝ := fun m ↦
    (((dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).times
      (i m).castSucc : NNReal) : ℝ)
  have hsub_bound :
      ∀ m, 0 ≤ t - left m ∧ t - left m ≤ (S : ℝ) / (2 ^ m : ℝ) := by
    intro m
    -- Proof comment: the chosen predecessor point lies in the unique dyadic strip containing `t`,
    -- so the distance to `t` is bounded by one mesh width.
    simpa [left, S] using
      dyadicLeftEndpointSub_le_mesh_of_mem_interval
        ℱ T n m hG_prog hG_bdd hG_cutoff (le_of_lt ht_pos) (i m) (hi m)
  have hsub_tendsto :
      Filter.Tendsto (fun m ↦ t - left m) Filter.atTop (𝓝 0) := by
    -- Proof comment: the dyadic mesh tends to `0`, and the predecessor-point error is squeezed
    -- between `0` and that mesh.
    apply squeeze_zero
    · intro m
      exact (hsub_bound m).1
    · intro m
      exact (hsub_bound m).2
    · simpa [S] using tendsto_dyadicMesh_zero S
  -- Proof comment: the predecessor-point error tending to `0` is equivalent to the left endpoints
  -- themselves converging to `t`.
  have hleft_tendsto :
      Filter.Tendsto (fun m ↦ t - (t - left m)) Filter.atTop (𝓝 t) := by
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ t) Filter.atTop (𝓝 t)).sub
        hsub_tendsto)
  refine Filter.Tendsto.congr' ?_ hleft_tendsto
  exact Filter.Eventually.of_forall fun m ↦ by
    dsimp [left]
    ring

/-- Helper for Theorem 25.9: at each positive time in the active strip, the dyadic left-endpoint
step rows converge pointwise to the moving-average cutoff row. -/
private theorem tendsto_processToTimeSpaceFun_dyadicRepresentationOfMovingAverageCutoff_at_pos
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) {t : ℝ} (ht_pos : 0 < t)
    (ht_le : t ≤ ((T + 1 / (n + 1 : NNReal)) : ℝ)) :
    Filter.Tendsto
      (fun m ↦
        processToTimeSpaceFun
          (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess
          (ω, t))
      Filter.atTop
      (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))) := by
  classical
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : ℕ → PredictableStepRepresentation ℱ := fun m ↦
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  let i : ∀ m, Fin (data m).n := fun m ↦
    Classical.choose <|
      (data m).exists_mem_interval_of_pos_le_last
        (by
          have ht_pos_nnreal : 0 < t.toNNReal := by
            simpa [Real.toNNReal_of_nonneg (le_of_lt ht_pos)] using ht_pos
          exact ht_pos_nnreal)
        (by
          have ht_le_last : t.toNNReal ≤ (data m).times (Fin.last (data m).n) := by
            simpa [data, S, Real.toNNReal_of_nonneg (le_of_lt ht_pos),
              dyadicRepresentationOfMovingAverageCutoff_times_last_eq
                ℱ T n m hG_prog hG_bdd hG_cutoff] using ht_le
          exact ht_le_last)
  let hi :
      ∀ m,
        t.toNNReal ∈ Set.Ioc ((data m).times (i m).castSucc) ((data m).times (i m).succ) :=
    fun m ↦
      Classical.choose_spec <|
        (data m).exists_mem_interval_of_pos_le_last
          (by
            have ht_pos_nnreal : 0 < t.toNNReal := by
              simpa [Real.toNNReal_of_nonneg (le_of_lt ht_pos)] using ht_pos
            exact ht_pos_nnreal)
          (by
            have ht_le_last : t.toNNReal ≤ (data m).times (Fin.last (data m).n) := by
              simpa [data, S, Real.toNNReal_of_nonneg (le_of_lt ht_pos),
                dyadicRepresentationOfMovingAverageCutoff_times_last_eq
                  ℱ T n m hG_prog hG_bdd hG_cutoff] using ht_le
            exact ht_le_last)
  let leftNN : ℕ → NNReal := fun m ↦ (data m).times (i m).castSucc
  let left : ℕ → ℝ := fun m ↦ (leftNN m : ℝ)
  have hleft_tendsto :
      Filter.Tendsto (fun m ↦ left m) Filter.atTop (𝓝 t) := by
    -- Proof comment: the predecessor points sit within one dyadic mesh of `t`, so they converge
    -- to `t` as the mesh goes to zero.
    simpa [left, leftNN, data] using
      tendsto_dyadicChosenLeftEndpoint_of_pos_le_cutoff
        ℱ T n hG_prog hG_bdd hG_cutoff ht_pos ht_le i hi
  have hcont :
      Continuous fun s : ℝ ↦ processToTimeSpaceFun (movingAverageCutoff G T n) (ω, s) := by
    -- Proof comment: continuity of the cutoff path over `NNReal` transfers to real time after
    -- composing with `Real.toNNReal`.
    simpa [processToTimeSpaceFun] using
      (movingAverageCutoff_continuousPath T n hG_prog hG_bdd ω).comp continuous_real_toNNReal
  have hcontAt :
      ContinuousAt (fun s : ℝ ↦ processToTimeSpaceFun (movingAverageCutoff G T n) (ω, s)) t :=
    hcont.continuousAt
  have htarget :
      Filter.Tendsto
        (fun m ↦ processToTimeSpaceFun (movingAverageCutoff G T n) (ω, left m))
        Filter.atTop
        (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))) := by
    exact hcontAt.tendsto.comp hleft_tendsto
  have hrow_eq :
      ∀ m,
        processToTimeSpaceFun (data m).toProcess (ω, t) =
          processToTimeSpaceFun (movingAverageCutoff G T n) (ω, left m) := by
    intro m
    have hproc : (data m).toProcess t.toNNReal ω = (data m).coeff (i m) ω :=
      (data m).toProcess_eq_coeff_of_mem_interval (i m) (hi m) ω
    have hcoeff :
        (data m).coeff (i m) ω =
          movingAverageCutoff G T n ((data m).times (i m).castSucc) ω := by
      -- Proof comment: the dyadic row stores exactly the left-endpoint moving-average sample as
      -- its `coeff` field.
      simpa [data] using
        dyadicRepresentationOfMovingAverageCutoff_coeff_eq
          ℱ T n m hG_prog hG_bdd hG_cutoff (i m) ω
    -- Proof comment: on the chosen strip, the dyadic step row is exactly the left-endpoint sample
    -- of the moving-average cutoff.
    calc
      processToTimeSpaceFun (data m).toProcess (ω, t)
          = (data m).toProcess t.toNNReal ω := by
              simp [processToTimeSpaceFun]
      _ = (data m).coeff (i m) ω := hproc
      _ = movingAverageCutoff G T n ((data m).times (i m).castSucc) ω := hcoeff
      _ = movingAverageCutoff G T n (leftNN m) ω := by simp [leftNN]
      _ = processToTimeSpaceFun (movingAverageCutoff G T n) (ω, left m) := by
            simp [processToTimeSpaceFun, left, leftNN]
  -- Proof comment: rewrite the dyadic row as evaluation of the continuous cutoff path at the
  -- predecessor points, then compose the path continuity with predecessor-point convergence.
  have hrow_tendsto :
      Filter.Tendsto
        (fun m ↦ processToTimeSpaceFun (data m).toProcess (ω, t))
        Filter.atTop
        (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))) := by
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun m ↦ (hrow_eq m).symm) htarget
  simpa [data] using hrow_tendsto

private theorem ae_tendsto_processToTimeSpaceFun_dyadicRepresentationOfMovingAverageCutoff
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∀ ω : Ω,
      ∀ᵐ t ∂ ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))),
        Filter.Tendsto
          (fun m ↦
            processToTimeSpaceFun
              (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess
              (ω, t))
          Filter.atTop
          (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))) := by
  intro ω
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : ℕ → PredictableStepRepresentation ℱ := fun m ↦
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  have hzero_ae : ∀ᵐ t ∂ ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))), t ≠ 0 := by
    change ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))), t ≠ 0
    rw [ae_iff]
    simp [measurableSet_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ici, hzero_ae] with t ht0 hzero
  by_cases ht : t ≤ S
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hzero)
    -- Proof comment: on the active strip `[0, T + 1 / (n + 1)]`, the dyadic rows sample the
    -- continuous cutoff path at predecessor points whose mesh tends to zero.
    simpa [S] using
      tendsto_processToTimeSpaceFun_dyadicRepresentationOfMovingAverageCutoff_at_pos
        ℱ T n hG_prog hG_bdd hG_cutoff ω ht_pos ht
  · have hAfter : (S : ℝ) < t := lt_of_not_ge ht
    have htarget_zero : processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) = 0 := by
      have hineq :
          T + (1 / (n + 1 : NNReal)) ≤ t.toNNReal := by
        simpa [S, Real.toNNReal_of_nonneg ht0] using le_of_lt hAfter
      -- Proof comment: once the observation time lies beyond the active cutoff horizon, the
      -- target moving-average row vanishes identically.
      simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using
        movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff hineq ω
    have hconst :
        Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop
          (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))) := by
      simpa [htarget_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0))
    refine hconst.congr' ?_
    refine Filter.Eventually.of_forall fun m ↦ ?_
    have hAfter_nn : S < t.toNNReal := by
      simpa [Real.toNNReal_of_nonneg ht0] using hAfter
    have hlast : (data m).times (Fin.last (data m).n) < t.toNNReal := by
      simpa [data, S, dyadicRepresentationOfMovingAverageCutoff_times_last_eq
        ℱ T n m hG_prog hG_bdd hG_cutoff] using hAfter_nn
    have hzero_row : (data m).toProcess t.toNNReal ω = 0 :=
      (data m).toProcess_eq_zero_of_last_lt hlast ω
    -- Proof comment: after the last dyadic partition point, each dyadic step row is identically
    -- zero, so the whole sequence is eventually constant at the target value `0`.
    simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hzero_row.symm

/-- Helper for Theorem 25.9: for each fixed sample point, the dyadic approximation error to the
moving-average cutoff has vanishing row energy. -/
private theorem dyadicRepresentationOfMovingAverageCutoff_error_sqRowEnergy_tendsto_zero
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    Filter.Tendsto
      (fun m ↦
        sqRowEnergy
          (fun t ω' ↦
            (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess t ω' -
              movingAverageCutoff G T n t ω') ω)
      Filter.atTop (𝓝 0) := by
  have hG_bdd' := hG_bdd
  rcases movingAverageCutoff_hasBound T n hG_bdd hG_cutoff with ⟨C, hC_nonneg, hC⟩
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let K : Process := movingAverageCutoff G T n
  let data : ℕ → PredictableStepRepresentation ℱ := fun m ↦
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  let E : ℕ → Process := fun m t ω' ↦ (data m).toProcess t ω' - K t ω'
  let F : ℕ → ℝ → ℝ := fun m t ↦ (processToTimeSpaceFun (E m) (ω, t)) ^ 2
  let bound : ℝ → ℝ :=
    Set.indicator (Set.Icc (0 : ℝ) S) (fun _ ↦ (2 * C) ^ 2)
  have hK_prog : ProgMeasurable ℱ K := by
    simpa [K] using progMeasurable_movingAverageCutoff T n hG_prog hG_bdd' hG_cutoff
  have hData_prog : ∀ m, ProgMeasurable ℱ (data m).toProcess := by
    intro m
    simpa using (data m).isPredictable_toProcess.progMeasurable
  have hData_bdd : ∀ m, ∀ t ω', |(data m).toProcess t ω'| ≤ C := by
    intro m t ω'
    exact abs_toProcess_dyadicRepresentationOfMovingAverageCutoff_le
      ℱ T n m hG_prog hG_bdd hG_cutoff hC t ω'
  have hData_cutoff :
      ∀ m, ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → (data m).toProcess t ω' = 0 := by
    intro m t ω' ht
    have hlast : (data m).times (Fin.last (data m).n) < t := by
      simpa [data, S, dyadicRepresentationOfMovingAverageCutoff_times_last_eq
        ℱ T n m hG_prog hG_bdd hG_cutoff] using ht
    exact (data m).toProcess_eq_zero_of_last_lt hlast ω'
  have hK_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |K t ω'| ≤ C' := by
    simpa [K] using movingAverageCutoff_hasBound T n hG_bdd' hG_cutoff
  have hK_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → K t ω' = 0 := by
    intro t ω' ht
    simpa [K, S] using
      movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff (le_of_lt ht) ω'
  have hE_prog : ∀ m, ProgMeasurable ℱ (E m) := by
    intro m
    simpa [E, K, sub_eq_add_neg] using (hData_prog m).sub hK_prog
  have hE_bound : ∀ m, ∀ t ω', |E m t ω'| ≤ 2 * C := by
    intro m
    intro t ω'
    -- Proof comment: both the dyadic step row and the moving-average cutoff row share the same
    -- deterministic bound `C`, so their difference is bounded by `2C`.
    calc
      |E m t ω'| = |(data m).toProcess t ω' - K t ω'| := by rfl
      _ ≤ |(data m).toProcess t ω'| + |K t ω'| := by
            simpa using abs_sub_le ((data m).toProcess t ω') 0 (K t ω')
      _ ≤ C + C := add_le_add (hData_bdd m t ω') (by simpa [K] using hC t ω')
      _ = 2 * C := by ring
  have hE_bdd : ∀ m, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |E m t ω'| ≤ C' := by
    intro m
    exact ⟨2 * C, by positivity, hE_bound m⟩
  have hE_cutoff :
      ∀ m, ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → E m t ω' = 0 := by
    intro m t ω' ht
    simp [E, hData_cutoff m ht, hK_cutoff ht]
  have hF_meas : ∀ m, AEStronglyMeasurable (F m) ν := by
    intro m
    have hE_meas : Measurable (fun t : ℝ ↦ E m t.toNNReal ω) := by
      simpa [E, processToTimeSpaceFun] using measurable_realPath_of_progMeasurable (hE_prog m) ω
    -- Proof comment: fixing the sample point turns the dyadic error row into a measurable real
    -- path, and squaring preserves a.e.-strong measurability on `[0,∞)`.
    simpa [F, processToTimeSpaceFun] using (hE_meas.pow_const 2).aestronglyMeasurable
  have hbound_int : Integrable bound ν := by
    have hsubset : Set.Icc (0 : ℝ) S ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      exact ht.1
    have hfinite : ν (Set.Icc (0 : ℝ) S) ≠ ∞ := by
      simpa [ν, Set.inter_eq_left.mpr hsubset] using
        (measure_Icc_lt_top (a := (0 : ℝ)) (b := (S : ℝ))).ne
    -- Proof comment: the common support strip `[0,S]` has finite Lebesgue measure, so the
    -- constant square bound is integrable there.
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (μ := ν) (s := Set.Icc (0 : ℝ) S) (C := (2 * C) ^ 2) hfinite
  have h_bound : ∀ m, ∀ᵐ t ∂ν, ‖F m t‖ ≤ bound t := by
    intro m
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with t ht0
    by_cases hstrip : t ≤ S
    · have hE_bound' : |processToTimeSpaceFun (E m) (ω, t)| ≤ 2 * C := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using
          hE_bound m t.toNNReal ω
      have hsq :
          (processToTimeSpaceFun (E m) (ω, t)) ^ 2 ≤ (2 * C) ^ 2 := by
        have hlow :
            -(2 * C) ≤ processToTimeSpaceFun (E m) (ω, t) := (abs_le.mp hE_bound').1
        have hupp :
            processToTimeSpaceFun (E m) (ω, t) ≤ 2 * C := (abs_le.mp hE_bound').2
        nlinarith
      have hbound_mem : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0, hstrip⟩
      have hF_nonneg : 0 ≤ F m t := sq_nonneg _
      -- Proof comment: on the common active strip, the dyadic error row is uniformly bounded by
      -- `2C`, so its square is dominated by `(2C)^2`.
      calc
        ‖F m t‖ = F m t := by
          simp [Real.norm_eq_abs, abs_of_nonneg hF_nonneg]
        _ ≤ (2 * C) ^ 2 := by
          simpa [F] using hsq
        _ = bound t := by
          simp [bound, hbound_mem]
    · have ht_gt : (S : ℝ) < t := lt_of_not_ge hstrip
      have hzero' : E m t.toNNReal ω = 0 := by
        have ht_nn : S < t.toNNReal := by
          rw [Real.toNNReal_of_nonneg ht0]
          exact ht_gt
        exact hE_cutoff m ht_nn
      have hzero'' : E m ⟨t, ht0⟩ ω = 0 := by
        simpa [Real.toNNReal_of_nonneg ht0] using hzero'
      have hzero : processToTimeSpaceFun (E m) (ω, t) = 0 := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hzero'
      have hbound_zero : bound t = 0 := by
        have hnot_mem : t ∉ Set.Icc (0 : ℝ) S := by
          simp [ht0, hstrip]
        simp [bound, hnot_mem]
      -- Proof comment: beyond the deterministic horizon `S`, both rows vanish, so the dyadic
      -- error and the dominating indicator are both zero.
      have hF_zero : F m t = 0 := by
        dsimp [F]
        rw [hzero']
        norm_num
      rw [hF_zero, hbound_zero]
      norm_num
  have hsq_cont : Continuous fun x : ℝ ↦ x ^ 2 := by
    continuity
  have h_lim : ∀ᵐ t ∂ν, Filter.Tendsto (fun m ↦ F m t) Filter.atTop (𝓝 0) := by
    filter_upwards
      [ae_tendsto_processToTimeSpaceFun_dyadicRepresentationOfMovingAverageCutoff
        ℱ T n hG_prog hG_bdd hG_cutoff ω] with t ht
    -- Proof comment: once the dyadic row converges pathwise to `K`, subtracting the limit row and
    -- squaring sends the error path to `0`.
    have hsub :
        Filter.Tendsto
          (fun m ↦
            processToTimeSpaceFun
                (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess
                (ω, t) -
              processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))
          Filter.atTop (𝓝 0) := by
      simpa using
        ht.sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ ↦ processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))
              Filter.atTop
              (𝓝 (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))))
    simpa [F, E, K] using hsq_cont.continuousAt.tendsto.comp hsub
  have hInt :
      Filter.Tendsto (fun m ↦ ∫ t, F m t ∂ν) Filter.atTop (𝓝 (∫ t, (0 : ℝ) ∂ν)) := by
    exact tendsto_integral_of_dominated_convergence bound hF_meas hbound_int h_bound h_lim
  -- Proof comment: the row energy is exactly the time integral of the squared dyadic error path,
  -- so dominated convergence on the time variable yields the vanishing row-energy limit.
  simpa [sqRowEnergy, ν, F, E, K] using hInt

/-- Helper for Theorem 25.9: the dyadic approximation error to the moving-average cutoff is
dominated by a fixed multiple of `sqRowEnergy G`. -/
private theorem sqRowEnergy_dyadicRepresentationOfMovingAverageCutoff_sub_le
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n m : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    sqRowEnergy
        (fun t ω' ↦
          (dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff).toProcess t ω' -
            movingAverageCutoff G T n t ω') ω ≤
      (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) * sqRowEnergy G ω := by
  have hG_bdd' := hG_bdd
  rcases movingAverageCutoff_hasBound T n hG_bdd hG_cutoff with ⟨C, hC_nonneg, hC⟩
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let data : PredictableStepRepresentation ℱ :=
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  let K : Process := movingAverageCutoff G T n
  let E : Process := fun t ω' ↦ data.toProcess t ω' - K t ω'
  have hData_prog : ProgMeasurable ℱ data.toProcess := by
    simpa using data.isPredictable_toProcess.progMeasurable
  have hData_bound : ∀ t ω', |data.toProcess t ω'| ≤ C := by
    intro t ω'
    exact abs_toProcess_dyadicRepresentationOfMovingAverageCutoff_le
      ℱ T n m hG_prog hG_bdd hG_cutoff hC t ω'
  have hData_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |data.toProcess t ω'| ≤ C' := by
    exact ⟨C, hC_nonneg, hData_bound⟩
  have hData_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → data.toProcess t ω' = 0 := by
    intro t ω' ht
    have hlast : data.times (Fin.last data.n) < t := by
      simpa [data, S, dyadicRepresentationOfMovingAverageCutoff_times_last_eq
        ℱ T n m hG_prog hG_bdd hG_cutoff] using ht
    exact data.toProcess_eq_zero_of_last_lt hlast ω'
  have hK_prog : ProgMeasurable ℱ K := by
    simpa [K] using progMeasurable_movingAverageCutoff T n hG_prog hG_bdd' hG_cutoff
  have hK_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |K t ω'| ≤ C' := by
    simpa [K] using movingAverageCutoff_hasBound T n hG_bdd' hG_cutoff
  have hK_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → K t ω' = 0 := by
    intro t ω' ht
    simpa [K, S] using
      movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff (le_of_lt ht) ω'
  have hE_prog : ProgMeasurable ℱ E := by
    simpa [E, K, sub_eq_add_neg] using hData_prog.sub hK_prog
  have hE_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |E t ω'| ≤ C' := by
    refine ⟨2 * C, by positivity, ?_⟩
    intro t ω'
    -- Proof comment: both dyadic rows and moving-average rows are bounded by `C`, so the
    -- pointwise error is bounded by `2C`.
    calc
      |E t ω'| = |data.toProcess t ω' - K t ω'| := by rfl
      _ ≤ |data.toProcess t ω'| + |K t ω'| := by
            simpa using abs_sub_le (data.toProcess t ω') 0 (K t ω')
      _ ≤ C + C := add_le_add (hData_bound t ω') (by simpa [K] using hC t ω')
      _ = 2 * C := by ring
  have hE_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, S < t → E t ω' = 0 := by
    intro t ω' ht
    simp [E, hData_cutoff ht, hK_cutoff ht]
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hE_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun E (ω, s)) ^ 2) ν := by
    simpa [E, ν] using integrable_sq_realPath_on_Ici_of_bound_cutoff S hE_prog hE_bdd hE_cutoff ω
  have hData_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2) ν := by
    simpa [ν] using
      integrable_sq_realPath_on_Ici_of_bound_cutoff S hData_prog hData_bdd hData_cutoff ω
  have hK_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun K (ω, s)) ^ 2) ν := by
    simpa [K, ν] using integrable_sq_realPath_on_Ici_of_bound_cutoff S hK_prog hK_bdd hK_cutoff ω
  have hright_int :
      Integrable
        (fun s : ℝ ↦
          2 * (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun K (ω, s)) ^ 2) ν := by
    exact (hData_int.const_mul (2 : ℝ)).add (hK_int.const_mul (2 : ℝ))
  have hpointwise :
      ∀ᵐ s ∂ν,
        (processToTimeSpaceFun E (ω, s)) ^ 2 ≤
          2 * (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun K (ω, s)) ^ 2 := by
    filter_upwards with s
    have hsq :
        (processToTimeSpaceFun E (ω, s)) ^ 2 ≤
          2 * (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun K (ω, s)) ^ 2 := by
      have haux :
          (processToTimeSpaceFun data.toProcess (ω, s) -
              processToTimeSpaceFun K (ω, s)) ^ 2 ≤
            2 * (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2 +
              2 * (processToTimeSpaceFun K (ω, s)) ^ 2 := by
        nlinarith [sq_nonneg
          (processToTimeSpaceFun data.toProcess (ω, s) +
            processToTimeSpaceFun K (ω, s))]
      simpa [E, K] using haux
    exact hsq
  -- Proof comment: integrate the elementary inequality `(a - b)^2 ≤ 2 a^2 + 2 b^2` along the
  -- time row, then insert the dyadic and moving-average row-energy dominations by `sqRowEnergy G`.
  calc
    sqRowEnergy E ω = ∫ s, (processToTimeSpaceFun E (ω, s)) ^ 2 ∂ν := by
      rfl
    _ ≤
        ∫ s,
          2 * (processToTimeSpaceFun data.toProcess (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun K (ω, s)) ^ 2 ∂ν := by
          exact integral_mono_ae hE_int hright_int hpointwise
    _ = 2 * sqRowEnergy data.toProcess ω + 2 * sqRowEnergy K ω := by
          rw [integral_add (hData_int.const_mul (2 : ℝ)) (hK_int.const_mul (2 : ℝ)),
            integral_const_mul, integral_const_mul]
          rfl
    _ ≤
        2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) * sqRowEnergy G ω) +
          2 * sqRowEnergy G ω := by
            gcongr
            · simpa [data] using
                sqRowEnergy_dyadicRepresentationOfMovingAverageCutoff_le
                  ℱ T n m hG_prog hG_bdd hG_cutoff ω
            · simpa [K] using movingAverageCutoff_sqRowEnergy_le T n hG_prog hG_bdd' hG_cutoff ω
    _ = (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) * sqRowEnergy G ω := by
          ring

/-- Helper for Theorem 25.9: for a fixed moving-average row, the remaining task is the dyadic
predictable-step packaging in ambient `L²(processMeasure μ)`. -/
private theorem exists_tendsto_predictableSimpleProcessL2_of_movingAverageCutoff
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (hK_memLp :
      MemLp (processToTimeSpaceFun (movingAverageCutoff G T n))
        (2 : ℝ≥0∞) (processMeasure μ)) :
    ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
      Filter.Tendsto (fun m ↦ (Hs m : Lp ℝ 2 (processMeasure μ))) Filter.atTop
        (𝓝 (hK_memLp.toLp (processToTimeSpaceFun (movingAverageCutoff G T n)))) := by
  -- Route correction: this helper now follows the same global row-energy dominated-convergence
  -- pattern as `movingAverageCutoff_tendstoL2`; the only remaining source-facing blocker is the
  -- pathwise convergence of the dyadic left-endpoint rows.
  let K : Process := movingAverageCutoff G T n
  let S : NNReal := T + 1 / (n + 1 : NNReal)
  let dyadicData : ℕ → PredictableStepRepresentation ℱ := fun m ↦
    dyadicRepresentationOfMovingAverageCutoff ℱ T n m hG_prog hG_bdd hG_cutoff
  have hdyadicCoeff_memLp :
      ∀ m, ∀ i : Fin (dyadicData m).n, MemLp ((dyadicData m).coeff i) (2 : ℝ≥0∞) μ := by
    intro m i
    -- Proof comment: the canonical dyadic package now exposes the exact coefficient family that
    -- will feed the predictable-step `L²` constructor.
    simpa [dyadicData] using
      dyadicRepresentationOfMovingAverageCutoff_coeff_memLp
        ℱ μ T n m hG_prog hG_memLp hG_bdd hG_cutoff i
  have hdyadic_mem :
      ∀ m,
        (predictableStepRepresentation_memLp_of_sqIntegrableCoeff
          μ (dyadicData m) (hdyadicCoeff_memLp m)).toLp
            (processToTimeSpaceFun (dyadicData m).toProcess) ∈
          predictableSimpleProcessL2 ℱ μ := by
    intro m
    -- Proof comment: once the coefficients are globally in `L²(μ)`, the packaged dyadic row is
    -- already a canonical predictable simple `L²` process.
    exact predictableStepRepresentation_toLp_mem_predictableSimpleProcessL2_of_sqIntegrableCoeff
      μ (dyadicData m) (hdyadicCoeff_memLp m)
  let Hs : ℕ → predictableSimpleProcessL2 ℱ μ := fun m ↦
    ⟨(predictableStepRepresentation_memLp_of_sqIntegrableCoeff
        μ (dyadicData m) (hdyadicCoeff_memLp m)).toLp
        (processToTimeSpaceFun (dyadicData m).toProcess),
      hdyadic_mem m⟩
  let error : ℕ → Process := fun m t ω ↦ (dyadicData m).toProcess t ω - K t ω
  have hError_memLp :
      ∀ m, MemLp (processToTimeSpaceFun (error m)) (2 : ℝ≥0∞) (processMeasure μ) := by
    intro m
    -- Proof comment: subtracting the dyadic ambient `L²` row from the target cutoff row stays in
    -- ambient `L²(processMeasure μ)`.
    simpa [error, K, processToTimeSpaceFun] using
      (predictableStepRepresentation_memLp_of_sqIntegrableCoeff
        μ (dyadicData m) (hdyadicCoeff_memLp m)).sub hK_memLp
  have hRowEnergy_int :
      Integrable
        (fun ω ↦
          (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) *
            sqRowEnergy G ω) μ := by
    exact
      (sqRowEnergy_integrable_of_memLp μ hG_memLp).const_mul
        (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1))
  have hRowEnergy_bound :
      ∀ m, ∀ᵐ ω ∂μ,
        ‖sqRowEnergy (error m) ω‖ ≤
          (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) *
            sqRowEnergy G ω := by
    intro m
    filter_upwards with ω
    have hnonneg_left : 0 ≤ sqRowEnergy (error m) ω := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    have hnonneg_right :
        0 ≤
          (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) *
            sqRowEnergy G ω := by
      refine mul_nonneg ?_ ?_
      · positivity
      · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    -- Proof comment: the dyadic error row is controlled by the single row-energy majorant proved
    -- just above.
    calc
      ‖sqRowEnergy (error m) ω‖ = sqRowEnergy (error m) ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hnonneg_left]
      _ ≤
          (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) *
            sqRowEnergy G ω := by
          simpa [error, dyadicData, K] using
            sqRowEnergy_dyadicRepresentationOfMovingAverageCutoff_sub_le
              ℱ T n m hG_prog hG_bdd hG_cutoff ω
  have hRowEnergy_tendsto_zero :
      Filter.Tendsto
        (fun m ↦ ∫ ω, sqRowEnergy (error m) ω ∂μ)
        Filter.atTop (𝓝 0) := by
    have h_meas :
        ∀ m, AEStronglyMeasurable (fun ω ↦ sqRowEnergy (error m) ω) μ := by
      intro m
      exact (sqRowEnergy_integrable_of_memLp μ (hError_memLp m)).aestronglyMeasurable
    have h_lim :
        ∀ᵐ ω ∂μ,
          Filter.Tendsto (fun m ↦ sqRowEnergy (error m) ω) Filter.atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun ω ↦
        dyadicRepresentationOfMovingAverageCutoff_error_sqRowEnergy_tendsto_zero
          ℱ T n hG_prog hG_bdd hG_cutoff ω
    -- Proof comment: after rewriting the ambient squared error as the outer integral of row
    -- energies, dominated convergence on `Ω` supplies the scalar convergence to `0`.
    simpa using
      (tendsto_integral_of_dominated_convergence
        (fun ω ↦
          (2 * ((((T + 1 / (n + 1 : NNReal)) : ℝ) * (n + 1 : ℝ)) + 1)) *
            sqRowEnergy G ω)
        h_meas hRowEnergy_int hRowEnergy_bound h_lim)
  have hELpNorm_eq :
      ∀ m,
        eLpNorm
          (fun x ↦
            processToTimeSpaceFun (dyadicData m).toProcess x -
              processToTimeSpaceFun K x)
          (2 : ℝ≥0∞) (processMeasure μ) =
          ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error m) ω ∂μ)) := by
    intro m
    have hsq_eq :
        ∫ x,
            (processToTimeSpaceFun (error m) x) ^ 2
          ∂ processMeasure μ =
          ∫ ω, sqRowEnergy (error m) ω ∂μ := by
      simpa [error] using integral_sq_process_eq_integral_sqRowEnergy μ (hError_memLp m)
    calc
      eLpNorm
          (fun x ↦
            processToTimeSpaceFun (dyadicData m).toProcess x -
              processToTimeSpaceFun K x)
          (2 : ℝ≥0∞) (processMeasure μ)
          =
          ENNReal.ofReal
            ((∫ x, ‖processToTimeSpaceFun (error m) x‖ ^ ((2 : ℝ≥0∞).toReal)
                ∂ processMeasure μ) ^
              (((2 : ℝ≥0∞).toReal)⁻¹)) := by
                simpa [error, K, processToTimeSpaceFun] using
                  (MemLp.eLpNorm_eq_integral_rpow_norm
                    (μ := processMeasure μ)
                    (p := (2 : ℝ≥0∞))
                    (hp1 := by norm_num)
                    (hp2 := by norm_num)
                    (hf := hError_memLp m))
      _ =
          ENNReal.ofReal
            ((∫ x, (processToTimeSpaceFun (error m) x) ^ 2 ∂ processMeasure μ) ^
              (((2 : ℝ≥0∞).toReal)⁻¹)) := by
                congr 1
                congr 1
                refine integral_congr_ae ?_
                filter_upwards with x
                norm_num [Real.norm_eq_abs, sq_abs]
      _ = ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error m) ω ∂μ)) := by
            rw [hsq_eq]
            norm_num [Real.sqrt_eq_rpow]
  have hELpNorm :
      Filter.Tendsto
        (fun m ↦
          eLpNorm
            (fun x ↦
              processToTimeSpaceFun (dyadicData m).toProcess x -
                processToTimeSpaceFun K x)
            (2 : ℝ≥0∞) (processMeasure μ))
        Filter.atTop (𝓝 0) := by
    have hsqrt :
        Filter.Tendsto
          (fun m ↦ Real.sqrt (∫ ω, sqRowEnergy (error m) ω ∂μ))
          Filter.atTop (𝓝 0) := by
      have hsqrt_cont : Continuous fun x : ℝ ↦ Real.sqrt x := by
        continuity
      simpa using hsqrt_cont.continuousAt.tendsto.comp hRowEnergy_tendsto_zero
    have hofReal :
        Filter.Tendsto
          (fun m ↦ ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error m) ω ∂μ)))
          Filter.atTop (𝓝 0) := by
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun m ↦ (hELpNorm_eq m).symm) hofReal
  refine ⟨Hs, ?_⟩
  -- Proof comment: once the dyadic error goes to zero in ambient `L²(processMeasure μ)`, the
  -- dyadic predictable-step rows converge to the moving-average cutoff in the canonical `Lp`
  -- topology.
  simpa [Hs, K] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun m x ↦ processToTimeSpaceFun (dyadicData m).toProcess x)
      (fun m ↦ predictableStepRepresentation_memLp_of_sqIntegrableCoeff
        μ (dyadicData m) (hdyadicCoeff_memLp m))
      (processToTimeSpaceFun K) hK_memLp).2 hELpNorm

/-- Helper for Theorem 25.9: for each fixed sample point, the moving-average regularization error
has vanishing row energy. -/
private theorem movingAverageCutoff_error_sqRowEnergy_tendsto_zero
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    Filter.Tendsto
      (fun n ↦ sqRowEnergy (fun t ω' ↦ movingAverageCutoff G T n t ω' - G t ω') ω)
      Filter.atTop (𝓝 0) := by
  have hG_bdd' := hG_bdd
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  let F : ℕ → ℝ → ℝ := fun n t ↦
    (processToTimeSpaceFun (fun s ω' ↦ movingAverageCutoff G T n s ω' - G s ω') (ω, t)) ^ 2
  let bound : ℝ → ℝ :=
    Set.indicator (Set.Icc (0 : ℝ) ((T : ℝ) + 1)) (fun _ ↦ (2 * C) ^ 2)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) ν := by
    intro n
    have hK_meas :
        Measurable (fun t : ℝ ↦ movingAverageCutoff G T n t.toNNReal ω) := by
      simpa [processToTimeSpaceFun] using
        measurable_realPath_of_progMeasurable
          (progMeasurable_movingAverageCutoff T n hG_prog hG_bdd' hG_cutoff) ω
    have hG_meas : Measurable (fun t : ℝ ↦ G t.toNNReal ω) := by
      simpa [processToTimeSpaceFun] using measurable_realPath_of_progMeasurable hG_prog ω
    -- Proof comment: fixing the sample point turns the moving-average error into a measurable
    -- real path, so squaring preserves a.e.-strong measurability on `[0,∞)`.
    simpa [F, processToTimeSpaceFun] using ((hK_meas.sub hG_meas).pow_const 2).aestronglyMeasurable
  have hbound_int : Integrable bound ν := by
    have hsubset : Set.Icc (0 : ℝ) ((T : ℝ) + 1) ⊆ Set.Ici (0 : ℝ) := by
      intro t ht
      exact ht.1
    have hfinite : ν (Set.Icc (0 : ℝ) ((T : ℝ) + 1)) ≠ ∞ := by
      simpa [ν, Set.inter_eq_left.mpr hsubset] using
        (measure_Icc_lt_top (a := (0 : ℝ)) (b := (T : ℝ) + 1)).ne
    -- Proof comment: the deterministic strip `[0,T+1]` has finite Lebesgue measure, so the
    -- constant square bound is integrable there and hence as an indicator on `ν`.
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (μ := ν) (s := Set.Icc (0 : ℝ) ((T : ℝ) + 1)) (C := (2 * C) ^ 2)
      hfinite
  have h_bound : ∀ n, ∀ᵐ t ∂ν, ‖F n t‖ ≤ bound t := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with t ht0
    by_cases hstrip : t ≤ (T : ℝ) + 1
    · have hK_bound :
          |processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t)| ≤ C := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using
          abs_movingAverageCutoff_le T n hC_nonneg hC hG_cutoff t.toNNReal ω
      have hG_bound : |processToTimeSpaceFun G (ω, t)| ≤ C := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hC t.toNNReal ω
      have hsub :
          |processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
              processToTimeSpaceFun G (ω, t)| ≤ 2 * C := by
        calc
          |processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
              processToTimeSpaceFun G (ω, t)|
              ≤
                |processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t)| +
                |processToTimeSpaceFun G (ω, t)| := by
                  simpa using
                    (abs_sub_le
                      (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t))
                      0
                      (processToTimeSpaceFun G (ω, t)))
          _ ≤ C + C := add_le_add hK_bound hG_bound
          _ = 2 * C := by ring
      have hsq :
          (processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
              processToTimeSpaceFun G (ω, t)) ^ 2 ≤
            (2 * C) ^ 2 := by
        have hlow :
            -(2 * C) ≤
              processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
                processToTimeSpaceFun G (ω, t) :=
          (abs_le.mp hsub).1
        have hupp :
            processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
                processToTimeSpaceFun G (ω, t) ≤
              2 * C :=
          (abs_le.mp hsub).2
        nlinarith
      have hbound_mem : t ∈ Set.Icc (0 : ℝ) ((T : ℝ) + 1) := ⟨ht0, hstrip⟩
      have hF_nonneg : 0 ≤ F n t := sq_nonneg _
      -- Proof comment: on the active strip, both paths are bounded by the same deterministic
      -- constant, so the squared error is controlled by `(2C)^2`.
      calc
        ‖F n t‖ = F n t := by
          simp [Real.norm_eq_abs, abs_of_nonneg hF_nonneg]
        _ ≤ (2 * C) ^ 2 := by
          simpa [F] using hsq
        _ = bound t := by
          simp [bound, hbound_mem]
    · have ht_gt : (T : ℝ) + 1 < t := lt_of_not_ge hstrip
      have hG_zero : processToTimeSpaceFun G (ω, t) = 0 := by
        have hTt : T < t.toNNReal := by
          rw [Real.toNNReal_of_nonneg ht0]
          linarith
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hG_cutoff (ω := ω) hTt
      have hK_zero : processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) = 0 := by
        have hineq : (T : ℝ) + 1 / (n + 1 : ℝ) ≤ t := by
          have hmesh_le : (1 : ℝ) / (n + 1) ≤ 1 := by
            have hpos : (0 : ℝ) < n + 1 := by positivity
            rw [div_le_iff₀ hpos]
            have hn : (0 : ℝ) ≤ n := by positivity
            have hone : (1 : ℝ) ≤ n + 1 := by linarith
            simpa [one_mul] using hone
          linarith
        have hineq_nn : T + 1 / (n + 1 : NNReal) ≤ t.toNNReal := by
          rw [Real.toNNReal_of_nonneg ht0]
          exact_mod_cast hineq
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using
          movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff hineq_nn ω
      have hbound_zero : bound t = 0 := by
        have hnot_mem : t ∉ Set.Icc (0 : ℝ) ((T : ℝ) + 1) := by
          simp [ht0, hstrip]
        simp [bound, hnot_mem]
      -- Proof comment: beyond the deterministic strip `[0,T+1]`, both the cutoff process and `G`
      -- vanish, so the error and its dominating indicator are identically zero.
      have hzero_diff :
          processToTimeSpaceFun (fun s ω' ↦ movingAverageCutoff G T n s ω' - G s ω') (ω, t) = 0 := by
        calc
          processToTimeSpaceFun (fun s ω' ↦ movingAverageCutoff G T n s ω' - G s ω') (ω, t)
              =
                processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
                  processToTimeSpaceFun G (ω, t) := by
                    simp [processToTimeSpaceFun]
          _ = 0 := by simp [hG_zero, hK_zero]
      have hzero_value :
          movingAverageCutoff G T n t.toNNReal ω - G t.toNNReal ω = 0 := by
        simpa [processToTimeSpaceFun, Real.toNNReal_of_nonneg ht0] using hzero_diff
      have hzero_value' :
          movingAverageCutoff G T n ⟨t, ht0⟩ ω - G ⟨t, ht0⟩ ω = 0 := by
        simpa [Real.toNNReal_of_nonneg ht0] using hzero_value
      have hF_zero : F n t = 0 := by
        dsimp [F]
        rw [hzero_value]
        norm_num
      rw [hF_zero, hbound_zero]
      norm_num
  have hsq_cont : Continuous fun x : ℝ ↦ x ^ 2 := by
    continuity
  have h_lim : ∀ᵐ t ∂ν, Filter.Tendsto (fun n ↦ F n t) Filter.atTop (𝓝 0) := by
    filter_upwards
      [ae_tendsto_processToTimeSpaceFun_movingAverageCutoff T hG_prog hG_bdd' hG_cutoff ω] with
      t ht
    -- Proof comment: the rowwise a.e. convergence of the moving averages to `G` survives
    -- subtraction and squaring.
    have hsub :
        Filter.Tendsto
          (fun n ↦
            processToTimeSpaceFun (movingAverageCutoff G T n) (ω, t) -
              processToTimeSpaceFun G (ω, t))
          Filter.atTop (𝓝 0) := by
      simpa using
        ht.sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℕ ↦ processToTimeSpaceFun G (ω, t))
              Filter.atTop (𝓝 (processToTimeSpaceFun G (ω, t))))
    simpa [F] using hsq_cont.continuousAt.tendsto.comp hsub
  have hInt :
      Filter.Tendsto (fun n ↦ ∫ t, F n t ∂ν) Filter.atTop (𝓝 (∫ t, (0 : ℝ) ∂ν)) := by
    exact tendsto_integral_of_dominated_convergence bound hF_meas hbound_int h_bound h_lim
  -- Proof comment: the row-energy integral is exactly the `ν`-integral of the squared error path,
  -- so dominated convergence on the time variable yields the claimed limit.
  simpa [sqRowEnergy, ν, F] using hInt

/-- Helper for Theorem 25.9: the row energy of the moving-average regularization error is
dominated by four times the original row energy. -/
private theorem sqRowEnergy_movingAverageCutoff_sub_le_four_mul
    (ℱ : ContinuousFiltration) {G : Process} (T : NNReal) (n : ℕ)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0)
    (ω : Ω) :
    sqRowEnergy (fun t ω' ↦ movingAverageCutoff G T n t ω' - G t ω') ω ≤
      4 * sqRowEnergy G ω := by
  have hG_bdd' := hG_bdd
  rcases hG_bdd with ⟨C, hC_nonneg, hC⟩
  let K : Process := movingAverageCutoff G T n
  let E : Process := fun t ω' ↦ K t ω' - G t ω'
  have hK_prog : ProgMeasurable ℱ K := by
    simpa [K] using progMeasurable_movingAverageCutoff T n hG_prog hG_bdd' hG_cutoff
  have hK_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |K t ω'| ≤ C' := by
    simpa [K] using movingAverageCutoff_hasBound T n hG_bdd' hG_cutoff
  have hK_cutoff :
      ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, T + 1 / (n + 1 : NNReal) < t → K t ω' = 0 := by
    intro t ω' ht
    simpa [K] using movingAverageCutoff_eq_zero_of_window_past_cutoff T n hG_cutoff
      (le_of_lt ht) ω'
  have hE_prog : ProgMeasurable ℱ E := by
    simpa [E, K, sub_eq_add_neg] using hK_prog.sub hG_prog
  have hE_bdd : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ω', |E t ω'| ≤ C' := by
    refine ⟨2 * C, by positivity, ?_⟩
    intro t ω'
    -- Proof comment: both the moving-average row and the original row are bounded by `C`, so
    -- the rowwise difference is bounded by `2C`.
    calc
      |E t ω'| = |K t ω' - G t ω'| := by rfl
      _ ≤ |K t ω'| + |G t ω'| := by
        simpa using abs_sub_le (K t ω') 0 (G t ω')
      _ ≤ C + C := add_le_add (by simpa [K] using abs_movingAverageCutoff_le T n hC_nonneg hC hG_cutoff t ω')
        (hC t ω')
      _ = 2 * C := by ring
  have hE_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω' : Ω⦄, T + 1 < t → E t ω' = 0 := by
    intro t ω' ht
    have hKzero : K t ω' = 0 := by
      have hmesh_le : (1 / (n + 1 : NNReal) : NNReal) ≤ 1 := by
        have hden : (1 : NNReal) ≤ n + 1 := by
          exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
        simpa using
          (one_div_le_one_div_of_le (show (0 : NNReal) < 1 by positivity) hden)
      have hshift : T + 1 / (n + 1 : NNReal) ≤ T + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmesh_le T
      exact hK_cutoff (ω' := ω') (lt_of_le_of_lt hshift ht)
    have hGzero : G t ω' = 0 := by
      have hTplus : T < T + 1 := by
        have hpos : (0 : NNReal) < 1 := by positivity
        simpa using (lt_add_of_pos_right T hpos)
      exact hG_cutoff (ω := ω') (lt_of_le_of_lt (le_of_lt hTplus) ht)
    simp [E, hKzero, hGzero]
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hE_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun E (ω, s)) ^ 2) ν := by
    simpa [E, ν] using integrable_sq_realPath_on_Ici_of_bound_cutoff (T + 1) hE_prog hE_bdd hE_cutoff ω
  have hK_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun K (ω, s)) ^ 2) ν := by
    simpa [K, ν] using
      integrable_sq_realPath_on_Ici_of_bound_cutoff (T + 1 / (n + 1 : NNReal))
        hK_prog hK_bdd hK_cutoff ω
  have hG_int :
      Integrable (fun s : ℝ ↦ (processToTimeSpaceFun G (ω, s)) ^ 2) ν := by
    simpa [ν] using integrable_sq_realPath_on_Ici_of_bound_cutoff T hG_prog hG_bdd' hG_cutoff ω
  have hright_int :
      Integrable
        (fun s : ℝ ↦
          2 * (processToTimeSpaceFun K (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun G (ω, s)) ^ 2) ν := by
    exact (hK_int.const_mul (2 : ℝ)).add (hG_int.const_mul (2 : ℝ))
  have hpointwise :
      ∀ᵐ s ∂ν,
        (processToTimeSpaceFun E (ω, s)) ^ 2 ≤
          2 * (processToTimeSpaceFun K (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun G (ω, s)) ^ 2 := by
    filter_upwards with s
    have hsq :
        (processToTimeSpaceFun E (ω, s)) ^ 2 ≤
          2 * (processToTimeSpaceFun K (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun G (ω, s)) ^ 2 := by
      have haux :
          (processToTimeSpaceFun K (ω, s) - processToTimeSpaceFun G (ω, s)) ^ 2 ≤
            2 * (processToTimeSpaceFun K (ω, s)) ^ 2 +
              2 * (processToTimeSpaceFun G (ω, s)) ^ 2 := by
        nlinarith [sq_nonneg
          (processToTimeSpaceFun K (ω, s) + processToTimeSpaceFun G (ω, s))]
      simpa [E, K] using haux
    exact hsq
  -- Proof comment: integrate the elementary inequality `(a - b)^2 ≤ 2 a^2 + 2 b^2` along the
  -- time row and then use the previously proved domination for the moving-average row itself.
  calc
    sqRowEnergy E ω = ∫ s, (processToTimeSpaceFun E (ω, s)) ^ 2 ∂ν := by
      rfl
    _ ≤
        ∫ s,
          2 * (processToTimeSpaceFun K (ω, s)) ^ 2 +
            2 * (processToTimeSpaceFun G (ω, s)) ^ 2 ∂ν := by
          exact integral_mono_ae hE_int hright_int hpointwise
    _ = 2 * sqRowEnergy K ω + 2 * sqRowEnergy G ω := by
          rw [integral_add (hK_int.const_mul (2 : ℝ)) (hG_int.const_mul (2 : ℝ)),
            integral_const_mul, integral_const_mul]
          rfl
    _ ≤ 2 * sqRowEnergy G ω + 2 * sqRowEnergy G ω := by
          gcongr
          simpa [K] using movingAverageCutoff_sqRowEnergy_le T n hG_prog hG_bdd' hG_cutoff ω
    _ = 4 * sqRowEnergy G ω := by ring

/-- Helper for Theorem 25.9: the moving-average rows stay in ambient `L²(processMeasure μ)` and
converge back to the bounded cutoff process. -/
-- TODO: the remaining blocker is the common tail estimate
-- `sqRowEnergy_movingAverageCutoff_le`. The fixed-time coefficient `L²(μ)` bridge is now isolated
-- as `memLp_fixedTime_movingAverageCutoff`; what still blocks closure is the global overlap-count
-- needed to control every moving-average row by the single integrable dominator `sqRowEnergy G`.
private theorem movingAverageCutoff_tendstoL2
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {G : Process} (T : NNReal)
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∃ hK_memLp :
        ∀ n, MemLp (processToTimeSpaceFun (movingAverageCutoff G T n))
          (2 : ℝ≥0∞) (processMeasure μ),
      Filter.Tendsto
        (fun n ↦ (hK_memLp n).toLp
          (processToTimeSpaceFun (movingAverageCutoff G T n)))
        Filter.atTop
        (𝓝 (hG_memLp.toLp (processToTimeSpaceFun G))) := by
  refine ⟨fun n ↦ movingAverageCutoff_memLp_of_rowEnergy_domination
    ℱ μ T n hG_prog hG_memLp hG_bdd hG_cutoff, ?_⟩
  let hK_memLp_local :
      ∀ n, MemLp (processToTimeSpaceFun (movingAverageCutoff G T n))
        (2 : ℝ≥0∞) (processMeasure μ) :=
    fun n ↦ movingAverageCutoff_memLp_of_rowEnergy_domination
      ℱ μ T n hG_prog hG_memLp hG_bdd hG_cutoff
  let error : ℕ → Process := fun n t ω ↦ movingAverageCutoff G T n t ω - G t ω
  have hError_memLp :
      ∀ n, MemLp (processToTimeSpaceFun (error n)) (2 : ℝ≥0∞) (processMeasure μ) := by
    intro n
    -- Proof comment: subtracting the ambient `L²` moving-average row from `G` stays in ambient
    -- `L²(processMeasure μ)`.
    simpa [error, processToTimeSpaceFun] using (hK_memLp_local n).sub hG_memLp
  have hRowEnergy_int :
      Integrable (fun ω ↦ 4 * sqRowEnergy G ω) μ := by
    exact (sqRowEnergy_integrable_of_memLp μ hG_memLp).const_mul (4 : ℝ)
  have hRowEnergy_bound :
      ∀ n, ∀ᵐ ω ∂μ, ‖sqRowEnergy (error n) ω‖ ≤ 4 * sqRowEnergy G ω := by
    intro n
    filter_upwards with ω
    have hnonneg_left : 0 ≤ sqRowEnergy (error n) ω := by
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    have hnonneg_right : 0 ≤ 4 * sqRowEnergy G ω := by
      refine mul_nonneg (by positivity) ?_
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    -- Proof comment: the error row is controlled by the elementary square inequality and the
    -- already proved overlap-count domination on the moving-average row.
    calc
      ‖sqRowEnergy (error n) ω‖ = sqRowEnergy (error n) ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hnonneg_left]
      _ ≤ 4 * sqRowEnergy G ω := by
        simpa [error] using
          sqRowEnergy_movingAverageCutoff_sub_le_four_mul
            ℱ T n hG_prog hG_bdd hG_cutoff ω
  have hRowEnergy_tendsto_zero :
      Filter.Tendsto
        (fun n ↦ ∫ ω, sqRowEnergy (error n) ω ∂μ)
        Filter.atTop (𝓝 0) := by
    have h_meas :
        ∀ n, AEStronglyMeasurable (fun ω ↦ sqRowEnergy (error n) ω) μ := by
      intro n
      exact (sqRowEnergy_integrable_of_memLp μ (hError_memLp n)).aestronglyMeasurable
    have h_lim :
        ∀ᵐ ω ∂μ,
          Filter.Tendsto (fun n ↦ sqRowEnergy (error n) ω) Filter.atTop (𝓝 0) :=
      Filter.Eventually.of_forall fun ω ↦
        movingAverageCutoff_error_sqRowEnergy_tendsto_zero
          ℱ T hG_prog hG_bdd hG_cutoff ω
    -- Proof comment: after rewriting the ambient squared error as the outer integral of row
    -- energies, dominated convergence on `Ω` closes the remaining analytic step.
    simpa using
      (tendsto_integral_of_dominated_convergence
        (fun ω ↦ 4 * sqRowEnergy G ω) h_meas hRowEnergy_int hRowEnergy_bound h_lim)
  have hELpNorm_eq :
      ∀ n,
        eLpNorm
          (fun x ↦
            processToTimeSpaceFun (movingAverageCutoff G T n) x -
              processToTimeSpaceFun G x)
          (2 : ℝ≥0∞) (processMeasure μ) =
          ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error n) ω ∂μ)) := by
    intro n
    have hsq_eq :
        ∫ x,
            (processToTimeSpaceFun (error n) x) ^ 2
          ∂ processMeasure μ =
          ∫ ω, sqRowEnergy (error n) ω ∂μ := by
      simpa [error] using integral_sq_process_eq_integral_sqRowEnergy μ (hError_memLp n)
    calc
      eLpNorm
          (fun x ↦
            processToTimeSpaceFun (movingAverageCutoff G T n) x -
              processToTimeSpaceFun G x)
          (2 : ℝ≥0∞) (processMeasure μ)
          =
          ENNReal.ofReal
            ((∫ x, ‖processToTimeSpaceFun (error n) x‖ ^ ((2 : ℝ≥0∞).toReal)
                ∂ processMeasure μ) ^
              (((2 : ℝ≥0∞).toReal)⁻¹)) := by
                simpa [error, processToTimeSpaceFun] using
                  (MemLp.eLpNorm_eq_integral_rpow_norm
                    (μ := processMeasure μ)
                    (p := (2 : ℝ≥0∞))
                    (hp1 := by norm_num)
                    (hp2 := by norm_num)
                    (hf := hError_memLp n))
      _ =
          ENNReal.ofReal
            ((∫ x, (processToTimeSpaceFun (error n) x) ^ 2 ∂ processMeasure μ) ^
              (((2 : ℝ≥0∞).toReal)⁻¹)) := by
                congr 1
                congr 1
                refine integral_congr_ae ?_
                filter_upwards with x
                norm_num [Real.norm_eq_abs, sq_abs]
      _ = ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error n) ω ∂μ)) := by
            rw [hsq_eq]
            norm_num [Real.sqrt_eq_rpow]
  have hELpNorm :
      Filter.Tendsto
        (fun n ↦
          eLpNorm
            (fun x ↦
              processToTimeSpaceFun (movingAverageCutoff G T n) x -
                processToTimeSpaceFun G x)
            (2 : ℝ≥0∞) (processMeasure μ))
        Filter.atTop (𝓝 0) := by
    have hsqrt :
        Filter.Tendsto
          (fun n ↦ Real.sqrt (∫ ω, sqRowEnergy (error n) ω ∂μ))
          Filter.atTop (𝓝 0) := by
      have hsqrt_cont : Continuous fun x : ℝ ↦ Real.sqrt x := by
        continuity
      simpa using hsqrt_cont.continuousAt.tendsto.comp hRowEnergy_tendsto_zero
    have hofReal :
        Filter.Tendsto
          (fun n ↦ ENNReal.ofReal (Real.sqrt (∫ ω, sqRowEnergy (error n) ω ∂μ)))
          Filter.atTop (𝓝 0) := by
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hELpNorm_eq n).symm) hofReal
    -- Proof comment: the `L²` seminorm is the square root of the squared ambient integral, so the
    -- row-energy convergence translates directly into the ambient `eLpNorm` convergence.
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n x ↦ processToTimeSpaceFun (movingAverageCutoff G T n) x)
    hK_memLp_local (processToTimeSpaceFun G) hG_memLp).2 hELpNorm

/-- Helper for Theorem 25.9: the textbook bounded-cutoff layer should produce predictable-simple
`L²` approximants for any bounded progressively measurable process with compact time support. -/
private theorem exists_tendsto_predictableSimpleProcessL2_of_boundedProgMeasurableCutoff
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {G : Process}
    (hG_prog : ProgMeasurable ℱ G)
    (hG_memLp : MemLp (processToTimeSpaceFun G) (2 : ℝ≥0∞) (processMeasure μ))
    (hG_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |G t ω| ≤ C)
    (hG_cutoff : ∃ T : NNReal, ∀ ⦃t : NNReal⦄ ⦃ω : Ω⦄, T < t → G t ω = 0) :
    ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
      Filter.Tendsto (fun n ↦ (Hs n : Lp ℝ 2 (processMeasure μ))) Filter.atTop
        (𝓝 (hG_memLp.toLp (processToTimeSpaceFun G))) := by
  rcases hG_cutoff with ⟨T, hT⟩
  rcases movingAverageCutoff_tendstoL2 ℱ μ T hG_prog hG_memLp hG_bdd hT with
    ⟨hK_memLp, hK_tendsto⟩
  -- Route correction: the bounded-cutoff theorem is now only the final assembly step. The
  -- moving-average ambient convergence and the fixed-row dyadic approximation live in separate
  -- helpers so the diagonal extraction sees exactly one family of `L²` rows.
  refine exists_tendsto_predictableSimpleProcessL2_of_tendsto_and_each_exists
    ℱ μ hK_memLp hK_tendsto ?_
  intro n
  -- Proof comment: once the `n`-th moving-average row is known to lie in ambient `L²`, the row
  -- theorem supplies its predictable-simple approximants.
  exact exists_tendsto_predictableSimpleProcessL2_of_movingAverageCutoff
    ℱ μ T n hG_prog hG_memLp hG_bdd hT (hK_memLp n)

/-- Helper for Theorem 25.9: the textbook time-height truncations of `H` stay progressively
measurable, remain in ambient `L²(μ ⊗ dt)`, and converge back to `H` in `L²`. -/
-- TODO: replace the current Vitali-style route by the planned dominated-convergence argument on
-- the squared truncation error, then transport that convergence to the ambient `Lp` classes.
private theorem timeHeightTruncation_tendstoL2_of_progMeasurable_memLp
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    ∃ hTrunc_memLp :
        ∀ n, MemLp (processToTimeSpaceFun (timeHeightTruncation H n))
          (2 : ℝ≥0∞) (processMeasure μ),
      (∀ n, ProgMeasurable ℱ (timeHeightTruncation H n)) ∧
        Filter.Tendsto
          (fun n ↦ (hTrunc_memLp n).toLp
            (processToTimeSpaceFun (timeHeightTruncation H n)))
          Filter.atTop
          (𝓝 (hH_memLp.toLp (processToTimeSpaceFun H))) := by
  classical
  let f : ℕ → Ω × ℝ → ℝ := fun n ↦ processToTimeSpaceFun (timeHeightTruncation H n)
  let g : Ω × ℝ → ℝ := processToTimeSpaceFun H
  have hg_ae : AEMeasurable g (processMeasure μ) := hH_memLp.aestronglyMeasurable.aemeasurable
  have hTrunc_memLp :
      ∀ n, MemLp (f n) (2 : ℝ≥0∞) (processMeasure μ) := by
    intro n
    let s : Set (Ω × ℝ) := {x | x.2 ≤ (n : ℝ) ∧ |g x| ≤ (n : ℝ)}
    have hs_time : MeasurableSet {x : Ω × ℝ | x.2 ≤ (n : ℝ)} :=
      measurableSet_le measurable_snd measurable_const
    have hs_height : NullMeasurableSet {x : Ω × ℝ | |g x| ≤ (n : ℝ)} (processMeasure μ) := by
      exact hg_ae.norm.nullMeasurableSet_preimage (measurableSet_Iic : MeasurableSet (Set.Iic (n : ℝ)))
    have hs : NullMeasurableSet s (processMeasure μ) := hs_time.nullMeasurableSet.inter hs_height
    have hIndicator_mem :
        MemLp (Set.indicator (toMeasurable (processMeasure μ) s) g)
          (2 : ℝ≥0∞) (processMeasure μ) :=
      MemLp.indicator (measurableSet_toMeasurable _ _) hH_memLp
    have hIndicator_ae :
        Set.indicator (toMeasurable (processMeasure μ) s) g =ᵐ[processMeasure μ]
          Set.indicator s g :=
      indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq
    have hEq :
        Set.indicator (toMeasurable (processMeasure μ) s) g =ᵐ[processMeasure μ] f n :=
      hIndicator_ae.trans (processToTimeSpaceFun_timeHeightTruncation μ H n).symm
    exact MemLp.ae_eq hEq hIndicator_mem
  refine ⟨hTrunc_memLp, ?_, ?_⟩
  · -- Proof comment: progressive measurability was isolated earlier as a strip-local indicator
    -- argument, so each truncation inherits it directly from the original process.
    intro n
    exact progMeasurable_timeHeightTruncation hH_prog n
  · have hUi :
        MeasureTheory.UnifIntegrable f (2 : ℝ≥0∞) (processMeasure μ) := by
      let gMk : Ω × ℝ → ℝ := hH_memLp.aestronglyMeasurable.mk g
      have hgMk_memLp : MemLp gMk (2 : ℝ≥0∞) (processMeasure μ) :=
        hH_memLp.ae_eq hH_memLp.aestronglyMeasurable.ae_eq_mk
      refine MeasureTheory.unifIntegrable_of (p := (2 : ℝ≥0∞)) (by norm_num)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun n ↦ (hTrunc_memLp n).aestronglyMeasurable) ?_
      intro ε hε
      obtain ⟨M, hM_pos, hM⟩ :=
        hgMk_memLp.eLpNorm_indicator_norm_ge_pos_le
          hH_memLp.aestronglyMeasurable.stronglyMeasurable_mk hε
      refine ⟨⟨M, le_of_lt hM_pos⟩, fun n ↦ ?_⟩
      refine le_trans (eLpNorm_mono_ae ?_) hM
      filter_upwards [hH_memLp.aestronglyMeasurable.ae_eq_mk] with x hx
      have habs : |f n x| ≤ |gMk x| := by
        have habs' : |f n x| ≤ |g x| := by
          simpa [Real.norm_eq_abs] using norm_processToTimeSpaceFun_timeHeightTruncation_le H n x
        have hxabs : |g x| = |gMk x| := by
          simpa [Real.norm_eq_abs] using congrArg abs hx
        exact hxabs ▸ habs'
      rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm,
        Set.indicator_apply, Set.indicator_apply]
      by_cases hfx : (⟨M, le_of_lt hM_pos⟩ : ℝ≥0) ≤ ‖f n x‖₊
      · have hfx' : M ≤ |f n x| := by
          simpa [Real.norm_eq_abs] using hfx
        have hgx' : M ≤ |gMk x| := le_trans hfx' habs
        have hcore : (if (⟨M, le_of_lt hM_pos⟩ : ℝ≥0) ≤ ‖f n x‖₊ then |f n x| else 0) ≤ |gMk x| := by
          rw [if_pos hfx]
          exact habs
        simpa [Set.indicator_apply, hgx'] using hcore
      · by_cases hgx' : M ≤ |gMk x|
        · have hcore :
              (if (⟨M, le_of_lt hM_pos⟩ : ℝ≥0) ≤ ‖f n x‖₊ then |f n x| else 0) ≤ |gMk x| := by
            rw [if_neg hfx]
            exact abs_nonneg (gMk x)
          simpa [Set.indicator_apply, hgx'] using hcore
        · have hcore :
              (if (⟨M, le_of_lt hM_pos⟩ : ℝ≥0) ≤ ‖f n x‖₊ then |f n x| else 0) ≤ 0 := by
            simpa [hfx]
          simpa [Set.indicator_apply, hgx'] using hcore
    have hUt :
        MeasureTheory.UnifTight f (2 : ℝ≥0∞) (processMeasure μ) := by
      intro ε hε
      obtain ⟨s, hs_meas, hs_finite, hs_small⟩ :=
        hH_memLp.exists_eLpNorm_indicator_compl_lt (p := (2 : ℝ≥0∞))
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ε := ε) (by simpa using hε.ne')
      refine ⟨s, hs_finite.ne, fun n ↦ ?_⟩
      refine le_trans (eLpNorm_mono fun x ↦ ?_) hs_small.le
      rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
      by_cases hx : x ∈ sᶜ
      · simpa [Set.indicator_of_mem, hx] using norm_processToTimeSpaceFun_timeHeightTruncation_le H n x
      · simp [Set.indicator_of_notMem, hx]
    have hAeTendsto :
        ∀ᵐ x ∂ processMeasure μ, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (𝓝 (g x)) :=
      Filter.Eventually.of_forall (tendsto_processToTimeSpaceFun_timeHeightTruncation H)
    have hELpNorm :
        Filter.Tendsto (fun n ↦ eLpNorm (f n - g) (2 : ℝ≥0∞) (processMeasure μ))
          Filter.atTop (𝓝 0) :=
      MeasureTheory.tendsto_Lp_of_tendsto_ae (μ := processMeasure μ) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (fun n ↦ (hTrunc_memLp n).aestronglyMeasurable) hH_memLp hUi hUt hAeTendsto
    -- Proof comment: Vitali convergence turns the pointwise convergence of the truncations into
    -- convergence in ambient `L²(processMeasure μ)`, which is exactly the required `Lp` limit.
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hTrunc_memLp g hH_memLp).2 hELpNorm

/-- Helper for Theorem 25.9: a progressively measurable square-integrable process should admit an
ambient `L²(μ ⊗ dt)` approximation sequence by globally square-integrable predictable simple
processes. -/
-- TODO: reassemble the source route `truncation -> bounded cutoff -> diagonal` once the two
-- placeholder analytic frontiers are proved.
private theorem exists_tendsto_predictableSimpleProcessL2_of_progMeasurable_memLp
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    ∃ Hs : ℕ → predictableSimpleProcessL2 ℱ μ,
      Filter.Tendsto (fun n ↦ (Hs n : Lp ℝ 2 (processMeasure μ))) Filter.atTop
        (𝓝 (hH_memLp.toLp (processToTimeSpaceFun H))) := by
  rcases timeHeightTruncation_tendstoL2_of_progMeasurable_memLp ℱ μ hH_prog hH_memLp with
    ⟨hTrunc_memLp, hTrunc_prog, hTrunc_tendsto⟩
  -- Proof comment: once truncations converge to `H` in ambient `L²`, approximate each truncation
  -- by predictable simple processes and diagonalize the two-index family.
  refine exists_tendsto_predictableSimpleProcessL2_of_tendsto_and_each_exists
    ℱ μ hTrunc_memLp hTrunc_tendsto ?_
  intro n
  exact exists_tendsto_predictableSimpleProcessL2_of_boundedProgMeasurableCutoff
    ℱ μ (hTrunc_prog n) (hTrunc_memLp n) (timeHeightTruncation_hasBound H n)
    (timeHeightTruncation_hasCutoff H n)

-- Proof sketch: on each finite horizon, first approximate a bounded progressively measurable
-- process by time-averaged continuous adapted processes, then approximate those by predictable
-- simple step processes; finally truncate a general `L²` progressively measurable process and use
-- the global `MemLp` hypothesis to control the truncation error.
/-- Theorem 25.9, core/canonical form: the `Lp` class of a progressively measurable
square-integrable process belongs to the realized closure
`PredictableSimpleProcessL2Closure ℱ μ = \overline{\mathcal E}`. -/
theorem progMeasurable_toLp_mem_predictableSimpleProcessL2_closure
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    hH_memLp.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ := by
  -- Route correction: keep the main theorem at the closedness level and delegate the full
  -- approximation construction to a single source-facing helper.
  refine mem_closure_of_exists_tendsto_predictableSimpleProcessL2 ℱ μ ?_
  -- Proof comment: the helper below is exactly the missing source frontier, with the closedness
  -- argument already factored out above.
  exact exists_tendsto_predictableSimpleProcessL2_of_progMeasurable_memLp ℱ μ hH_prog hH_memLp

/-- Source-facing bridge form of Theorem 25.9: every progressively measurable real-valued process
with finite `L²(μ ⊗ dt)` norm belongs to the canonical closure predicate
`MemPredictableStepProcessClosure ℱ μ`. -/
theorem progMeasurable_memPredictableStepProcessClosure
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    MemPredictableStepProcessClosure ℱ μ H :=
  ⟨hH_memLp, progMeasurable_toLp_mem_predictableSimpleProcessL2_closure ℱ μ hH_prog hH_memLp⟩

end MeasureTheory
