/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.HittingTime
public import TR_LALM_theory.Corollary_4_2.Region
public import TR_LALM_theory.Corollary_4_2.Run
public import TR_LALM_theory.Theorem_3_6.Schedule
public import TR_LALM_theory.Theorem_3_6.UniformOutput

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The corrected stochastic Lyapunov error coefficient. -/
noncomputable def lyapunovErrorConstant (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  2 / params.beta + LALM.multiplierErrorConstant h / params.rho

/-- The corrected stochastic Lyapunov error coefficient has the source formula. -/
theorem lyapunovErrorConstant_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    lyapunovErrorConstant h params =
      2 / params.beta + LALM.multiplierErrorConstant h / params.rho := by
  -- Expose the two terms in the corrected Lyapunov error coefficient.
  rfl

/-- The corrected initial stochastic step allowance. -/
noncomputable def initialStepBound (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  params.delta ^ 2 +
    4 * (initialPotentialBound h params - lyapunovLowerBound h params) / params.beta

/-- The corrected initial stochastic step allowance has the source formula. -/
theorem initialStepBound_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    initialStepBound h params = params.delta ^ 2 +
      4 * (initialPotentialBound h params - lyapunovLowerBound h params) /
        params.beta := by
  -- Expose the initial step allowance from its proof-free definition.
  rfl

/-- The corrected coefficient transferring stochastic gradient error to step size. -/
noncomputable def errorStepConstant (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  8 * lyapunovErrorConstant h params / params.beta

/-- The corrected error-step coefficient is the corrected `D₁`. -/
theorem errorStepConstant_def (h : EqualityConstrained.Regularity f c)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    errorStepConstant h params = 8 * lyapunovErrorConstant h params / params.beta := by
  -- Expose the corrected error-to-step coefficient.
  rfl

/-- The corrected average stochastic-gradient error constant. -/
noncomputable def errorAverageConstant (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  2 * oracle.noiseLevel ^ 2 + initialStepBound h params / errorStepConstant h params

/-- The corrected average error constant has its source formula. -/
theorem errorAverageConstant_def (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    errorAverageConstant h oracle params = 2 * oracle.noiseLevel ^ 2 +
      initialStepBound h params / errorStepConstant h params := by
  -- Expose the corrected average gradient-error allowance.
  rfl

/-- The corrected average base-step constant. -/
noncomputable def stepAverageConstant (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  2 * errorStepConstant h params * oracle.noiseLevel ^ 2 +
    2 * initialStepBound h params

/-- The corrected average base-step constant has its source formula. -/
theorem stepAverageConstant_def (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    stepAverageConstant h oracle params =
      2 * errorStepConstant h params * oracle.noiseLevel ^ 2 +
        2 * initialStepBound h params := by
  -- Expose the corrected average base-step allowance.
  rfl

/-- The corrected stochastic KKT-residual comparison constant. -/
noncomputable def stochasticResidualConstant
    (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  max
    (2 * primalComparisonConstant h delta beta rho multiplierBound ^ 2 +
      multiplierPrimalConstant h delta beta rho multiplierBound / rho ^ 2)
    (2 + LALM.multiplierErrorConstant h / rho ^ 2)

/-- The corrected stochastic residual constant has its explicit maximum formula. -/
theorem stochasticResidualConstant_def
    (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    stochasticResidualConstant h delta beta rho multiplierBound =
      max
        (2 * primalComparisonConstant h delta beta rho multiplierBound ^ 2 +
          multiplierPrimalConstant h delta beta rho multiplierBound / rho ^ 2)
        (2 + LALM.multiplierErrorConstant h / rho ^ 2) := by
  -- Expose the two residual-comparison branches in the defining maximum.
  rfl

/-- The corrected direct stochastic residual-complexity constant. -/
noncomputable def stochasticComplexityConstant
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) : ℝ :=
  2 * stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound *
    (stepAverageConstant h oracle params + errorAverageConstant h oracle params)

/-- The corrected stochastic complexity constant has its explicit source formula. -/
theorem stochasticComplexityConstant_def
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    stochasticComplexityConstant h oracle params =
      2 * stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (stepAverageConstant h oracle params + errorAverageConstant h oracle params) := by
  -- Expose the corrected residual and moment factors in the complexity constant.
  rfl

/-- A stochastic NR-LALM+SOC run driven by independent SPIDER samples. -/
structure StochasticRun
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+) where
  /-- The jointly indexed oracle samples. -/
  sample : ℕ → ℕ → Ω → Ξ
  /-- The corrected random primal points. -/
  point : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  /-- The random classical multipliers. -/
  multiplier : ℕ → Ω → EuclideanSpace ℝ (Fin m)
  /-- The random base-model steps. -/
  baseStep : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  /-- Each sample coordinate has the oracle law. -/
  hasLaw_sample : ∀ k i, ProbabilityTheory.HasLaw (sample k i) ν P
  /-- All sample coordinates are mutually independent. -/
  independent_sample :
    ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ sample ki.1 ki.2) P
  /-- The state fixed before iteration `k` is independent of its fresh sample batch. -/
  independent_preBatchState_sample (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω ↦
        (point k ω, point (k - 1) ω, multiplier k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle point sample Q B b (k - 1) ω))
      (fun ω i ↦ sample k i ω) P
  /-- Each recursive raw estimate is almost everywhere measurable. -/
  aemeasurable_rawEstimate (k : ℕ) :
    AEMeasurable (SPIDER.rawEstimate oracle point sample Q B b k) P
  /-- Each corrected point is almost everywhere measurable. -/
  aemeasurable_point (k : ℕ) : AEMeasurable (point k) P
  /-- Each multiplier is almost everywhere measurable. -/
  aemeasurable_multiplier (k : ℕ) : AEMeasurable (multiplier k) P
  /-- Each base step is almost everywhere measurable. -/
  aemeasurable_baseStep (k : ℕ) : AEMeasurable (baseStep k) P
  /-- The point sequence has the prescribed initialization. -/
  point_zero (ω : Ω) : point 0 ω = x₀
  /-- The multiplier sequence has the prescribed initialization. -/
  multiplier_zero (ω : Ω) : multiplier 0 ω = multiplier₀
  /-- Every base step minimizes the stochastic-gradient model. -/
  minimizes_baseStep (k : ℕ) (ω : Ω) :
    IsMinOn (LALM.stepModelWithGradient c
      (SPIDER.estimate h.gradientBound oracle point sample Q B b k ω)
      params.rho params.beta (point k ω) (multiplier k ω)) Set.univ (baseStep k ω)
  /-- Every sample path applies the corrected primal update. -/
  point_succ (k : ℕ) (ω : Ω) :
    point (k + 1) ω = nextPoint c (point k ω) (baseStep k ω)
  /-- Every sample path applies the classical multiplier update at the corrected point. -/
  multiplier_succ (k : ℕ) (ω : Ω) :
    multiplier (k + 1) ω =
      nextMultiplier c params.rho (point k ω) (multiplier k ω) (baseStep k ω)

namespace StochasticRun

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀} {Q B b : ℕ+}

/-- Construct a corrected stochastic run from explicit samples, sequences, and laws. -/
def ofSequences
    (sample : ℕ → ℕ → Ω → Ξ)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (baseStep : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hasLaw_sample : ∀ k i, ProbabilityTheory.HasLaw (sample k i) ν P)
    (independent_sample :
      ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ sample ki.1 ki.2) P)
    (independent_preBatchState_sample : ∀ k,
      ProbabilityTheory.IndepFun
        (fun ω ↦
          (point k ω, point (k - 1) ω, multiplier k ω,
            if k = 0 then 0 else
              SPIDER.rawEstimate oracle point sample Q B b (k - 1) ω))
        (fun ω i ↦ sample k i ω) P)
    (aemeasurable_rawEstimate : ∀ k,
      AEMeasurable (SPIDER.rawEstimate oracle point sample Q B b k) P)
    (aemeasurable_point : ∀ k, AEMeasurable (point k) P)
    (aemeasurable_multiplier : ∀ k, AEMeasurable (multiplier k) P)
    (aemeasurable_baseStep : ∀ k, AEMeasurable (baseStep k) P)
    (point_zero : ∀ ω, point 0 ω = x₀)
    (multiplier_zero : ∀ ω, multiplier 0 ω = multiplier₀)
    (minimizes_baseStep : ∀ k ω,
      IsMinOn (LALM.stepModelWithGradient c
        (SPIDER.estimate h.gradientBound oracle point sample Q B b k ω)
        params.rho params.beta (point k ω) (multiplier k ω)) Set.univ (baseStep k ω))
    (point_succ : ∀ k ω,
      point (k + 1) ω = nextPoint c (point k ω) (baseStep k ω))
    (multiplier_succ : ∀ k ω,
      multiplier (k + 1) ω =
        nextMultiplier c params.rho (point k ω) (multiplier k ω) (baseStep k ω)) :
    StochasticRun h oracle P x₀ multiplier₀ params Q B b :=
  { sample
    point
    multiplier
    baseStep
    hasLaw_sample
    independent_sample
    independent_preBatchState_sample
    aemeasurable_rawEstimate
    aemeasurable_point
    aemeasurable_multiplier
    aemeasurable_baseStep
    point_zero
    multiplier_zero
    minimizes_baseStep
    point_succ
    multiplier_succ }

/-- A corrected stochastic run exposes its sampling and corrected-update semantics. -/
theorem spec (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) :
    ((∀ k i, ProbabilityTheory.HasLaw (run.sample k i) ν P) ∧
      ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ run.sample ki.1 ki.2) P ∧
      (∀ k, ProbabilityTheory.IndepFun
        (fun ω ↦
          (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
            if k = 0 then 0 else
              SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
        (fun ω i ↦ run.sample k i ω) P) ∧
      ∀ k, AEMeasurable
        (SPIDER.rawEstimate oracle run.point run.sample Q B b k) P ∧
        AEMeasurable (run.point k) P ∧ AEMeasurable (run.multiplier k) P ∧
        AEMeasurable (run.baseStep k) P) ∧
    ((∀ ω, run.point 0 ω = x₀ ∧ run.multiplier 0 ω = multiplier₀) ∧
      ∀ k ω,
        IsMinOn (LALM.stepModelWithGradient c
          (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
          params.rho params.beta (run.point k ω) (run.multiplier k ω))
            Set.univ (run.baseStep k ω) ∧
        run.point (k + 1) ω =
          nextPoint c (run.point k ω) (run.baseStep k ω) ∧
        run.multiplier (k + 1) ω = nextMultiplier c params.rho
          (run.point k ω) (run.multiplier k ω) (run.baseStep k ω)) := by
  -- Collect the owner projections into the two public semantic blocks.
  exact ⟨⟨run.hasLaw_sample, run.independent_sample,
    run.independent_preBatchState_sample,
    fun k ↦ ⟨run.aemeasurable_rawEstimate k, run.aemeasurable_point k,
      run.aemeasurable_multiplier k, run.aemeasurable_baseStep k⟩⟩,
    ⟨fun ω ↦ ⟨run.point_zero ω, run.multiplier_zero ω⟩,
      fun k ω ↦ ⟨run.minimizes_baseStep k ω, run.point_succ k ω,
        run.multiplier_succ k ω⟩⟩⟩

/-- The explicit correction used by a corrected stochastic run. -/
noncomputable def correction
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  step c (run.point k ω) (run.baseStep k ω)

/-- A stochastic run-facing correction is the correction of its base step. -/
theorem correction_apply
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.correction k ω = step c (run.point k ω) (run.baseStep k ω) := by
  -- Unfold the run-facing correction at the requested sample path.
  rfl

/-- A corrected stochastic prefix is almost surely admissible when both segments
of every corrected transition lie in the regularity region. -/
def IsAEAdmissiblePrefix
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ᵐ ω ∂P, ∀ k < K,
    IsAdmissible h (run.point k ω) (run.baseStep k ω)

/-- Almost-sure corrected admissibility is simultaneous containment of the
base-to-trial and trial-to-corrected segments. -/
theorem isAEAdmissiblePrefix_iff
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.IsAEAdmissiblePrefix K ↔ ∀ᵐ ω ∂P, ∀ k < K,
      segment ℝ (run.point k ω) (trialPoint (run.point k ω) (run.baseStep k ω)) ⊆
          h.region ∧
        segment ℝ (trialPoint (run.point k ω) (run.baseStep k ω))
          (nextPoint c (run.point k ω) (run.baseStep k ω)) ⊆ h.region := by
  -- Rewrite each pathwise admissibility assertion to its two segment conditions.
  simp only [IsAEAdmissiblePrefix, isAdmissible_iff]

namespace UniformOutput

/-- The corrected primal point selected at the successor of the uniform index. -/
def point (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) :
    ℕ × Ω → EuclideanSpace ℝ (Fin n) :=
  fun output ↦ run.point (output.1 + 1) output.2

/-- The corrected multiplier selected at the successor of the uniform index. -/
def multiplier (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) :
    ℕ × Ω → EuclideanSpace ℝ (Fin m) :=
  fun output ↦ run.multiplier (output.1 + 1) output.2

/-- The corrected uniform-output point has its defining evaluation formula. -/
theorem point_apply (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (output : ℕ × Ω) :
    point run output = run.point (output.1 + 1) output.2 := by
  -- Evaluate the selected-point map at the given index and sample.
  rfl

/-- The corrected uniform-output multiplier has its defining evaluation formula. -/
theorem multiplier_apply
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (output : ℕ × Ω) :
    multiplier run output = run.multiplier (output.1 + 1) output.2 := by
  -- Evaluate the selected-multiplier map at the given index and sample.
  rfl

end UniformOutput

namespace Localization

/-- The corrected confidence-dependent stochastic objective threshold. -/
noncomputable def objectiveBound (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) : ℝ :=
  deterministicObjectiveBound h params +
    2 * lyapunovErrorConstant h params * errorAverageConstant h oracle params /
      confidence

/-- The corrected stochastic objective threshold has its explicit formula. -/
theorem objectiveBound_def (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) :
    objectiveBound h oracle params confidence = deterministicObjectiveBound h params +
      2 * lyapunovErrorConstant h params * errorAverageConstant h oracle params /
        confidence := by
  -- Expose the deterministic threshold and stochastic confidence correction.
  rfl

/-- The corrected confidence-dependent stochastic objective--feasibility
localization set. -/
def sublevel (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ objectiveBound h oracle params confidence ∧
    ‖c x‖ ≤ 2 * params.multiplierBound / params.rho}

/-- Membership in the corrected stochastic localization set is the conjunction
of its objective and feasibility inequalities. -/
theorem mem_sublevel (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ sublevel h oracle params confidence ↔
      f x ≤ objectiveBound h oracle params confidence ∧
        ‖c x‖ ≤ 2 * params.multiplierBound / params.rho := by
  rfl

/-- The two geometric conditions on a corrected stochastic localization set. -/
def RegionCondition (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  sublevel h oracle params confidence ⊆ X ∧
    Metric.cthickening (localizationRadius h params) X ⊆ h.region

/-- The corrected stochastic region condition is objective--feasibility
localization-set containment together with containment of the closed corrected
localization neighborhood. -/
theorem regionCondition_iff (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    RegionCondition h oracle params confidence X ↔
      sublevel h oracle params confidence ⊆ X ∧
        Metric.cthickening (localizationRadius h params) X ⊆ h.region := Iff.rfl

/-- Construct the corrected stochastic region condition from its two geometric clauses. -/
theorem RegionCondition.of
    {confidence : ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_sublevel : sublevel h oracle params confidence ⊆ X)
    (h_thickening : Metric.cthickening (localizationRadius h params) X ⊆ h.region) :
    RegionCondition h oracle params confidence X :=
  ⟨h_sublevel, h_thickening⟩

/-- A corrected stochastic localization region contains its objective--feasibility
localization set. -/
theorem RegionCondition.sublevel_subset
    {confidence : ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_region : RegionCondition h oracle params confidence X) :
    sublevel h oracle params confidence ⊆ X := h_region.1

/-- The corrected localization neighborhood lies in the regularity region. -/
theorem RegionCondition.thickening_subset
    {confidence : ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (h_region : RegionCondition h oracle params confidence X) :
    Metric.cthickening (localizationRadius h params) X ⊆ h.region := h_region.2

/-- The first time at or after iteration `1` when a corrected stochastic run
leaves a localization set. -/
noncomputable def exitTime
    {P : Measure Ω} [IsProbabilityMeasure P]
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) : Ω → ℕ∞ :=
  MeasureTheory.hittingAfter run.point Xᶜ 1

/-- The corrected localization exit time is the hitting time of the complement. -/
theorem exitTime_def
    {P : Measure Ω} [IsProbabilityMeasure P]
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    exitTime run X = MeasureTheory.hittingAfter run.point Xᶜ 1 := by
  rfl

/-- Exiting by `K` means that a corrected iterate leaves the localization set
at an index from `1` through `K`. -/
theorem exitTime_le_iff
    {P : Measure Ω} [IsProbabilityMeasure P]
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω) (K : ℕ) :
    exitTime run X ω ≤ K ↔
      ∃ j ∈ Set.Icc 1 K, run.point j ω ∉ X := by
  -- Apply the canonical finite-horizon characterization of a hitting time.
  rw [exitTime_def]
  constructor
  · intro h_exit
    obtain ⟨j, hj, hpoint⟩ :=
      (MeasureTheory.hittingAfter_le_iff
        (u := run.point) (s := Xᶜ) (n := 1) (i := K) (ω := ω)).mp h_exit
    exact ⟨j, hj, hpoint⟩
  · rintro ⟨j, hj, hpoint⟩
    exact (MeasureTheory.hittingAfter_le_iff
      (u := run.point) (s := Xᶜ) (n := 1) (i := K) (ω := ω)).mpr
        ⟨j, hj, hpoint⟩

end Localization

end StochasticRun

end LALM.Correction

namespace SPIDER.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- The corrected SPIDER inner batch size, with `Lₛ²` replaced by
`Lₛ² * (χᶜᵒʳ)²`. -/
noncomputable def innerBatchSize
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Correction.Parameters h x₀ multiplier₀) (K : ℕ) : ℕ+ :=
  (max 1 (Nat.ceil
    (2 * LALM.Correction.errorStepConstant h params *
      oracle.meanSquareLipschitz ^ 2 *
      LALM.Correction.displacementFactor h params.delta ^ 2 *
      SPIDER.refreshPeriod K))).toPNat'

/-- The corrected inner batch size exposes the exact displacement-factor scaling. -/
theorem innerBatchSize_coe
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Correction.Parameters h x₀ multiplier₀) (K : ℕ) :
    (innerBatchSize h oracle params K : ℕ) =
      max 1 (Nat.ceil
        (2 * LALM.Correction.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 *
          LALM.Correction.displacementFactor h params.delta ^ 2 *
          SPIDER.refreshPeriod K)) := by
  -- The defining maximum is positive, so `toPNat'` preserves it on coercion.
  have hmaxPos :
      0 < max 1 (Nat.ceil
        (2 * LALM.Correction.errorStepConstant h params *
          oracle.meanSquareLipschitz ^ 2 *
          LALM.Correction.displacementFactor h params.delta ^ 2 *
          SPIDER.refreshPeriod K)) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  rw [innerBatchSize, Nat.toPNat'_coe, if_pos hmaxPos]

/-- A stochastic NR-LALM+SOC run using the prescribed horizon-dependent
SPIDER refresh period and batch sizes. -/
abbrev ScheduledRun
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : LALM.Correction.Parameters h x₀ multiplier₀) (K : ℕ) :=
  LALM.Correction.StochasticRun h oracle P x₀ multiplier₀ params
    (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K) (innerBatchSize h oracle params K)

end SPIDER.Correction

end

open LALM.Correction.StochasticRun
