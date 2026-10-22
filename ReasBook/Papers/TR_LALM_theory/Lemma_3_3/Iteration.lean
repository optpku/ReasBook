/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TR_LALM_theory.Assumption_2_3.Parameters
public import TR_LALM_theory.Lemma_3_3.Estimator

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

namespace LALM

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The LALM quadratic step model with an explicit objective-gradient vector. -/
@[expose] noncomputable def stepModelWithGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪g, p⟫_ℝ + ⟪multiplier, c x + fderiv ℝ c x p⟫_ℝ +
    (ρ / 2) * ‖c x + fderiv ℝ c x p‖ ^ 2 + (β / 2) * ‖p‖ ^ 2

/-- The explicit-gradient step model has the objective-gradient,
linearized-constraint, penalty, and proximal terms. -/
theorem stepModelWithGradient_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    stepModelWithGradient c g ρ β x multiplier p =
      ⟪g, p⟫_ℝ + ⟪multiplier, c x + fderiv ℝ c x p⟫_ℝ +
        (ρ / 2) * ‖c x + fderiv ℝ c x p‖ ^ 2 + (β / 2) * ‖p‖ ^ 2 := rfl

/-- Supplying the deterministic objective gradient recovers the original NR-LALM
step model. -/
theorem stepModel_eq_stepModelWithGradient
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (p : EuclideanSpace ℝ (Fin n)) :
    stepModel f c ρ β x multiplier p =
      stepModelWithGradient c (gradient f x) ρ β x multiplier p := rfl

/-- The part of an algorithmic parameter configuration needed to define a
stochastic NR-LALM run: positive penalty and proximal coefficients. -/
class PositivePenaltyParameters (Param : Type*) where
  /-- The fixed penalty coefficient. -/
  rho : Param → ℝ
  /-- The fixed proximal coefficient. -/
  beta : Param → ℝ
  /-- The penalty coefficient is positive. -/
  rho_pos (params : Param) : 0 < rho params
  /-- The proximal coefficient is positive. -/
  beta_pos (params : Param) : 0 < beta params

namespace PositivePenaltyParameters

/-- An Assumption 2.3 parameter certificate supplies the smaller positive
parameter interface used by the stochastic iteration and Lemma 3.3. -/
instance parametersInstance
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    {h : EqualityConstrained.Regularity f c} :
    PositivePenaltyParameters (Parameters h x₀ multiplier₀) where
  rho params := params.rho
  beta params := params.beta
  rho_pos params := params.spec.1.2.2.1
  beta_pos params := params.spec.1.2.1

end PositivePenaltyParameters

/-- The positive-parameter interface reads the original penalty field from an
Assumption 2.3 parameter certificate. -/
@[simp] theorem positivePenaltyParameters_rho
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    {h : EqualityConstrained.Regularity f c}
    (params : Parameters h x₀ multiplier₀) :
    PositivePenaltyParameters.rho params =
      (params.toAdmissibleParameters.rho : ℝ) := rfl

/-- The positive-parameter interface reads the original proximal field from an
Assumption 2.3 parameter certificate. -/
@[simp] theorem positivePenaltyParameters_beta
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    {h : EqualityConstrained.Regularity f c}
    (params : Parameters h x₀ multiplier₀) :
    PositivePenaltyParameters.beta params =
      (params.toAdmissibleParameters.beta : ℝ) := rfl

/-- A stochastic fixed-penalty NR-LALM run driven by independent SPIDER samples and
the projected recursive gradient estimate. -/
structure StochasticRun
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m))
    {Param : Type*} [PositivePenaltyParameters Param]
    (params : Param) (Q B b : ℕ+) where
  /-- The jointly indexed family of oracle samples. -/
  sample : ℕ → ℕ → Ω → Ξ
  /-- The generated random primal points. -/
  point : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  /-- The generated random multipliers. -/
  multiplier : ℕ → Ω → EuclideanSpace ℝ (Fin m)
  /-- The generated random primal steps. -/
  step : ℕ → Ω → EuclideanSpace ℝ (Fin n)
  /-- Every sample coordinate has the oracle sample law. -/
  hasLaw_sample : ∀ k i, ProbabilityTheory.HasLaw (sample k i) ν P
  /-- All sample coordinates are mutually independent. -/
  independent_sample :
    ProbabilityTheory.iIndepFun (fun ki : ℕ × ℕ ↦ sample ki.1 ki.2) P
  /-- The state fixed before iteration `k` is independent of the fresh batch
  sampled at that iteration. -/
  independent_preBatchState_sample (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω ↦
        (point k ω, point (k - 1) ω, multiplier k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle point sample Q B b (k - 1) ω))
      (fun ω i ↦ sample k i ω) P
  /-- Every recursively generated raw estimate is almost everywhere measurable. -/
  aemeasurable_rawEstimate (k : ℕ) :
    AEMeasurable (SPIDER.rawEstimate oracle point sample Q B b k) P
  /-- Every generated primal point is almost everywhere measurable. -/
  aemeasurable_point (k : ℕ) : AEMeasurable (point k) P
  /-- Every generated multiplier is almost everywhere measurable. -/
  aemeasurable_multiplier (k : ℕ) : AEMeasurable (multiplier k) P
  /-- Every generated primal step is almost everywhere measurable. -/
  aemeasurable_step (k : ℕ) : AEMeasurable (step k) P
  /-- The point sequence starts at the specified initial point on every sample path. -/
  point_zero (ω : Ω) : point 0 ω = x₀
  /-- The multiplier sequence starts at the specified initial multiplier on every sample path. -/
  multiplier_zero (ω : Ω) : multiplier 0 ω = multiplier₀
  /-- Each step minimizes the LALM model driven by the projected SPIDER estimate. -/
  minimizes_step (k : ℕ) (ω : Ω) :
    IsMinOn (stepModelWithGradient c
      (SPIDER.estimate h.gradientBound oracle point sample Q B b k ω)
      (PositivePenaltyParameters.rho params)
      (PositivePenaltyParameters.beta params)
      (point k ω) (multiplier k ω)) Set.univ (step k ω)
  /-- Each sample path updates its primal point by the stored step. -/
  point_succ (k : ℕ) (ω : Ω) : point (k + 1) ω = point k ω + step k ω
  /-- Each sample path uses the classical multiplier update at the new point. -/
  multiplier_succ (k : ℕ) (ω : Ω) :
    multiplier (k + 1) ω = multiplier k ω +
      PositivePenaltyParameters.rho params • c (point (k + 1) ω)

namespace StochasticRun

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {Param : Type*} [PositivePenaltyParameters Param]
variable {params : Param} {Q B b : ℕ+}

/-- Construct a stochastic run from explicit samples, iterate sequences, and
certificates for all sampling and update laws. -/
def ofSequences
    (sample : ℕ → ℕ → Ω → Ξ)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (multiplier : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (step : ℕ → Ω → EuclideanSpace ℝ (Fin n))
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
    (aemeasurable_step : ∀ k, AEMeasurable (step k) P)
    (point_zero : ∀ ω, point 0 ω = x₀)
    (multiplier_zero : ∀ ω, multiplier 0 ω = multiplier₀)
    (minimizes_step : ∀ k ω,
      IsMinOn (stepModelWithGradient c
        (SPIDER.estimate h.gradientBound oracle point sample Q B b k ω)
        (PositivePenaltyParameters.rho params)
        (PositivePenaltyParameters.beta params)
        (point k ω) (multiplier k ω)) Set.univ (step k ω))
    (point_succ : ∀ k ω, point (k + 1) ω = point k ω + step k ω)
    (multiplier_succ : ∀ k ω,
      multiplier (k + 1) ω = multiplier k ω +
        PositivePenaltyParameters.rho params • c (point (k + 1) ω)) :
    StochasticRun h oracle P x₀ multiplier₀ params Q B b :=
  { sample
    point
    multiplier
    step
    hasLaw_sample
    independent_sample
    independent_preBatchState_sample
    aemeasurable_rawEstimate
    aemeasurable_point
    aemeasurable_multiplier
    aemeasurable_step
    point_zero
    multiplier_zero
    minimizes_step
    point_succ
    multiplier_succ }

/-- A stochastic run exposes its sampling/estimator conditions and its unchanged
LALM initialization and update laws in two source-semantic blocks. -/
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
        AEMeasurable (run.step k) P) ∧
    ((∀ ω, run.point 0 ω = x₀ ∧ run.multiplier 0 ω = multiplier₀) ∧
      ∀ k ω,
        IsMinOn (stepModelWithGradient c
          (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
          (PositivePenaltyParameters.rho params)
          (PositivePenaltyParameters.beta params)
          (run.point k ω) (run.multiplier k ω))
            Set.univ (run.step k ω) ∧
        run.point (k + 1) ω = run.point k ω + run.step k ω ∧
        run.multiplier (k + 1) ω =
          run.multiplier k ω + PositivePenaltyParameters.rho params •
            c (run.point (k + 1) ω)) := by
  exact ⟨⟨run.hasLaw_sample, run.independent_sample,
    run.independent_preBatchState_sample,
    fun k ↦ ⟨run.aemeasurable_rawEstimate k, run.aemeasurable_point k,
      run.aemeasurable_multiplier k, run.aemeasurable_step k⟩⟩,
    ⟨fun ω ↦ ⟨run.point_zero ω, run.multiplier_zero ω⟩,
      fun k ω ↦ ⟨run.minimizes_step k ω, run.point_succ k ω,
        run.multiplier_succ k ω⟩⟩⟩

/-- The projected gradient estimator associated with a stochastic run. -/
@[expose] noncomputable def gradientEstimate
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω

/-- The run-facing estimator is the clipped recursive SPIDER estimate. -/
theorem gradientEstimate_apply
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientEstimate k ω =
      SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω := rfl

/-- The projected gradient error associated with a stochastic run. -/
@[expose] noncomputable def gradientError
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  SPIDER.error h.gradientBound oracle run.point run.sample Q B b k ω

/-- The run-facing gradient error is the estimator minus the deterministic gradient. -/
theorem gradientError_apply
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientError k ω =
      run.gradientEstimate k ω - gradient f (run.point k ω) := rfl

/-- The expected squared norm of the projected gradient error at one iteration. -/
@[expose] noncomputable def gradientErrorMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) : ℝ :=
  ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂P

/-- The gradient-error mean square is its defining Bochner integral. -/
theorem gradientErrorMeanSquare_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    run.gradientErrorMeanSquare k = ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂P := rfl

/-- The expected squared norm of the primal step at one iteration. -/
@[expose] noncomputable def stepMeanSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) : ℝ :=
  ∫ ω, ‖run.step k ω‖ ^ 2 ∂P

/-- The step mean square is its defining Bochner integral. -/
theorem stepMeanSquare_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (k : ℕ) :
    run.stepMeanSquare k = ∫ ω, ‖run.step k ω‖ ^ 2 ∂P := rfl

/-- Every primal point used through a stochastic prefix lies in the regularity
region on every sample path. -/
def PointsInRegion
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) : Prop :=
  ∀ k < K, ∀ ω, run.point k ω ∈ h.region

/-- Pointwise region membership through a stochastic prefix is exactly the
corresponding pathwise condition at every index below the horizon. -/
theorem pointsInRegion_iff
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b) (K : ℕ) :
    run.PointsInRegion K ↔ ∀ k < K, ∀ ω, run.point k ω ∈ h.region := Iff.rfl

/-- A stochastic prefix is admissible when every sample-path segment lies in the
regularity region through all completed iterations. -/
def IsAdmissiblePrefix
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ k < K, ∀ ω, segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region

/-- A stochastic prefix is almost surely admissible when all of its completed
segments lie in the regularity region on almost every sample path. -/
def IsAEAdmissiblePrefix
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ᵐ ω ∂P, ∀ k < K,
    segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region

/-- Helper for Lemma 3.3: squared primal steps are integrable through the
specified finite prefix. -/
abbrev HasIntegrableStepSquares
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ k < K, Integrable (fun ω ↦ ‖run.step k ω‖ ^ 2) P

/-- Stochastic prefix admissibility is pathwise segment containment at every
index below the horizon. -/
theorem isAdmissiblePrefix_iff
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.IsAdmissiblePrefix K ↔
      ∀ k < K, ∀ ω, segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region := Iff.rfl

/-- Almost-sure prefix admissibility is simultaneous segment containment up to
the specified horizon on almost every sample path. -/
theorem isAEAdmissiblePrefix_iff
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) :
    run.IsAEAdmissiblePrefix K ↔
      ∀ᵐ ω ∂P, ∀ k < K,
        segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region := Iff.rfl

/-- Pathwise admissibility implies almost-sure admissibility. -/
theorem IsAdmissiblePrefix.isAE
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b} {K : ℕ}
    (h_admissible : run.IsAdmissiblePrefix K) :
    run.IsAEAdmissiblePrefix K := by
  filter_upwards [] with ω
  intro k hk
  exact h_admissible k hk ω

omit [MeasurableSpace Ω] in
/-- Helper for Lemma 3.3: the raw SPIDER estimate commutes with a common
reindexing of all sample-space-dependent inputs. -/
private lemma rawEstimate_comp_right
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (redirect : Ω → Ω) (k : ℕ) (ω : Ω) :
    SPIDER.rawEstimate oracle
        (fun j ω' ↦ point j (redirect ω'))
        (fun j i ω' ↦ sample j i (redirect ω')) Q B b k ω =
      SPIDER.rawEstimate oracle point sample Q B b k (redirect ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [SPIDER.rawEstimate]
      split
      · rfl
      · simp only [ih]

/-- An almost-surely admissible stochastic run has an almost-everywhere equal
version whose prefix is admissible on every sample path. -/
theorem IsAEAdmissiblePrefix.exists_pathwiseVersion
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAEAdmissiblePrefix K) :
    ∃ run' : StochasticRun h oracle P x₀ multiplier₀ params Q B b,
      run'.IsAdmissiblePrefix K ∧
      (∀ k, run'.point k =ᵐ[P] run.point k) ∧
      (∀ k, run'.multiplier k =ᵐ[P] run.multiplier k) ∧
      (∀ k, run'.step k =ᵐ[P] run.step k) ∧
      (∀ k, run'.gradientError k =ᵐ[P] run.gradientError k) := by
  classical
  let Good : Ω → Prop := fun ω ↦ ∀ k < K,
    segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region
  have hGoodAE : ∀ᵐ ω ∂P, Good ω := h_admissible
  obtain ⟨ω₀, hω₀⟩ := hGoodAE.exists
  let redirect : Ω → Ω := fun ω ↦ if Good ω then ω else ω₀
  have hredirectGood (ω : Ω) : Good (redirect ω) := by
    by_cases hω : Good ω
    · simp only [redirect, hω, if_true]
    · simpa only [redirect, hω, if_false] using hω₀
  have hredirectEq : ∀ᵐ ω ∂P, redirect ω = ω := by
    filter_upwards [hGoodAE] with ω hω
    simp only [redirect, hω, if_true]
  let sample' : ℕ → ℕ → Ω → Ξ :=
    fun k i ω ↦ run.sample k i (redirect ω)
  let point' : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω ↦ run.point k (redirect ω)
  let multiplier' : ℕ → Ω → EuclideanSpace ℝ (Fin m) :=
    fun k ω ↦ run.multiplier k (redirect ω)
  let step' : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω ↦ run.step k (redirect ω)
  have hsampleAE (k i : ℕ) : sample' k i =ᵐ[P] run.sample k i := by
    filter_upwards [hredirectEq] with ω hω
    simp only [sample', hω]
  have hpointAE (k : ℕ) : point' k =ᵐ[P] run.point k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [point', hω]
  have hmultiplierAE (k : ℕ) : multiplier' k =ᵐ[P] run.multiplier k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [multiplier', hω]
  have hstepAE (k : ℕ) : step' k =ᵐ[P] run.step k := by
    filter_upwards [hredirectEq] with ω hω
    simp only [step', hω]
  have hraw (k : ℕ) (ω : Ω) :
      SPIDER.rawEstimate oracle point' sample' Q B b k ω =
        SPIDER.rawEstimate oracle run.point run.sample Q B b k (redirect ω) := by
    exact rawEstimate_comp_right run.point run.sample redirect k ω
  have hrawAE (k : ℕ) :
      SPIDER.rawEstimate oracle point' sample' Q B b k =ᵐ[P]
        SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
    filter_upwards [hredirectEq] with ω hω
    rw [hraw, hω]
  have hstateAE (k : ℕ) :
      (fun ω ↦
        (run.point k ω, run.point (k - 1) ω, run.multiplier k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) ω))
        =ᵐ[P]
      (fun ω ↦
        (point' k ω, point' (k - 1) ω, multiplier' k ω,
          if k = 0 then 0 else
            SPIDER.rawEstimate oracle point' sample' Q B b (k - 1) ω)) := by
    filter_upwards [hredirectEq] with ω hω
    simp only [point', multiplier', hω]
    split
    · rfl
    · rw [hraw, hω]
  have hbatchAE (k : ℕ) :
      (fun ω i ↦ run.sample k i ω) =ᵐ[P]
        (fun ω i ↦ sample' k i ω) := by
    filter_upwards [hredirectEq] with ω hω
    funext i
    simp only [sample', hω]
  have hminimizes (k : ℕ) (ω : Ω) :
      IsMinOn (stepModelWithGradient c
        (SPIDER.estimate h.gradientBound oracle point' sample' Q B b k ω)
        (PositivePenaltyParameters.rho params)
        (PositivePenaltyParameters.beta params)
        (point' k ω) (multiplier' k ω))
          Set.univ (step' k ω) := by
    simpa only [point', multiplier', step', SPIDER.estimate_apply, hraw] using
      run.minimizes_step k (redirect ω)
  let run' : StochasticRun h oracle P x₀ multiplier₀ params Q B b :=
    { sample := sample'
      point := point'
      multiplier := multiplier'
      step := step'
      hasLaw_sample := fun k i ↦
        (run.hasLaw_sample k i).congr (hsampleAE k i)
      independent_sample := ProbabilityTheory.iIndepFun.congr
        (fun ki ↦ (hsampleAE ki.1 ki.2).symm) run.independent_sample
      independent_preBatchState_sample := fun k ↦
        (run.independent_preBatchState_sample k).congr (hstateAE k) (hbatchAE k)
      aemeasurable_rawEstimate := fun k ↦
        (run.aemeasurable_rawEstimate k).congr (hrawAE k).symm
      aemeasurable_point := fun k ↦
        (run.aemeasurable_point k).congr (hpointAE k).symm
      aemeasurable_multiplier := fun k ↦
        (run.aemeasurable_multiplier k).congr (hmultiplierAE k).symm
      aemeasurable_step := fun k ↦
        (run.aemeasurable_step k).congr (hstepAE k).symm
      point_zero := fun ω ↦ run.point_zero (redirect ω)
      multiplier_zero := fun ω ↦ run.multiplier_zero (redirect ω)
      minimizes_step := hminimizes
      point_succ := fun k ω ↦ run.point_succ k (redirect ω)
      multiplier_succ := fun k ω ↦ run.multiplier_succ k (redirect ω) }
  have hgradientErrorAE (k : ℕ) :
      run'.gradientError k =ᵐ[P] run.gradientError k := by
    filter_upwards [hredirectEq] with ω hω
    rw [run'.gradientError_apply, run.gradientError_apply,
      run'.gradientEstimate_apply, run.gradientEstimate_apply]
    change SPIDER.clip h.gradientBound
        (SPIDER.rawEstimate oracle point' sample' Q B b k ω) -
          gradient f (point' k ω) =
      SPIDER.clip h.gradientBound
        (SPIDER.rawEstimate oracle run.point run.sample Q B b k ω) -
          gradient f (run.point k ω)
    rw [hraw, hω]
    simp only [point', hω]
  refine ⟨run', ?_, ?_, ?_, ?_, hgradientErrorAE⟩
  · intro k hk ω
    exact hredirectGood ω k hk
  · intro k
    exact hpointAE k
  · intro k
    exact hmultiplierAE k
  · intro k
    exact hstepAE k

/-- Segment admissibility implies the pointwise region condition needed by the
SPIDER estimator. -/
theorem IsAdmissiblePrefix.pointsInRegion
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b} {K : ℕ}
    (h_admissible : run.IsAdmissiblePrefix K) : run.PointsInRegion K := by
  intro k hk ω
  exact h_admissible k hk ω (left_mem_segment ℝ _ _)

end StochasticRun

end LALM

end
