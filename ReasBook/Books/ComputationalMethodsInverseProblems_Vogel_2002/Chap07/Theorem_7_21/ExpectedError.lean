/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_11.WeightedSeries
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

public section

noncomputable section

namespace TikhonovEstimation

universe u v w

section Objective

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A reconstruction family `R n α` is the Chapter 7 Tikhonov reconstruction
family for `K n` when every candidate parameter `α` has the corresponding
Tikhonov filter-series representation relative to the singular system `S n`. -/
abbrev IsTikhonovReconstructionFamily
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (R : ℕ → ℝ → F →L[ℝ] H) : Prop :=
  ∀ n α, (S n).HasTikhonovFilterRepresentation α (R n α)

@[simp] theorem isTikhonovReconstructionFamily_iff
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (R : ℕ → ℝ → F →L[ℝ] H) :
    IsTikhonovReconstructionFamily K S R ↔
      ∀ n α, (S n).HasTikhonovFilterRepresentation α (R n α) :=
  Iff.rfl

/-- The admissible Tikhonov parameter set from Theorem 7.21 is the nonnegative
half-line `α ≥ 0`, constant in `n`. -/
@[expose] def admissibleParameters : ℕ → Set ℝ :=
  fun _ ↦ Set.Ici 0

@[simp] theorem mem_admissibleParameters (n : ℕ) (α : ℝ) :
    α ∈ admissibleParameters n ↔ 0 ≤ α :=
  Iff.rfl

/-- The `n`-indexed Tikhonov expected squared estimation-error objective from
Theorem 7.21, evaluated at the candidate parameter `α`. -/
@[expose] def expectedObjective
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℝ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) : ℕ → ℝ → ℝ :=
  fun n α ↦ FilterRegularization.expectedSqEstimationError μ (R n α) (K n) fTrue (η n)

omit [CompleteSpace H] [CompleteSpace F] in
@[simp] theorem expectedObjective_apply
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℝ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) (n : ℕ) (α : ℝ) :
    expectedObjective μ K R fTrue η n α =
      FilterRegularization.expectedSqEstimationError μ (R n α) (K n) fTrue (η n) :=
  rfl

/-- Evaluate an `n`-indexed scalar objective family along a parameter family
`α`. -/
@[expose] def objectiveAlong
    (objective : ℕ → ℝ → ℝ) (α : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ objective n (α n)

@[simp] theorem objectiveAlong_apply
    (objective : ℕ → ℝ → ℝ) (α : ℕ → ℝ) (n : ℕ) :
    objectiveAlong objective α n = objective n (α n) :=
  rfl

end Objective

section SourceTerms

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The source-condition coefficient series encoding the squared
`‖f_true‖_{K* K}` term from Theorem 7.21. -/
@[expose] def adjointCompSourceSeries
    {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) : ℕ+ → ℝ :=
  fun i ↦
    S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 /
      (S.singularValueSequence h_length i ^ 4)

@[simp] theorem adjointCompSourceSeries_apply
    {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) (i : ℕ+) :
    adjointCompSourceSeries S h_length fTrue i =
      S.generalizedFourierCoefficientSequence h_length fTrue i ^ 2 /
        (S.singularValueSequence h_length i ^ 4) :=
  rfl

/-- The squared `‖f_true‖_{K* K}` source term from Theorem 7.21, encoded as the
sum of the `K* K`-weighted generalized Fourier coefficients. -/
@[expose] def adjointCompSourceNormSq
    {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) : ℝ :=
  tsum (adjointCompSourceSeries S h_length fTrue)

@[simp] theorem adjointCompSourceNormSq_def
    {K : H →L[ℝ] F}
    (S : ContinuousLinearMap.SingularSystem K)
    (h_length : S.length = ⊤) (fTrue : H) :
    adjointCompSourceNormSq S h_length fTrue =
      tsum (adjointCompSourceSeries S h_length fTrue) :=
  rfl

/-- The squared nullspace floor `‖f_{Null(K_n)}‖_ℋ^2` from equation `(7.81)`. -/
@[expose] def nullspaceErrorFloor
    (K : ℕ → H →L[ℝ] F) (fTrue : H) : ℕ → ℝ :=
  fun n ↦ ‖FilterRegularization.nullspaceComponent (K n) fTrue‖ ^ 2

omit [CompleteSpace F] in
@[simp] theorem nullspaceErrorFloor_apply
    (K : ℕ → H →L[ℝ] F) (fTrue : H) (n : ℕ) :
    nullspaceErrorFloor K fTrue n =
      ‖FilterRegularization.nullspaceComponent (K n) fTrue‖ ^ 2 :=
  rfl

end SourceTerms

section Benchmarks

/-- The explicit nonsaturated constant `C₁` from equation `(7.80)`. -/
@[expose] def parameterConstantC1 (b c p q : ℝ) : ℝ :=
  ((c ^ (q / p) * KernelMoment.integral p 3 (2 * p)) /
      (b * KernelMoment.integral p 3 (2 * p - q))) ^ (p / (p + q))

/-- The defining formula for `parameterConstantC1`. -/
theorem parameterConstantC1_def (b c p q : ℝ) :
    parameterConstantC1 b c p q =
      ((c ^ (q / p) * KernelMoment.integral p 3 (2 * p)) /
          (b * KernelMoment.integral p 3 (2 * p - q))) ^ (p / (p + q)) :=
  rfl

/-- The explicit saturated constant `C₂` from equation `(7.80)`. The scalar
`kStarKNormSq` represents the source term `‖f_true‖_{K* K}^2`. -/
@[expose] def parameterConstantC2 (c p kStarKNormSq : ℝ) : ℝ :=
  ((c ^ (1 / p) * KernelMoment.integral p 3 (2 * p)) / kStarKNormSq) ^
    (p / (3 * p + 1))

/-- The defining formula for `parameterConstantC2`. -/
theorem parameterConstantC2_def (c p kStarKNormSq : ℝ) :
    parameterConstantC2 c p kStarKNormSq =
      ((c ^ (1 / p) * KernelMoment.integral p 3 (2 * p)) / kStarKNormSq) ^
        (p / (3 * p + 1)) :=
  rfl

/-- The right-hand side of the critical root equation defining `β_e`. -/
@[expose] def criticalRootRhs (b c p σ : ℝ) (n : ℕ) : ℝ :=
  ((σ ^ 2) / (n : ℝ)) * b ^ ((-1 : ℝ)) * c ^ 2 * p * KernelMoment.integral p 3 (2 * p)

/-- The explicit nonsaturated constant `C₃` from equation `(7.81)`. -/
@[expose] def errorConstantC3 (b c p q : ℝ) : ℝ :=
  b * c ^ (-(q - 1) / p) * KernelMoment.integral p 2 (2 * p - q)

/-- The explicit critical constant `C₄` from equation `(7.81)`. -/
@[expose] def errorConstantC4 (c p : ℝ) : ℝ :=
  c ^ (1 / p) * KernelMoment.integral p 2 p

/-- The explicit saturated constant `C₅` from equation `(7.81)`. -/
@[expose] def errorConstantC5 : ℝ :=
  1

/-- The displayed critical root equation for the benchmark sequence `β_e`. -/
@[expose] def SatisfiesCriticalRootEquation (b c p σ : ℝ) (n : ℕ) (β : ℝ) : Prop :=
  -(β ^ ((3 * p + 1) / p)) * Real.log β = criticalRootRhs b c p σ n

/-- A benchmark sequence `β_e` satisfies the source root equation from
Theorem 7.21 at every index `n`. -/
@[expose] def IsCriticalBenchmark (b c p σ : ℝ) (βe : ℕ → ℝ) : Prop :=
  ∀ n, SatisfiesCriticalRootEquation b c p σ n (βe n)

@[simp] theorem isCriticalBenchmark_iff
    (b c p σ : ℝ) (βe : ℕ → ℝ) :
    IsCriticalBenchmark b c p σ βe ↔
      ∀ n, SatisfiesCriticalRootEquation b c p σ n (βe n) :=
  Iff.rfl

/-- The nonsaturated benchmark sequence from equation `(7.80)`. -/
@[expose] def nonsaturatedParameterBenchmark (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ parameterConstantC1 b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))

/-- The saturated benchmark sequence from equation `(7.80)`. -/
@[expose] def saturatedParameterBenchmark (c p σ kStarKNormSq : ℝ) : ℕ → ℝ :=
  fun n ↦
    parameterConstantC2 c p kStarKNormSq * (((σ ^ 2) / (n : ℝ)) ^ (p / (3 * p + 1)))

/-- The nonsaturated benchmark sequence from equation `(7.81)`. -/
@[expose] def nonsaturatedErrorBenchmark (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦
    errorConstantC3 b c p q * (((σ ^ 2) / (n : ℝ)) ^ ((q - 1) / (p + q)))

/-- The critical benchmark sequence from equation `(7.81)`. -/
@[expose] def criticalErrorBenchmark (c p : ℝ) (βe : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ errorConstantC4 c p * (βe n ^ (-p - 1))

/-- The saturated benchmark sequence from equation `(7.81)`. -/
@[expose] def saturatedErrorBenchmark (p σ : ℝ) : ℕ → ℝ :=
  fun n ↦ errorConstantC5 * (((σ ^ 2) / (n : ℝ)) ^ (2 * p / (3 * p + 1)))

@[simp] theorem nonsaturatedParameterBenchmark_apply
    (b c p q σ : ℝ) (n : ℕ) :
    nonsaturatedParameterBenchmark b c p q σ n =
      parameterConstantC1 b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) :=
  rfl

@[simp] theorem saturatedParameterBenchmark_apply
    (c p σ kStarKNormSq : ℝ) (n : ℕ) :
    saturatedParameterBenchmark c p σ kStarKNormSq n =
      parameterConstantC2 c p kStarKNormSq * (((σ ^ 2) / (n : ℝ)) ^ (p / (3 * p + 1))) :=
  rfl

@[simp] theorem nonsaturatedErrorBenchmark_apply
    (b c p q σ : ℝ) (n : ℕ) :
    nonsaturatedErrorBenchmark b c p q σ n =
      errorConstantC3 b c p q * (((σ ^ 2) / (n : ℝ)) ^ ((q - 1) / (p + q))) :=
  rfl

@[simp] theorem criticalErrorBenchmark_apply
    (c p : ℝ) (βe : ℕ → ℝ) (n : ℕ) :
    criticalErrorBenchmark c p βe n =
      errorConstantC4 c p * (βe n ^ (-p - 1)) :=
  rfl

@[simp] theorem saturatedErrorBenchmark_apply
    (p σ : ℝ) (n : ℕ) :
    saturatedErrorBenchmark p σ n =
      errorConstantC5 * (((σ ^ 2) / (n : ℝ)) ^ (2 * p / (3 * p + 1))) :=
  rfl

end Benchmarks

end TikhonovEstimation
