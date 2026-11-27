/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.Boundary
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.AsymptoticError
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

public section

open scoped Asymptotics TsvdEstimation.Notation

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
variable (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
variable
  (h_noise_modeVariance :
    ∀ n i,
      ∫ ω,
        (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
          σ ^ 2 / (n : ℝ))
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
variable {mE : ℕ → ℕ}
variable (h_estOptimal :
  ParameterChoice.IsOptimalParameterFamily
    (expectedSqErrorObjective μ K Rtsvd fTrue η)
    𝒵
    mE)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_estOptimal

/-- Companion to Theorem 7.16 (1). Under the concrete Chapter 7 positivity,
semistochastic white-noise, and algebraic decay hypotheses for the TSVD
expected squared estimation-error objective, the estimation-optimal
truncation-index family `mE` eventually avoids the boundary values `0` and `n`
of the admissible set `𝒵(n)`.

The boundary argument only uses the positivity and decay hypotheses: the
backward step at `1` is eventually `-b + σ² / (n c) < 0`, which excludes the
boundary index `0`, while the steps beyond `n` are positive (they grow like
`n ^ (p - 1)`), which excludes every index at or beyond the upper boundary
`n`. Assumption `(7.56)` is kept in the statement for fidelity to the source
formulation. -/
theorem optimalFamily_eventuallyAvoidsBoundary
    (_h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    ∀ᶠ n in Filter.atTop, 0 < mE n ∧ mE n < n :=
  expectedSqErrorObjective_minimizer_interior_eventually
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (mE := mE)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hmin := fun n ↦ h_estOptimal n)

/-- Theorem 7.16 (1). Under the concrete Chapter 7 positivity, semistochastic
white-noise, and algebraic decay hypotheses for the TSVD expected squared
estimation-error objective on `𝒵(n)`, any estimation-optimal truncation-index
family `mE` eventually takes one of the two admissible values adjacent to the
explicit benchmark floor formula `optimalIndex b c p q σ` from `(7.63)`.

The disjunctive form is forced by the tie case: Proposition 7.15 only locates
an interior minimizer within the one-step window
`optimalIndex - 1 ≤ mE n ≤ optimalIndex`, and both endpoints can be minimizers
simultaneously (this happens exactly when `(7.63)` is an integer). Assumption
`(7.56)` is kept in the statement for fidelity to the source formulation. -/
theorem optimalFamily_eq_optimalIndex_eventually
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    ∀ᶠ n in Filter.atTop,
      mE n = optimalIndex b c p q σ n ∨ mE n + 1 = optimalIndex b c p q σ n := by
  filter_upwards [optimalFamily_eventuallyAvoidsBoundary
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (mE := mE)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_estOptimal := h_estOptimal)
      h_vanishingNullspaceComponent] with n hn
  -- Proposition 7.15 confines the interior minimizer to the one-step window.
  have hwindow := interiorMinimizer_eq_optimalIndex
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (n := n) (mStar := mE n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_min := h_estOptimal n) (hm_pos := hn.1) (hm_lt := hn.2)
  omega

/-- Theorem 7.16 (2). Under the same concrete Chapter 7 positivity,
semistochastic white-noise, algebraic decay, and vanishing-nullspace
hypotheses, any estimation-optimal family `mE` has expected squared TSVD
estimation error asymptotically equivalent to the nullspace term plus the
explicit TSVD benchmark profile `optimalErrorBenchmark K fTrue b c p q σ` from
`(7.64)`.

The proof uses the exact orthogonal decomposition into the nullspace floor,
the signal tail, and the retained-mode noise sum. Integral comparison gives
`∑_{j > m} j ^ (-q) ~ m ^ (1 - q) / (q - 1)` and
`∑_{j ≤ m} j ^ p ~ m ^ (p + 1) / (p + 1)`. Both indices in the optimality
window give the same leading term, including the tie case in `(7.63)`. -/
theorem expectedSqErrorAtOptimalFamily_isEquivalent
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    Asymptotics.IsEquivalent Filter.atTop
      (expectedSqErrorAlong μ K Rtsvd fTrue η mE)
      (optimalErrorBenchmark K fTrue b c p q σ) := by
  apply expectedSqErrorAlong_isEquivalent_of_optimalIndexWindow
    μ K S h_length fTrue h_b h_c h_p h_q h_σ η Rtsvd h_tsvd h_noise_memLp
    h_singularDecay h_fourierDecay
  · exact Filter.Eventually.of_forall (fun n i _ ↦ h_noise_modeVariance n i)
  · exact optimalFamily_eq_optimalIndex_eventually
      μ K S h_length fTrue b c p q σ η Rtsvd h_b h_c h_p h_q h_σ
      h_noise_memLp h_noise_meanZero h_noise_modeVariance h_singularDecay h_fourierDecay
      h_tsvd h_estOptimal h_vanishingNullspaceComponent

/-- thm_7_16. Theorem 7.16 (Minimizer of Estimation Error for TSVD). Main
labeled source-facing entry.

The source theorem is recorded for the chosen estimation-optimal TSVD
truncation-index family `mE`, asserting the eventual floor formula together
with the matching asymptotic expected squared estimation-error profile. The
preceding companion theorems expose the arbitrary-family boundary-avoidance
claim and the two source clauses separately for later proof stages and
downstream reuse. The floor clause is available in disjunctive form, since
`(7.63)` admits the tie `{optimalIndex - 1, optimalIndex}`; the asymptotic
clause is recorded as the second conjunct. -/
theorem estimationOptimalFamily_spec
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue) :
    (∀ᶠ n in Filter.atTop,
        mE n = optimalIndex b c p q σ n ∨ mE n + 1 = optimalIndex b c p q σ n) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (expectedSqErrorAlong μ K Rtsvd fTrue η mE)
        (optimalErrorBenchmark K fTrue b c p q σ) := by
  refine ⟨optimalFamily_eq_optimalIndex_eventually
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (mE := mE)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_estOptimal := h_estOptimal)
    h_vanishingNullspaceComponent, ?_⟩
  exact expectedSqErrorAtOptimalFamily_isEquivalent
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (mE := mE)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_estOptimal := h_estOptimal)
    h_vanishingNullspaceComponent

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_estOptimal

end

end TsvdEstimation
