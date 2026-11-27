/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRisk
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.Boundary
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRiskBoundary
public import Mathlib.Order.Filter.Extr

public section

open scoped TsvdEstimation.Notation

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
variable (mP mE : ℕ → ℕ)
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

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

/-- Companion to Theorem 7.18. Under the concrete Chapter 7 positivity,
semistochastic white-noise, and algebraic decay hypotheses for the TSVD
expected predictive risk, a predictive-optimal truncation-index family `mP`
eventually avoids the boundary values `0` and `n` of `𝒵(n)`.

The argument is the one used for Theorem 7.16: the predictive-risk backward
step at index `1` is eventually `(σ² / n - b * c) / n < 0`, which excludes the
boundary index `0`, and past the diagonal the steps are eventually positive,
which excludes every index at or beyond `n`. -/
theorem predictiveOptimalFamily_eventuallyAvoidsBoundary
    (h_predOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedPredictiveRiskObjective μ K Rtsvd fTrue η)
        𝒵
        mP) :
    ∀ᶠ n in Filter.atTop, 0 < mP n ∧ mP n < n :=
  predictiveRisk_minimizer_interior_eventually
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (mP := mP)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hmin := fun n ↦ h_predOptimal n)

/-- Theorem 7.18 (1). Any TSVD predictive-optimal truncation-index family on
the Chapter 7 admissible sets `𝒵(n)` eventually takes one of the two values
adjacent to the explicit benchmark `optimalIndex b c p q σ` from `(7.63)`.

As for Theorem 7.16, the disjunctive form is forced by the tie case: the
predictive risk and the expected squared estimation error have backward steps
`σ² / n² - (b c / n) m ^ (-(p + q))` and `-b m ^ (-q) + (σ² / (n c)) m ^ p`,
which differ by the strictly positive factor `(c / n) m ^ (-p)`, so they share
the same sign pattern and hence the same one-step minimizer window
`(7.61)`; both window endpoints can be minimizers when `(7.63)` is an integer. -/
theorem predictiveOptimalFamily_eq_optimalIndex_eventually
    (h_predOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedPredictiveRiskObjective μ K Rtsvd fTrue η)
        𝒵
        mP) :
    ∀ᶠ n in Filter.atTop,
      mP n = optimalIndex b c p q σ n ∨ mP n + 1 = optimalIndex b c p q σ n := by
  filter_upwards [predictiveOptimalFamily_eventuallyAvoidsBoundary
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (mP := mP)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) h_predOptimal] with n hn
  have hwindow := predictiveRisk_interiorMinimizer_window
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (n := n) (mStar := mP n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hn := lt_trans hn.1 hn.2) (hmin := h_predOptimal n)
    (hm_pos := hn.1) (hm_lt := hn.2)
  omega

/-- Theorem 7.18 (Minimizer of Predictive Risk for TSVD). For TSVD
regularization, a predictive-optimal truncation family `mP` and an
estimation-optimal family `mE` eventually differ by at most one truncation
index, so the two optimality criteria select the same minimizer up to the
`(7.63)` tie window.

The three-way disjunction records the tie case of `(7.63)`: the two objectives
have backward steps differing by the positive factor `(c / n) m ^ (-p)`, so the
minimizer window `(7.61)` has the two admissible endpoints
`optimalIndex - 1 ≤ m ≤ optimalIndex`, and `mP n` and `mE n` may occupy
different endpoints. -/
theorem predictiveOptimalFamily_eq_estimationOptimalFamily_eventually
    (h_predOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedPredictiveRiskObjective μ K Rtsvd fTrue η)
        𝒵
        mP)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    ∀ᶠ n in Filter.atTop,
      mP n = mE n ∨ mP n + 1 = mE n ∨ mE n + 1 = mP n := by
  filter_upwards [predictiveRisk_minimizer_interior_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (mP := mP)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (hmin := fun n ↦ h_predOptimal n),
    expectedSqErrorObjective_minimizer_interior_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (mE := mE)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (hmin := fun n ↦ h_estOptimal n)] with n hP hE
  -- Both families sit in the same one-step benchmark window.
  have hPw := predictiveRisk_interiorMinimizer_window
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (n := n) (mStar := mP n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hn := lt_trans hP.1 hP.2) (hmin := h_predOptimal n)
    (hm_pos := hP.1) (hm_lt := hP.2)
  have hEw := interiorMinimizer_eq_optimalIndex
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (n := n) (mStar := mE n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_min := h_estOptimal n) (hm_pos := hE.1) (hm_lt := hE.2)
  omega

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

end

end TsvdEstimation
